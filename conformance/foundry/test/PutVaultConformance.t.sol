// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {MiniTest} from "./lib/MiniTest.sol";
import {MockERC20} from "./mocks/MockERC20.sol";
import {PutVault} from "../src/PutVault.sol";
import {LegToken, IERC20} from "../src/SplitVault.sol";

/*
 * PutVaultConformance — stateful conformance of the SHIPPED PUT vault (T_PutSymmetry)
 * =================================================================================
 * First-class proof of the same theorems with roles swapped (SETTLEMENT_SPEC §7):
 *   collateral = USDC (6dp), strike asset = WETH (18dp).
 *   mint:        pull usdcRequired = ceil(q*strike/1e18) USDC in (CEIL-in)
 *   redeemPair:  send usdcOut     = floor(q*strike/1e18) USDC out (FLOOR-out; ceil dust stays)
 *   exercise:    pull q WETH in, send usdcOut(q) USDC out
 *   redeemP:     FLOOR pro-rata of (usdcPool, wethPool)
 * Asserts the same invariant_<TheoremName> set against the production PutVault.
 */
contract PutHandler is MiniTest {
    PutVault public vault;
    MockERC20 public weth;
    MockERC20 public usdc;
    LegToken public P;
    LegToken public N;

    address[] public actors;

    // ghost accounting, per asset:  in == out + held
    uint256 public usdcIn; // mint
    uint256 public usdcOut; // redeemPair + exercise(out) + claimUsdc
    uint256 public wethIn; // exercise(in)
    uint256 public wethOut; // claimWeth

    // exercise ghosts (T_ExercisePays mirror: collateral USDC out only against WETH in)
    uint256 public exerciseWethIn;
    uint256 public exerciseUsdcOut;

    // redeemP credit ghosts (T_ResidualBound)
    uint256 public creditedUsdc;
    uint256 public creditedWeth;

    // claim ghosts (T_ClaimNoDouble)
    uint256 public claimedUsdc;
    uint256 public claimedWeth;

    bool public settledWithZeroP;
    bool public phaseViolation;

    constructor(PutVault _vault, MockERC20 _weth, MockERC20 _usdc) {
        vault = _vault;
        weth = _weth;
        usdc = _usdc;
        P = _vault.P();
        N = _vault.N();
        for (uint160 i = 1; i <= 3; i++) {
            address a = address(i);
            actors.push(a);
            weth.mint(a, 1_000_000e18);
            usdc.mint(a, 1_000_000_000e6);
            vm.startPrank(a);
            weth.approve(address(vault), type(uint256).max);
            usdc.approve(address(vault), type(uint256).max);
            vm.stopPrank();
        }
    }

    function _actor(uint256 seed) internal view returns (address) {
        return actors[seed % actors.length];
    }

    function _inMintRedeem() internal view returns (bool) {
        return block.timestamp < vault.maturity();
    }

    function _inExercise() internal view returns (bool) {
        return block.timestamp >= vault.maturity() && block.timestamp <= vault.exerciseEnd();
    }

    function advanceTime(uint256 step) public {
        step = bound(step, 1 hours, 8 days);
        vm.warp(block.timestamp + step);
    }

    function hMint(uint256 seed, uint256 amt) public {
        if (!_inMintRedeem()) return;
        address a = _actor(seed);
        // cap by USDC the actor can lock (ceil required)
        uint256 maxByUsdc = (usdc.balanceOf(a) * 1e18) / vault.strike();
        if (maxByUsdc == 0) return;
        amt = bound(amt, 1, maxByUsdc > 1e24 ? 1e24 : maxByUsdc);
        uint256 req = vault.usdcRequired(amt);
        if (req > usdc.balanceOf(a)) return; // ceil edge guard
        vm.prank(a);
        vault.mint(amt);
        usdcIn += req;
    }

    function hRedeemPair(uint256 seed, uint256 amt) public {
        if (!_inMintRedeem()) return;
        address a = _actor(seed);
        uint256 cap = P.balanceOf(a) < N.balanceOf(a) ? P.balanceOf(a) : N.balanceOf(a);
        if (cap == 0) return;
        amt = bound(amt, 1, cap);
        uint256 out = vault.usdcOut(amt);
        vm.prank(a);
        vault.redeemPair(amt);
        usdcOut += out;
    }

    function hExercise(uint256 seed, uint256 amt) public {
        if (!_inExercise()) return;
        address a = _actor(seed);
        uint256 nbal = N.balanceOf(a);
        if (nbal == 0) return;
        uint256 cap = nbal < weth.balanceOf(a) ? nbal : weth.balanceOf(a);
        if (cap == 0) return;
        amt = bound(amt, 1, cap);
        uint256 out = vault.usdcOut(amt);
        if (out > usdc.balanceOf(address(vault))) return; // vault must hold enough USDC
        vm.prank(a);
        vault.exercise(amt);
        wethIn += amt;
        usdcOut += out;
        exerciseWethIn += amt;
        exerciseUsdcOut += out;
    }

    function hSettle() public {
        if (block.timestamp <= vault.exerciseEnd() || vault.settled()) return;
        if (P.totalSupply() == 0) settledWithZeroP = true;
        vault.settle();
    }

    // Directed liveness driver (see SplitVaultConformance.t.sol for rationale):
    // redeem all PutP+PutN pairs pre-maturity, warp past the window, settle with
    // pSupplyAt==0 so the residual-liveness branch is genuinely exercised.
    function hDrainAllThenSettle() public {
        if (!_inMintRedeem()) return;
        for (uint256 i = 0; i < actors.length; i++) {
            address a = actors[i];
            uint256 cap = P.balanceOf(a) < N.balanceOf(a) ? P.balanceOf(a) : N.balanceOf(a);
            if (cap == 0) continue;
            uint256 out = vault.usdcOut(cap);
            vm.prank(a);
            vault.redeemPair(cap);
            usdcOut += out;
        }
        vm.warp(vault.exerciseEnd() + 1);
        if (!vault.settled()) {
            if (P.totalSupply() == 0) settledWithZeroP = true;
            vault.settle();
        }
    }

    function hRedeemP(uint256 seed, uint256 amt) public {
        if (!vault.settled()) return;
        address a = _actor(seed);
        uint256 cap = P.balanceOf(a);
        if (cap == 0) return;
        if (vault.pSupplyAt() == 0) return; // shipped redeemP reverts (div by zero)
        amt = bound(amt, 1, cap);
        uint256 uCredit = (vault.usdcPool() * amt) / vault.pSupplyAt();
        uint256 wCredit = (vault.wethPool() * amt) / vault.pSupplyAt();
        vm.prank(a);
        vault.redeemP(amt);
        creditedUsdc += uCredit;
        creditedWeth += wCredit;
    }

    function hClaimUsdc(uint256 seed) public {
        address a = _actor(seed);
        uint256 amt = vault.claimableUsdc(a);
        if (amt == 0) return;
        vm.prank(a);
        vault.claimUsdc(a);
        usdcOut += amt;
        claimedUsdc += amt;
    }

    function hClaimWeth(uint256 seed) public {
        address a = _actor(seed);
        uint256 amt = vault.claimableWeth(a);
        if (amt == 0) return;
        vm.prank(a);
        vault.claimWeth(a);
        wethOut += amt;
        claimedWeth += amt;
    }

    // ---- phase-safety probes ----
    function probeMintOutOfPhase(uint256 seed) public {
        if (_inMintRedeem()) return;
        address a = _actor(seed);
        if (usdc.balanceOf(a) == 0) return;
        vm.prank(a);
        try vault.mint(1) {
            phaseViolation = true;
        } catch {}
    }

    function probeExerciseOutOfPhase(uint256 seed) public {
        if (_inExercise()) return;
        address a = _actor(seed);
        if (N.balanceOf(a) == 0) return;
        vm.prank(a);
        try vault.exercise(1) {
            phaseViolation = true;
        } catch {}
    }

    function probeRedeemPOutOfPhase(uint256 seed) public {
        if (vault.settled()) return;
        address a = _actor(seed);
        if (P.balanceOf(a) == 0) return;
        vm.prank(a);
        try vault.redeemP(1) {
            phaseViolation = true;
        } catch {}
    }

    function probeSettleEarly() public {
        if (block.timestamp > vault.exerciseEnd() || vault.settled()) return;
        try vault.settle() {
            phaseViolation = true;
        } catch {}
    }
}

contract PutVaultConformanceTest is MiniTest {
    MockERC20 weth;
    MockERC20 usdc;
    PutVault vault;
    PutHandler handler;

    uint256 constant STRIKE = 3_000e6; // USDC per 1 WETH
    uint256 constant WINDOW = 2 days;

    function setUp() public {
        weth = new MockERC20("Wrapped Ether", "WETH", 18);
        usdc = new MockERC20("USD Coin", "USDC", 6);
        vault = new PutVault(
            IERC20(address(weth)),
            IERC20(address(usdc)),
            STRIKE,
            block.timestamp + 30 days,
            WINDOW,
            address(0xBEEF) // SETTLEMENT_SPEC §6 residualRecipient (shipped PutVault now implements the terminal rule)
        );
        handler = new PutHandler(vault, weth, usdc);
    }

    function targetContracts() public view returns (address[] memory addrs) {
        addrs = new address[](1);
        addrs[0] = address(handler);
    }

    // T_Backing (put): pre-settle each PutN is backed by usdcOut(N) USDC claimable
    // via redeemPair, and the collateral held covers outstanding obligations. The
    // exact coupling: usdc held >= floor(N*strike/1e18) (what redeemPair could pay
    // out for all N), and post-settle held >= outstanding credits.
    function invariant_T_Backing() public view {
        uint256 vu = usdc.balanceOf(address(vault));
        if (!vault.settled()) {
            // every outstanding PutN can be paired+redeemed for usdcOut; vault must hold it.
            uint256 owedToPairs = (vault.N().totalSupply() * STRIKE) / 1e18; // floor = usdcOut
            assertGe(vu, owedToPairs, "T_Backing(put): usdc held >= redeemable to N");
        } else {
            uint256 outstandingU = handler.creditedUsdc() - handler.claimedUsdc();
            assertGe(vu, outstandingU, "T_Backing(put): usdc held >= outstanding usdc credits");
            uint256 vw = weth.balanceOf(address(vault));
            uint256 outstandingW = handler.creditedWeth() - handler.claimedWeth();
            assertGe(vw, outstandingW, "T_Backing(put): weth held >= outstanding weth credits");
        }
    }

    // T_Conservation (put): in == out + held, per asset.
    function invariant_T_Conservation() public view {
        assertEq(
            handler.usdcIn(),
            handler.usdcOut() + usdc.balanceOf(address(vault)),
            "T_Conservation(put): USDC in == out + held"
        );
        assertEq(
            handler.wethIn(),
            handler.wethOut() + weth.balanceOf(address(vault)),
            "T_Conservation(put): WETH in == out + held"
        );
    }

    // T_ExercisePays (put): USDC collateral leaves only against WETH delivered in.
    // usdcOut is FLOOR, so the USDC paid out never exceeds the exact strike value
    // of the WETH delivered: exerciseUsdcOut <= ceil(exerciseWethIn*strike/1e18).
    function invariant_T_ExercisePays() public view {
        uint256 wIn = handler.exerciseWethIn();
        uint256 exactCeil = (wIn * STRIKE + 1e18 - 1) / 1e18;
        assertLe(handler.exerciseUsdcOut(), exactCeil, "T_ExercisePays(put): usdc out <= strike value of weth in");
    }

    // T_ResidualBound (put): total credited <= frozen pool.
    function invariant_T_ResidualBound() public view {
        if (!vault.settled()) return;
        assertLe(handler.creditedUsdc(), vault.usdcPool(), "T_ResidualBound(put): usdc credits <= usdcPool");
        assertLe(handler.creditedWeth(), vault.wethPool(), "T_ResidualBound(put): weth credits <= wethPool");
    }

    // T_RoundingMonotone (put): FLOOR credits => dust = pool - credited >= 0.
    function invariant_T_RoundingMonotone() public view {
        if (!vault.settled()) return;
        assertGe(vault.usdcPool(), handler.creditedUsdc(), "T_RoundingMonotone(put): usdc dust >= 0");
        assertGe(vault.wethPool(), handler.creditedWeth(), "T_RoundingMonotone(put): weth dust >= 0");
        uint256 outstandingU = handler.creditedUsdc() - handler.claimedUsdc();
        assertGe(usdc.balanceOf(address(vault)), outstandingU, "T_RoundingMonotone(put): held >= outstanding usdc");
    }

    function invariant_T_PhaseSafety() public view {
        assertTrue(!handler.phaseViolation(), "T_PhaseSafety(put): out-of-phase call did not revert");
    }

    function invariant_T_ClaimNoDouble() public view {
        assertLe(handler.claimedUsdc(), handler.creditedUsdc(), "T_ClaimNoDouble(put): usdc claimed <= credited");
        assertLe(handler.claimedWeth(), handler.creditedWeth(), "T_ClaimNoDouble(put): weth claimed <= credited");
    }

    // T_ResidualLiveness (put), SETTLEMENT_SPEC §6: the shipped PutVault NOW implements
    // the residualRecipient terminal rule. When pSupplyAt==0 at settle, the entire frozen
    // residual must be claimable by the immutable residualRecipient — nothing stranded.
    // (Previously this cell was a RED honest-fail flagging the missing §6 rule; the shipped
    // code has since added it, so the property now holds and the invariant verifies it.)
    function invariant_T_ResidualLiveness() public view {
        if (!vault.settled()) return;
        if (vault.pSupplyAt() == 0) {
            address recipient = vault.residualRecipient();
            assertEq(
                vault.claimableUsdc(recipient),
                vault.usdcPool(),
                "T_ResidualLiveness(put): full usdc residual claimable by recipient"
            );
            assertEq(
                vault.claimableWeth(recipient),
                vault.wethPool(),
                "T_ResidualLiveness(put): full weth residual claimable by recipient"
            );
        }
    }
}
