// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {MiniTest} from "./lib/MiniTest.sol";
import {MockERC20} from "./mocks/MockERC20.sol";
import {SplitVault, LegToken, IERC20} from "../src/SplitVault.sol";

/*
 * SplitVaultConformance — stateful conformance of the SHIPPED CALL vault
 * =====================================================================
 * Verifies the production src/SplitVault.sol satisfies the frozen settlement
 * theorems (docs/SETTLEMENT_SPEC.md, docs/SAFETY_THEOREMS.md). The handler
 * fuzzes the REAL transition surface (mint, redeemPair, exercise, settle,
 * redeemP, claimWeth, claimUsdc) across all phases with random actors/amounts
 * and monotone time warps; the SplitVaultConformanceTest contract asserts one
 * invariant_<TheoremName> per theorem in conformance/THEOREM_MAP.md.
 *
 * Roles (call vault, per SETTLEMENT_SPEC §1):
 *   collateral = WETH (18dp), strike asset = USDC (6dp).
 *
 * fail_on_revert=false: the handler deliberately probes out-of-phase actions to
 * prove PhaseSafety. A revert is a valid no-op step, never a property failure.
 */
contract CallHandler is MiniTest {
    SplitVault public vault;
    MockERC20 public weth;
    MockERC20 public usdc;
    LegToken public P;
    LegToken public N;

    address[] public actors;

    // ---- ghost accounting (T_Conservation / T_ExercisePays / T_ClaimNoDouble) ----
    uint256 public wethIn; // WETH pulled into vault (mint)
    uint256 public wethOut; // WETH sent out (redeemPair + exercise + claimWeth)
    uint256 public usdcIn; // USDC pulled into vault (exercise)
    uint256 public usdcOut; // USDC sent out (claimUsdc)

    // exercise-specific ghosts (T_ExercisePays): collateral out only against ceil strike in
    uint256 public exerciseWethOut;
    uint256 public exerciseUsdcIn;

    // redeemP credit ghosts (T_ResidualBound): total credited vs frozen pool
    uint256 public creditedWeth;
    uint256 public creditedUsdc;

    // claim ghosts (T_ClaimNoDouble): total claimed can never exceed total credited
    uint256 public claimedWeth;
    uint256 public claimedUsdc;

    // residual-liveness witness: was settle() ever reached with pSupplyAt == 0?
    bool public settledWithZeroP;

    // phase-safety witness: an out-of-phase call that did NOT revert (must stay false)
    bool public phaseViolation;

    constructor(SplitVault _vault, MockERC20 _weth, MockERC20 _usdc) {
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

    // ----------------------------------------------------------------- time
    function advanceTime(uint256 step) public {
        step = bound(step, 1 hours, 8 days);
        vm.warp(block.timestamp + step);
    }

    // ------------------------------------------------------- mint [MINT_REDEEM]
    function hMint(uint256 seed, uint256 amt) public {
        if (!_inMintRedeem()) return;
        address a = _actor(seed);
        uint256 bal = weth.balanceOf(a);
        amt = bound(amt, 1, bal > 1e24 ? 1e24 : bal);
        if (amt == 0) return;
        vm.prank(a);
        vault.mint(amt);
        wethIn += amt;
    }

    // ------------------------------------------------- redeemPair [MINT_REDEEM]
    function hRedeemPair(uint256 seed, uint256 amt) public {
        if (!_inMintRedeem()) return;
        address a = _actor(seed);
        uint256 cap = P.balanceOf(a) < N.balanceOf(a) ? P.balanceOf(a) : N.balanceOf(a);
        if (cap == 0) return;
        amt = bound(amt, 1, cap);
        vm.prank(a);
        vault.redeemPair(amt);
        wethOut += amt;
    }

    // ----------------------------------------------------- exercise [EXERCISE]
    function hExercise(uint256 seed, uint256 amt) public {
        if (!_inExercise()) return;
        address a = _actor(seed);
        uint256 nbal = N.balanceOf(a);
        if (nbal == 0) return;
        // cap by what their USDC can pay (ceil strike)
        uint256 strike = vault.strike();
        uint256 maxByUsdc = (usdc.balanceOf(a) * 1e18) / strike;
        uint256 cap = nbal < maxByUsdc ? nbal : maxByUsdc;
        if (cap == 0) return;
        amt = bound(amt, 1, cap);
        uint256 owed = vault.usdcOwed(amt);
        if (owed > usdc.balanceOf(a)) return; // ceil edge guard
        vm.prank(a);
        vault.exercise(amt);
        usdcIn += owed;
        wethOut += amt;
        exerciseUsdcIn += owed;
        exerciseWethOut += amt;
    }

    // -------------------------------------------------------- settle [post-window]
    function hSettle() public {
        if (block.timestamp <= vault.exerciseEnd() || vault.settled()) return;
        if (P.totalSupply() == 0) settledWithZeroP = true;
        vault.settle();
    }

    // ------------------------------------------------------------------- liveness
    // Directed action so the residual-liveness branch (pSupplyAt==0 at settle) is
    // GENUINELY REACHABLE, not vacuously skipped. Pre-maturity, redeem every actor's
    // full P+N pair (burning all P and all N together), then warp past the window
    // and settle. This drives the contract into the exact pSupplyAt==0 settled
    // state that invariant_T_ResidualLiveness is meant to certify. The honest
    // outcome on the real transition surface: pools are empty (symmetric path), so
    // liveness holds with no stranding. (Stray-collateral stranding — the §6 gap —
    // is shown directly in ResidualLivenessWitness.t.sol; it is NOT reachable here
    // because the fuzzer cannot transfer tokens to the vault outside a transition.)
    function hDrainAllThenSettle() public {
        if (!_inMintRedeem()) return;
        for (uint256 i = 0; i < actors.length; i++) {
            address a = actors[i];
            uint256 cap = P.balanceOf(a) < N.balanceOf(a) ? P.balanceOf(a) : N.balanceOf(a);
            if (cap == 0) continue;
            vm.prank(a);
            vault.redeemPair(cap);
            wethOut += cap;
        }
        // jump past the exercise window and settle with (hopefully) zero P
        vm.warp(vault.exerciseEnd() + 1);
        if (!vault.settled()) {
            if (P.totalSupply() == 0) settledWithZeroP = true;
            vault.settle();
        }
    }

    // ------------------------------------------------------- redeemP [SETTLED]
    function hRedeemP(uint256 seed, uint256 amt) public {
        if (!vault.settled()) return;
        address a = _actor(seed);
        uint256 cap = P.balanceOf(a);
        if (cap == 0) return;
        amt = bound(amt, 1, cap);
        // shipped redeemP divides by pSupplyAt; pSupplyAt==0 path reverts (div by zero),
        // which is itself a residual-liveness defect surfaced by invariant_T_ResidualLiveness.
        if (vault.pSupplyAt() == 0) return;
        uint256 wCredit = (vault.wethPool() * amt) / vault.pSupplyAt();
        uint256 uCredit = (vault.usdcPool() * amt) / vault.pSupplyAt();
        vm.prank(a);
        vault.redeemP(amt);
        creditedWeth += wCredit;
        creditedUsdc += uCredit;
    }

    // --------------------------------------------------------- claims [SETTLED]
    function hClaimWeth(uint256 seed) public {
        address a = _actor(seed);
        uint256 amt = vault.claimableWeth(a);
        if (amt == 0) return;
        vm.prank(a);
        vault.claimWeth(a);
        wethOut += amt;
        claimedWeth += amt;
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

    // ---------------------------------------------------------------------------
    // PHASE-SAFETY PROBES (T_PhaseSafety): call each transition OUT of its phase
    // and require it to revert. If any out-of-phase call returns success, set the
    // phaseViolation witness, which invariant_T_PhaseSafety then fails on.
    // ---------------------------------------------------------------------------
    function probeMintOutOfPhase(uint256 seed) public {
        if (_inMintRedeem()) return; // only probe when out of MINT_REDEEM
        address a = _actor(seed);
        if (weth.balanceOf(a) == 0) return;
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
        if (vault.settled()) return; // only probe pre-settle
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

contract SplitVaultConformanceTest is MiniTest {
    MockERC20 weth;
    MockERC20 usdc;
    SplitVault vault;
    CallHandler handler;

    uint256 constant STRIKE = 3_000e6; // USDC per 1 WETH
    uint256 constant WINDOW = 2 days;

    function setUp() public {
        weth = new MockERC20("Wrapped Ether", "WETH", 18);
        usdc = new MockERC20("USD Coin", "USDC", 6);
        vault = new SplitVault(
            IERC20(address(weth)), IERC20(address(usdc)), STRIKE, block.timestamp + 30 days, WINDOW
        );
        handler = new CallHandler(vault, weth, usdc);
    }

    function targetContracts() public view returns (address[] memory addrs) {
        addrs = new address[](1);
        addrs[0] = address(handler);
    }

    // =====================================================================
    // T_Backing — claims never exceed holdings.
    //   pre-settle:  weth.balanceOf(vault) == N.totalSupply()  (each N backed 1:1)
    //                P.totalSupply()        >= weth.balanceOf(vault)
    //   post-settle: Σ outstanding claimableWeth + un-redeemed-P floor-share <= collat held
    //                (aggregate form proven via creditedWeth - claimedWeth <= held below;
    //                 the strict pre-settle coupling is the live-claim bound).
    // =====================================================================
    function invariant_T_Backing() public view {
        uint256 vw = weth.balanceOf(address(vault));
        if (!vault.settled()) {
            assertEq(vw, vault.N().totalSupply(), "T_Backing: weth==N pre-settle");
            assertGe(vault.P().totalSupply(), vw, "T_Backing: P>=weth pre-settle");
        } else {
            // post-settle: WETH still held >= outstanding (credited-but-unclaimed) WETH credits
            uint256 outstandingW = handler.creditedWeth() - handler.claimedWeth();
            assertGe(vw, outstandingW, "T_Backing: weth held >= outstanding weth credits");
            uint256 vu = usdc.balanceOf(address(vault));
            uint256 outstandingU = handler.creditedUsdc() - handler.claimedUsdc();
            assertGe(vu, outstandingU, "T_Backing: usdc held >= outstanding usdc credits");
        }
    }

    // =====================================================================
    // T_Conservation — no debt minted, no overpay. Per-asset:  in == out + held.
    // =====================================================================
    function invariant_T_Conservation() public view {
        assertEq(
            handler.wethIn(),
            handler.wethOut() + weth.balanceOf(address(vault)),
            "T_Conservation: WETH in == out + held"
        );
        assertEq(
            handler.usdcIn(),
            handler.usdcOut() + usdc.balanceOf(address(vault)),
            "T_Conservation: USDC in == out + held"
        );
    }

    // =====================================================================
    // T_ExercisePays — no free collateral: every WETH unit sent out via exercise
    // was matched by ceil(strike) USDC paid in. usdcOwed is ceil, so
    // exerciseUsdcIn >= floor(exerciseWethOut * strike / 1e18); strictly, the
    // USDC paid per unit is never less than the exact strike value.
    // =====================================================================
    function invariant_T_ExercisePays() public view {
        // exact lower bound: ceil-summed payments are >= the exact (real-valued)
        // strike owed for the collateral released. floor(wOut*strike/1e18) is the
        // largest integer not exceeding the exact owed; ceil per-call only ever
        // pays >= that, so this must hold.
        uint256 exactFloor = (handler.exerciseWethOut() * STRIKE) / 1e18;
        assertGe(handler.exerciseUsdcIn(), exactFloor, "T_ExercisePays: ceil strike paid for collateral out");
    }

    // =====================================================================
    // T_ResidualBound — post-settle, total credited <= frozen residual pool.
    //   Σ redeemP weth credits <= wethPool (collatAt)
    //   Σ redeemP usdc credits <= usdcPool (strikeAt)
    // =====================================================================
    function invariant_T_ResidualBound() public view {
        if (!vault.settled()) return;
        assertLe(handler.creditedWeth(), vault.wethPool(), "T_ResidualBound: weth credits <= wethPool");
        assertLe(handler.creditedUsdc(), vault.usdcPool(), "T_ResidualBound: usdc credits <= usdcPool");
    }

    // =====================================================================
    // T_RoundingMonotone — CEIL-in / FLOOR-out: the vault's held-minus-owed gap
    // is never negative; rounding can only STRAND dust, never DRAIN. Concretely
    // post-settle: held WETH >= sum of (floored) credits already taken, with the
    // residual (pool - credited) being non-negative dust kept in the vault.
    // =====================================================================
    function invariant_T_RoundingMonotone() public view {
        if (!vault.settled()) return;
        // FLOOR credits can never exceed the frozen pool => dust = pool - credited >= 0.
        assertGe(vault.wethPool(), handler.creditedWeth(), "T_RoundingMonotone: weth dust >= 0");
        assertGe(vault.usdcPool(), handler.creditedUsdc(), "T_RoundingMonotone: usdc dust >= 0");
        // and the vault still physically holds at least the outstanding (unclaimed) credits
        uint256 outstandingW = handler.creditedWeth() - handler.claimedWeth();
        assertGe(weth.balanceOf(address(vault)), outstandingW, "T_RoundingMonotone: held >= outstanding weth");
    }

    // =====================================================================
    // T_PhaseSafety — out-of-phase transitions revert. The handler probes each
    // transition outside its phase and sets phaseViolation iff one succeeded.
    // =====================================================================
    function invariant_T_PhaseSafety() public view {
        assertTrue(!handler.phaseViolation(), "T_PhaseSafety: out-of-phase call did not revert");
    }

    // =====================================================================
    // T_ClaimNoDouble — credit zeroed before transfer => cumulative claimed can
    // never exceed cumulative credited; no credit pays twice. (Reentrancy-safety
    // is structural CEI in the contract + the nonReentrant guard.)
    // =====================================================================
    function invariant_T_ClaimNoDouble() public view {
        assertLe(handler.claimedWeth(), handler.creditedWeth(), "T_ClaimNoDouble: weth claimed <= credited");
        assertLe(handler.claimedUsdc(), handler.creditedUsdc(), "T_ClaimNoDouble: usdc claimed <= credited");
    }

    // =====================================================================
    // T_ResidualLiveness — after settle, every asset is claimable by a valid
    // claimant or the residual recipient (SETTLEMENT_SPEC §6), or bounded dust.
    //
    // HONEST CONFORMANCE STATEMENT: the SHIPPED SplitVault.sol does NOT implement
    // the §6 terminal rule (no residualRecipient credit when pSupplyAt==0). When
    // settle() is reached with P.totalSupply()==0, wethPool/usdcPool are frozen
    // but redeemP reverts (divide-by-pSupplyAt==0) and nothing routes them out:
    // the residual is permanently stranded. This invariant DETECTS that case.
    //
    // The fuzzer can only reach pSupplyAt==0 if all P is redeemed pre-maturity
    // (redeemPair burns P+N together, so emptying P also empties N, leaving the
    // pools at 0 too -> no MEANINGFUL stranding in that symmetric path). We assert
    // the precise liveness condition: IF settled with zero P, the frozen pools
    // must be empty (else funds are stranded with no claimant).
    // =====================================================================
    function invariant_T_ResidualLiveness() public view {
        if (!vault.settled()) return;
        if (vault.pSupplyAt() == 0) {
            // No P holder and no residualRecipient => any non-zero pool is stranded.
            assertEq(vault.wethPool(), 0, "T_ResidualLiveness: weth stranded (pSupplyAt==0, no recipient)");
            assertEq(vault.usdcPool(), 0, "T_ResidualLiveness: usdc stranded (pSupplyAt==0, no recipient)");
        }
    }
}
