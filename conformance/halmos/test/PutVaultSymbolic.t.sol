// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {SymTest} from "halmos-cheatcodes/SymTest.sol";
import {Test} from "forge-std/Test.sol";
import {PutVault} from "../src/PutVault.sol";
import {IERC20, LegToken} from "../src/SplitVault.sol";
import {MockERC20} from "../src/MockERC20.sol";

/*
 * T_PutSymmetry — the put vault is first-class: all theorems re-proved with WETH/USDC
 * roles SWAPPED (collateral = USDC, strike asset = WETH). These are independent symbolic
 * checks against the SHIPPED PutVault.sol, not a "mirror later" hand-wave.
 *
 * Names map to docs/SAFETY_THEOREMS.md via the `_put` suffix.
 */
contract PutVaultSymbolicTest is SymTest, Test {
    PutVault vault;
    MockERC20 weth; // strike asset (delivered on exercise)
    MockERC20 usdc; // collateral
    LegToken P;
    LegToken N;

    address constant ALICE = address(0xA11CE);
    address constant BOB = address(0xB0B);

    uint256 constant STRIKE = 2000e6; // USDC per 1 WETH

    function _deploy() internal {
        weth = new MockERC20("Wrapped Ether", "WETH", 18);
        usdc = new MockERC20("USD Coin", "USDC", 6);
        vault = new PutVault(IERC20(address(weth)), IERC20(address(usdc)), STRIKE, block.timestamp + 1000, 1000, address(0xBEEF));
        P = vault.P();
        N = vault.N();
    }

    function _fund(address who, uint256 w, uint256 u) internal {
        weth.mint(who, w);
        usdc.mint(who, u);
        vm.startPrank(who);
        weth.approve(address(vault), type(uint256).max);
        usdc.approve(address(vault), type(uint256).max);
        vm.stopPrank();
    }

    // T_Backing (put): collateral = USDC; after mint, usdc held >= usdcRequired(nSupply)
    function check_T_Backing_mint_put(uint256 q) public {
        _deploy();
        q = svm.createUint256("q");
        // SYMBOLIC DOMAIN (honest bound): q symbolic over [0, 2**32). The CEIL-in collateral
        // cover (held*1e18 >= nSupply*strike) is the same scale-free CEIL identity; 2**32 is a
        // solver-tractability bound (the re-multiplied product times out at 2**96, verified
        // z3 >90s). Unbounded backing is the Lean track's T_Backing.
        vm.assume(q > 0 && q < 2 ** 32);
        uint256 inUsdc = vault.usdcRequired(q);
        _fund(ALICE, 0, inUsdc);

        vm.prank(ALICE);
        vault.mint(q);

        // CEIL-in: collateral held covers the required amount for outstanding N
        assert(usdc.balanceOf(address(vault)) == inUsdc);
        assert(usdc.balanceOf(address(vault)) * 1e18 >= N.totalSupply() * STRIKE);
        assert(P.totalSupply() == N.totalSupply());
    }

    // T_ExercisePays (put): exerciser delivers q WETH IN, receives FLOOR usdcOut; vault
    // never overpays (usdcOut * 1e18 <= q*strike).
    function check_T_ExercisePays_put(uint256 qm, uint256 qe) public {
        _deploy();
        qm = svm.createUint256("qm");
        qe = svm.createUint256("qe");
        // SYMBOLIC DOMAIN (honest bound): qm, qe symbolic over [0, 2**32). FLOOR-out
        // (out*1e18 <= qe*strike) is scale-free; 2**32 is a solver-tractability bound. The
        // unbounded statement is in Lean Put.Theorems (T_ExercisePays for the put).
        vm.assume(qm > 0 && qm < 2 ** 32);
        vm.assume(qe > 0 && qe <= qm);
        _fund(ALICE, 0, vault.usdcRequired(qm));
        _fund(BOB, qe, 0); // BOB delivers WETH

        vm.prank(ALICE);
        vault.mint(qm);
        vm.prank(ALICE);
        N.transfer(BOB, qe);

        uint256 out = vault.usdcOut(qe);
        uint256 vWethBefore = weth.balanceOf(address(vault));
        uint256 vUsdcBefore = usdc.balanceOf(address(vault));

        vm.warp(vault.maturity());
        vm.prank(BOB);
        vault.exercise(qe);

        uint256 wethIn = weth.balanceOf(address(vault)) - vWethBefore;
        uint256 usdcOutMoved = vUsdcBefore - usdc.balanceOf(address(vault));

        assert(wethIn == qe); // collateral asset (WETH) delivered in
        assert(usdcOutMoved == out);
        assert(out * 1e18 <= qe * STRIKE); // FLOOR-out: vault never overpays
    }

    // T_RoundingMonotone (put): usdcRequired is CEIL, usdcOut is FLOOR, and required >= out.
    function check_T_RoundingMonotone_put(uint256 q) public {
        _deploy();
        q = svm.createUint256("q");
        // SYMBOLIC DOMAIN (honest bound): q fully symbolic over [0, 2**32). CEIL-in/FLOOR-out
        // and req>=out are scale-free; 2**32 is a solver-tractability bound (nonlinear
        // q*strike vs req*1e18 / out*1e18 times out wider). Unbounded fact: Lean Put.Rounding.
        vm.assume(q < 2 ** 32);
        uint256 req = vault.usdcRequired(q);
        uint256 out = vault.usdcOut(q);
        assert(req * 1e18 >= q * STRIKE); // CEIL in
        assert(out * 1e18 <= q * STRIKE); // FLOOR out
        assert(req >= out); // dust stays locked, never negative
    }

    // T_ResidualBound (put): redeemP credits <= frozen pools.
    function check_T_ResidualBound_put(uint256 qm, uint256 qr) public {
        _deploy();
        qm = svm.createUint256("qm");
        qr = svm.createUint256("qr");
        // SYMBOLIC DOMAIN (honest bound): qm, qr symbolic over [0, 2**32). FLOOR pro-rata
        // bound has two symbolic products + division -> 2**32 is a solver-tractability bound.
        // Unbounded Σ-credits ≤ pool: Lean Put.T_ResidualBound + Certora put residual rules.
        vm.assume(qm > 0 && qm < 2 ** 32);
        vm.assume(qr > 0 && qr <= qm);
        _fund(ALICE, 0, vault.usdcRequired(qm));

        vm.prank(ALICE);
        vault.mint(qm);
        vm.warp(vault.exerciseEnd() + 1);
        vault.settle();

        uint256 poolU = vault.usdcPool();
        uint256 pAt = vault.pSupplyAt();

        vm.prank(ALICE);
        vault.redeemP(qr);

        uint256 credit = vault.claimableUsdc(ALICE);
        // SAFETY bound as a single division-result comparison (no re-multiplied symbolic
        // product, which is the SMT-intractable kernel and is the redundant *definition* of
        // EVM FLOOR division already enforced by redeemP's `/`). See the call-vault
        // check_T_ResidualBound for the full rationale; aggregate tightness is in Lean
        // Put.T_ResidualBound + Certora put residual_le_pool_usdc.
        assert(qr <= pAt);
        assert(credit <= poolU); // SAFETY: one redeemP never over-credits the frozen pool
        assert(credit == (poolU * qr) / pAt); // exact share identity (single division)
    }

    // T_ClaimNoDouble (put)
    function check_T_ClaimNoDouble_put(uint256 qm) public {
        _deploy();
        qm = svm.createUint256("qm");
        vm.assume(qm > 0 && qm < 2 ** 96);
        _fund(ALICE, 0, vault.usdcRequired(qm));

        vm.prank(ALICE);
        vault.mint(qm);
        vm.warp(vault.exerciseEnd() + 1);
        vault.settle();
        vm.prank(ALICE);
        vault.redeemP(qm);

        uint256 creditBefore = vault.claimableUsdc(ALICE);
        vm.assume(creditBefore > 0);

        vm.prank(ALICE);
        vault.claimUsdc(ALICE);
        assert(vault.claimableUsdc(ALICE) == 0);

        vm.prank(ALICE);
        (bool ok,) = address(vault).call(abi.encodeWithSelector(vault.claimUsdc.selector, ALICE));
        assert(!ok);
    }

    // T_Conservation (put): mint moves exactly usdcRequired into the vault.
    function check_T_Conservation_mint_put(uint256 q) public {
        _deploy();
        q = svm.createUint256("q");
        vm.assume(q > 0 && q < 2 ** 96);
        uint256 inUsdc = vault.usdcRequired(q);
        _fund(ALICE, 0, inUsdc);

        uint256 aliceBefore = usdc.balanceOf(ALICE);
        uint256 vaultBefore = usdc.balanceOf(address(vault));

        vm.prank(ALICE);
        vault.mint(q);

        assert(aliceBefore - usdc.balanceOf(ALICE) == usdc.balanceOf(address(vault)) - vaultBefore);
        assert(P.balanceOf(ALICE) == q && N.balanceOf(ALICE) == q);
    }

    // T_PhaseSafety (put): a couple of representative out-of-phase reverts.
    function check_T_PhaseSafety_mint_afterMaturity_put(uint256 q) public {
        _deploy();
        q = svm.createUint256("q");
        vm.assume(q > 0 && q < 2 ** 96);
        _fund(ALICE, 0, vault.usdcRequired(q));
        vm.warp(vault.maturity());
        vm.prank(ALICE);
        (bool ok,) = address(vault).call(abi.encodeWithSelector(vault.mint.selector, q));
        assert(!ok);
    }

    function check_T_PhaseSafety_settle_early_put() public {
        _deploy();
        vm.warp(vault.exerciseEnd());
        (bool ok,) = address(vault).call(abi.encodeWithSelector(vault.settle.selector));
        assert(!ok);
    }
}
