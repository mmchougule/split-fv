// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {MiniTest} from "./lib/MiniTest.sol";
import {MockERC20} from "./mocks/MockERC20.sol";
import {SplitVault, LegToken, IERC20} from "../src/SplitVault.sol";
import {PutVault} from "../src/PutVault.sol";

/*
 * ResidualLivenessWitness — directed reachability + defect characterization.
 * =========================================================================
 * The stateful invariant_T_ResidualLiveness can pass VACUOUSLY if the fuzzer
 * never reaches a settled state with pSupplyAt==0. These directed tests:
 *   1. PROVE that pSupplyAt==0-at-settle IS reachable on the shipped contracts.
 *   2. CHARACTERIZE the actual behavior: in the symmetric all-redeem path the
 *      pools are empty (no meaningful stranding), so the liveness invariant
 *      holds for everything the fuzzer can construct from honest transitions.
 *   3. DEMONSTRATE the §6 GAP: if any asset is forced into the vault before a
 *      pSupplyAt==0 settle (the asymmetric path the spec's residualRecipient
 *      rule is meant to cover), the shipped code strands it — redeemP reverts
 *      (div by zero) and nothing routes it out. This is the defect the
 *      conformance track surfaces.
 */
contract ResidualLivenessWitness is MiniTest {
    MockERC20 weth;
    MockERC20 usdc;
    SplitVault vault;
    PutVault put;

    uint256 constant STRIKE = 3_000e6;
    uint256 constant WINDOW = 2 days;
    uint256 maturity;

    address constant ALICE = address(0xA11CE);

    function setUp() public {
        weth = new MockERC20("Wrapped Ether", "WETH", 18);
        usdc = new MockERC20("USD Coin", "USDC", 6);
        maturity = block.timestamp + 30 days;
        vault = new SplitVault(IERC20(address(weth)), IERC20(address(usdc)), STRIKE, maturity, WINDOW);
        put = new PutVault(
            IERC20(address(weth)), IERC20(address(usdc)), STRIKE, maturity, WINDOW, address(0xBEEF)
        ); // shipped PutVault now takes the SETTLEMENT_SPEC §6 residualRecipient

        weth.mint(ALICE, 1_000e18);
        usdc.mint(ALICE, 10_000_000e6);
        vm.startPrank(ALICE);
        weth.approve(address(vault), type(uint256).max);
        usdc.approve(address(vault), type(uint256).max);
        weth.approve(address(put), type(uint256).max);
        usdc.approve(address(put), type(uint256).max);
        vm.stopPrank();
    }

    /// 1+2: pSupplyAt==0 at settle IS reachable, and via honest transitions the
    /// frozen pools are empty => T_ResidualLiveness holds (nothing stranded).
    function test_residualLiveness_zeroP_symmetric_pools_empty() public {
        vm.prank(ALICE);
        vault.mint(100e18); // P=N=100, weth held=100
        vm.prank(ALICE);
        vault.redeemPair(100e18); // burns all P AND all N, weth back to ALICE

        // now P.totalSupply()==0 and vault holds 0 weth, 0 usdc
        vm.warp(maturity + WINDOW + 1);
        vault.settle();

        assertEq(vault.pSupplyAt(), 0, "witness: reached pSupplyAt==0 at settle");
        assertEq(vault.wethPool(), 0, "witness: weth pool empty (no stranding)");
        assertEq(vault.usdcPool(), 0, "witness: usdc pool empty (no stranding)");
    }

    /// 3: the §6 GAP, demonstrated explicitly. Force WETH into the vault (a stray
    /// transfer — exactly the kind of residual the §6 rule exists for), redeem all
    /// P+N so pSupplyAt==0, settle. The pool is now NON-ZERO and unreachable:
    /// redeemP reverts (div by pSupplyAt==0) and there is no residualRecipient.
    function test_residualLiveness_GAP_shipped_strands_stray_collateral() public {
        vm.prank(ALICE);
        vault.mint(100e18);
        vm.prank(ALICE);
        vault.redeemPair(100e18); // P==N==0

        // stray WETH lands in the vault (donation / rounding / external transfer)
        weth.mint(address(vault), 5e18);

        vm.warp(maturity + WINDOW + 1);
        vault.settle();

        assertEq(vault.pSupplyAt(), 0, "GAP: pSupplyAt==0");
        // SHIPPED BEHAVIOR: pool is non-zero -> stranded. This documents the defect.
        assertEq(vault.wethPool(), 5e18, "GAP: 5 WETH frozen with no claimant");

        // and redeemP cannot release it (no P to burn; div-by-zero anyway)
        vm.prank(ALICE);
        try vault.redeemP(1) {
            assertTrue(false, "GAP: redeemP unexpectedly succeeded");
        } catch {
            // expected: stranded, unreachable. The §6 residualRecipient rule (not in
            // shipped code) is required to make this state live.
        }
    }
}
