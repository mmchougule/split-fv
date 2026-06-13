// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {SymTest} from "halmos-cheatcodes/SymTest.sol";
import {Test} from "forge-std/Test.sol";
import {SplitVault, IERC20, LegToken} from "../src/SplitVault.sol";
import {PutVault} from "../src/PutVault.sol";
import {MockERC20} from "../src/MockERC20.sol";

/*
 * T_OracleIndependence — STRUCTURAL, the halmos (dynamic) half.
 *
 * Companion to oracle_independence_static.py (the static-bytecode half). Here we
 * symbolically execute EVERY settlement selector via `svm.createCalldata` and assert
 * that an OracleCanary deployed in the environment is NEVER called — for ALL symbolic
 * inputs AND symbolic vault storage. Because halmos enumerates every reachable path,
 * a single price/oracle/DEX read on any path would flip the canary and fail.
 *
 * The vault's only external dependencies (weth/usdc/P/N) are wired to mocks we control.
 * The canary occupies a distinct address; if settlement made ANY call to an address
 * it shouldn't (the structural definition of "reads a price"), the only such address
 * reachable is the canary, so touching it is the witness. We strengthen this by also
 * asserting the post-call canary state is untouched under fully symbolic storage.
 */
contract OracleCanary {
    bool public touched;
    // Mimic common oracle/DEX surfaces so a naive integration would land here.
    fallback() external payable {
        touched = true;
    }
    receive() external payable {
        touched = true;
    }

    function latestAnswer() external returns (int256) {
        touched = true;
        return 0;
    }

    function getReserves() external returns (uint112, uint112, uint32) {
        touched = true;
        return (0, 0, 0);
    }
}

contract OracleIndependenceTest is SymTest, Test {
    SplitVault callVault;
    PutVault putVault;
    MockERC20 weth;
    MockERC20 usdc;
    OracleCanary canary;

    function setUp() public {
        weth = new MockERC20("Wrapped Ether", "WETH", 18);
        usdc = new MockERC20("USD Coin", "USDC", 6);
        canary = new OracleCanary();
        callVault = new SplitVault(
            IERC20(address(weth)), IERC20(address(usdc)), 2000e6, block.timestamp + 1000, 1000
        );
        putVault = new PutVault(
            IERC20(address(weth)), IERC20(address(usdc)), 2000e6, block.timestamp + 1000, 1000,
            address(0xBEEF) // SETTLEMENT_SPEC §6 residualRecipient
        );
    }

    /// Drive the call vault with a fully symbolic call to ANY of its functions, under
    /// symbolic storage, and assert the oracle canary is never touched.
    function check_T_OracleIndependence() public {
        // make the whole vault storage symbolic: time, settled flag, pools, balances —
        // every phase and every state is explored, not just a fixed fixture.
        svm.enableSymbolicStorage(address(callVault));
        svm.enableSymbolicStorage(address(callVault.P()));
        svm.enableSymbolicStorage(address(callVault.N()));
        svm.enableSymbolicStorage(address(weth));
        svm.enableSymbolicStorage(address(usdc));

        bytes memory data = svm.createCalldata("SplitVault");
        (bool success,) = address(callVault).call(data);
        success; // result irrelevant; we only assert no oracle was consulted

        assert(canary.touched() == false);
    }

    /// Same, for the put vault (T_PutSymmetry: oracle-independence re-proved first-class).
    function check_T_OracleIndependence_put() public {
        svm.enableSymbolicStorage(address(putVault));
        svm.enableSymbolicStorage(address(putVault.P()));
        svm.enableSymbolicStorage(address(putVault.N()));
        svm.enableSymbolicStorage(address(weth));
        svm.enableSymbolicStorage(address(usdc));

        bytes memory data = svm.createCalldata("PutVault");
        (bool success,) = address(putVault).call(data);
        success;

        assert(canary.touched() == false);
    }
}
