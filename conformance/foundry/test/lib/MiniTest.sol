// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Vm} from "./Vm.sol";

/// @dev Dependency-free test base: cheatcodes + assertions + bound, so the
/// conformance suite runs with no forge-std / git submodule. forge detects
/// test_/invariant_ functions and treats any revert as a failure, so assertions
/// just revert with a message.
abstract contract MiniTest {
    Vm internal constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function assertTrue(bool c, string memory m) internal pure {
        require(c, m);
    }

    function assertEq(uint256 a, uint256 b, string memory m) internal pure {
        require(a == b, m);
    }

    function assertEq(address a, address b, string memory m) internal pure {
        require(a == b, m);
    }

    function assertLe(uint256 a, uint256 b, string memory m) internal pure {
        require(a <= b, m);
    }

    function assertGe(uint256 a, uint256 b, string memory m) internal pure {
        require(a >= b, m);
    }

    function assertGt(uint256 a, uint256 b, string memory m) internal pure {
        require(a > b, m);
    }

    /// @dev forge-std-style inclusive bound into [lo, hi].
    function bound(uint256 x, uint256 lo, uint256 hi) internal pure returns (uint256) {
        require(lo <= hi, "bound: lo>hi");
        uint256 span = hi - lo + 1;
        if (span == 0) return x; // full-range
        return lo + (x % span);
    }
}
