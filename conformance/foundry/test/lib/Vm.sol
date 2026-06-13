// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @dev Minimal cheatcode interface — only what the conformance suite uses.
/// Dependency-free (no forge-std submodule needed).
interface Vm {
    function warp(uint256) external;
    function prank(address) external;
    function startPrank(address) external;
    function stopPrank() external;
    function expectRevert() external;
    function assume(bool) external;
    function store(address, bytes32, bytes32) external;
    function load(address, bytes32) external view returns (bytes32);
}
