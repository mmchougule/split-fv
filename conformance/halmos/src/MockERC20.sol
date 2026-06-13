// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "./SplitVault.sol";

/// @dev Minimal, faithful ERC20 used as the WETH/USDC stand-in for symbolic checks.
/// No transfer hooks, no rebasing, no blacklist — exactly the trusted-token model in
/// ASSUMPTIONS_AND_BOUNDARY.md. transfer/transferFrom revert on insufficient balance
/// (checked arithmetic), which is the property the settlement-core safety relies on.
contract MockERC20 is IERC20 {
    string public name;
    string public symbol;
    uint8 public immutable decimals;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    constructor(string memory _name, string memory _symbol, uint8 _decimals) {
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
    }

    function mint(address to, uint256 amt) external {
        totalSupply += amt;
        balanceOf[to] += amt;
    }

    function approve(address spender, uint256 amt) external returns (bool) {
        allowance[msg.sender][spender] = amt;
        return true;
    }

    function transfer(address to, uint256 amt) external returns (bool) {
        balanceOf[msg.sender] -= amt; // reverts on underflow (0.8 checked)
        balanceOf[to] += amt;
        return true;
    }

    function transferFrom(address from, address to, uint256 amt) external returns (bool) {
        uint256 a = allowance[from][msg.sender];
        if (a != type(uint256).max) allowance[from][msg.sender] = a - amt;
        balanceOf[from] -= amt;
        balanceOf[to] += amt;
        return true;
    }
}
