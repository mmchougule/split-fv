// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20, LegToken} from "./SplitVault.sol";

/*
 * PutVault — the cash-collateralized mirror of SplitVault (the SHORT side).
 * ------------------------------------------------------------------------
 * Splits S USDC into two complementary, non-liquidatable legs vs a WETH strike:
 *   PutP (cash-secured-put writer leg): min(ETH, S)        -> the LP side
 *   PutN (put / downside leg):          max(0, S - ETH)    -> leveraged short
 *
 * NO ORACLE. Settlement is physical: PutN holders exercise by DELIVERING WETH and
 * receiving S USDC, driven by arbitrage exactly when ETH < S. Every unit is always
 * backed by S USDC (pre-exercise) or 1 WETH (post-exercise). See spec/put-mirror.md.
 *
 * Rounding (vault-safe, mirrors SplitVault):
 *   usdcRequired (mint, in)   : CEIL  -> never under-collateralized
 *   usdcOut      (exercise,out): FLOOR -> vault never overpays
 *   redeemP credits           : FLOOR -> dust stays locked
 *
 * One immutable series. No admin, no upgradeability.
 */
contract PutVault {
    uint256 internal constant ONE = 1e18;

    IERC20 public immutable weth; // delivered on exercise
    IERC20 public immutable usdc; // collateral
    uint256 public immutable strike; // S: USDC (6dp) per 1e18 wei WETH
    uint256 public immutable maturity;
    uint256 public immutable exerciseEnd;
    // Residual-liveness terminal sink (SETTLEMENT_SPEC §6 / T_ResidualLiveness): if all PutP
    // is redeemed away before settlement (pSupplyAt == 0), the frozen residual pools would be
    // permanently unreachable (no P to redeem, redeemP divides by zero). Crediting them to this
    // immutable recipient at settle() makes every settled asset claimable — nothing stranded.
    address public immutable residualRecipient;
    LegToken public immutable P; // PutP — writer leg
    LegToken public immutable N; // PutN — downside leg

    bool public settled;
    uint256 public usdcPool; // leftover USDC frozen for PutP
    uint256 public wethPool; // WETH delivered by exercisers, frozen for PutP
    uint256 public pSupplyAt;

    mapping(address => uint256) public claimableWeth;
    mapping(address => uint256) public claimableUsdc;

    uint256 private _lock = 1;
    modifier nonReentrant() {
        require(_lock == 1, "reentrant");
        _lock = 2;
        _;
        _lock = 1;
    }

    event Mint(address indexed who, uint256 amount, uint256 usdcIn);
    event RedeemPair(address indexed who, uint256 amount, uint256 usdcOut);
    event Exercise(address indexed who, uint256 wethIn, uint256 usdcOut);
    event Settled(uint256 usdcPool, uint256 wethPool, uint256 pSupply);
    event RedeemP(address indexed who, uint256 burned, uint256 usdcCredited, uint256 wethCredited);
    event ClaimWeth(address indexed who, address indexed to, uint256 amount);
    event ClaimUsdc(address indexed who, address indexed to, uint256 amount);

    constructor(
        IERC20 _weth,
        IERC20 _usdc,
        uint256 _strike,
        uint256 _maturity,
        uint256 _window,
        address _residualRecipient
    ) {
        require(_strike > 0, "strike");
        require(_maturity > block.timestamp && _window > 0, "schedule");
        require(_residualRecipient != address(0), "residual recipient");
        weth = _weth;
        usdc = _usdc;
        strike = _strike;
        maturity = _maturity;
        exerciseEnd = _maturity + _window;
        residualRecipient = _residualRecipient;
        P = new LegToken("PutVault P", "pvP");
        N = new LegToken("PutVault N", "pvN");
    }

    /// @notice USDC to lock to mint `amount` units. Rounds UP (vault-safe).
    function usdcRequired(uint256 amount) public view returns (uint256) {
        return (amount * strike + ONE - 1) / ONE;
    }

    /// @notice USDC paid to an exerciser delivering `amount` WETH. Rounds DOWN (vault-safe).
    function usdcOut(uint256 amount) public view returns (uint256) {
        return (amount * strike) / ONE;
    }

    /// @notice Lock `usdcRequired(amount)` USDC, mint `amount` PutP and `amount` PutN.
    function mint(uint256 amount) external nonReentrant {
        require(block.timestamp < maturity, "closed");
        require(amount > 0, "zero");
        uint256 inUsdc = usdcRequired(amount);
        require(usdc.transferFrom(msg.sender, address(this), inUsdc), "usdc in");
        P.mint(msg.sender, amount);
        N.mint(msg.sender, amount);
        emit Mint(msg.sender, amount, inUsdc);
    }

    /// @notice Burn `amount` PutP + `amount` PutN, get the locked USDC back. Oracle-free,
    /// pre-maturity — this is what makes the short non-liquidatable. Returns usdcOut (FLOOR);
    /// any CEIL dust from mint stays locked (vault-safe, mirrors P-redeem flooring).
    function redeemPair(uint256 amount) external nonReentrant {
        require(block.timestamp < maturity, "closed");
        require(amount > 0, "zero");
        uint256 out = usdcOut(amount);
        P.burn(msg.sender, amount);
        N.burn(msg.sender, amount);
        require(usdc.transfer(msg.sender, out), "usdc out");
        emit RedeemPair(msg.sender, amount, out);
    }

    /// @notice During the window, exercise `amount` PutN: deliver `amount` WETH,
    /// receive `usdcOut(amount)` USDC. No price read — arbitrage drives this when ETH < S.
    function exercise(uint256 amount) external nonReentrant {
        require(block.timestamp >= maturity && block.timestamp <= exerciseEnd, "window");
        require(amount > 0, "zero");
        uint256 out = usdcOut(amount);
        N.burn(msg.sender, amount);
        require(weth.transferFrom(msg.sender, address(this), amount), "weth in");
        require(usdc.transfer(msg.sender, out), "usdc out");
        emit Exercise(msg.sender, amount, out);
    }

    /// @notice After the window, freeze pools for PutP holders. Anyone may call.
    function settle() external {
        require(block.timestamp > exerciseEnd, "early");
        require(!settled, "settled");
        usdcPool = usdc.balanceOf(address(this));
        wethPool = weth.balanceOf(address(this));
        pSupplyAt = P.totalSupply();
        settled = true;
        // SPEC §6 terminal rule: with no PutP outstanding, the residual would be unreachable
        // (T_ResidualLiveness). Credit it to the immutable recipient so it stays claimable.
        if (pSupplyAt == 0) {
            if (usdcPool > 0) claimableUsdc[residualRecipient] += usdcPool;
            if (wethPool > 0) claimableWeth[residualRecipient] += wethPool;
        }
        emit Settled(usdcPool, wethPool, pSupplyAt);
    }

    /// @notice After settlement, burn PutP for a pro-rata share of leftover USDC + WETH.
    /// Credits internal balances (pull pattern). Both legs floored -> dust stays locked.
    function redeemP(uint256 amount) external nonReentrant {
        require(settled, "not settled");
        require(amount > 0, "zero");
        require(pSupplyAt > 0, "no residual pool"); // unreachable (no P to burn) but explicit: never div-by-zero
        uint256 usdcCredit = (usdcPool * amount) / pSupplyAt;
        uint256 wethCredit = (wethPool * amount) / pSupplyAt;
        P.burn(msg.sender, amount);
        claimableUsdc[msg.sender] += usdcCredit;
        claimableWeth[msg.sender] += wethCredit;
        emit RedeemP(msg.sender, amount, usdcCredit, wethCredit);
    }

    function claimWeth(address to) external nonReentrant {
        uint256 amt = claimableWeth[msg.sender];
        require(amt > 0, "nothing");
        claimableWeth[msg.sender] = 0;
        require(weth.transfer(to, amt), "weth out");
        emit ClaimWeth(msg.sender, to, amt);
    }

    function claimUsdc(address to) external nonReentrant {
        uint256 amt = claimableUsdc[msg.sender];
        require(amt > 0, "nothing");
        claimableUsdc[msg.sender] = 0;
        require(usdc.transfer(to, amt), "usdc out");
        emit ClaimUsdc(msg.sender, to, amt);
    }
}
