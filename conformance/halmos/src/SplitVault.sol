// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/*
 * SplitVault — physically-settled, oracle-free WETH/USDC option split
 * -------------------------------------------------------------------
 * Splits WETH into two complementary, non-liquidatable legs against a USDC strike:
 *   P (covered-call leg): keeps WETH unless assigned, then gets S USDC  -> ETH floor
 *   N (call leg):         may pay S USDC to take 1 WETH                  -> ETH upside
 *
 * NO ORACLE IS EVER READ. Settlement is physical: N holders exercise by paying
 * the strike, driven by arbitrage exactly when WETH > S USDC. Solvency is
 * structural — every minted unit is always backed by 1 WETH or S USDC.
 *
 * Lifecycle (European with an exercise window):
 *   [genesis, M)     mint / redeemPair        (oracle-free 1:1:1 recombination)
 *   [M, M+W]         exercise                  (N pays S·a/1e18 USDC, gets a WETH)
 *   (M+W, inf)       settle once, then redeemP (P shares leftover WETH + USDC in)
 *                    unexercised N expire worthless (they were OTM by choice)
 *
 * Integer math mirrors proofs/conservation_physical.py exactly:
 *   exercise USDC owed : CEIL  -> payer never underpays
 *   P redemption       : FLOOR -> leftover dust stays locked
 *
 * Each vault is one immutable series. No admin, no upgradeability — by design
 * for the first audited series.
 */

interface IERC20 {
    function transfer(address to, uint256 amt) external returns (bool);
    function transferFrom(address from, address to, uint256 amt) external returns (bool);
    function balanceOf(address who) external view returns (uint256);
}

/// @dev Minimal ERC20 leg token; only the owning vault may mint/burn.
contract LegToken {
    string public name;
    string public symbol;
    uint8 public constant decimals = 18;
    uint256 public totalSupply;
    address public immutable vault;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor(string memory _name, string memory _symbol) {
        name = _name;
        symbol = _symbol;
        vault = msg.sender;
    }

    function mint(address to, uint256 amt) external {
        require(msg.sender == vault, "not vault");
        totalSupply += amt;
        balanceOf[to] += amt;
        emit Transfer(address(0), to, amt);
    }

    function burn(address from, uint256 amt) external {
        require(msg.sender == vault, "not vault");
        balanceOf[from] -= amt;
        totalSupply -= amt;
        emit Transfer(from, address(0), amt);
    }

    function approve(address spender, uint256 amt) external returns (bool) {
        allowance[msg.sender][spender] = amt;
        emit Approval(msg.sender, spender, amt);
        return true;
    }

    function transfer(address to, uint256 amt) external returns (bool) {
        balanceOf[msg.sender] -= amt;
        balanceOf[to] += amt;
        emit Transfer(msg.sender, to, amt);
        return true;
    }

    function transferFrom(address from, address to, uint256 amt) external returns (bool) {
        uint256 a = allowance[from][msg.sender];
        if (a != type(uint256).max) allowance[from][msg.sender] = a - amt;
        balanceOf[from] -= amt;
        balanceOf[to] += amt;
        emit Transfer(from, to, amt);
        return true;
    }
}

contract SplitVault {
    uint256 internal constant ONE = 1e18; // WETH scale

    // ---- immutable series parameters -------------------------------------
    IERC20  public immutable weth;        // collateral A
    IERC20  public immutable usdc;        // strike numeraire B
    uint256 public immutable strike;      // S: USDC (6dp) owed per 1e18 wei WETH
    uint256 public immutable maturity;    // M: exercise window opens
    uint256 public immutable exerciseEnd; // M + W: exercise window closes
    LegToken public immutable P;          // covered-call / floor leg
    LegToken public immutable N;          // call / upside leg

    // ---- settlement state ------------------------------------------------
    bool    public settled;
    uint256 public wethPool;   // leftover WETH frozen for P
    uint256 public usdcPool;   // USDC taken in from exercisers, frozen for P
    uint256 public pSupplyAt;  // P supply snapshot at settle

    // Pull-pattern credits (M-1): redeemP credits these; claims move tokens.
    // Decoupling WETH/USDC means a blacklisted/reverting recipient on one asset
    // can never block the other, and claims can be routed to a fresh address.
    mapping(address => uint256) public claimableWeth;
    mapping(address => uint256) public claimableUsdc;

    // ---- reentrancy guard (defense-in-depth; CEI is already respected) ----
    uint256 private _lock = 1;
    modifier nonReentrant() {
        require(_lock == 1, "reentrant");
        _lock = 2;
        _;
        _lock = 1;
    }

    event Mint(address indexed who, uint256 amount);
    event RedeemPair(address indexed who, uint256 amount);
    event Exercise(address indexed who, uint256 wethOut, uint256 usdcIn);
    event Settled(uint256 wethPool, uint256 usdcPool, uint256 pSupply);
    event RedeemP(address indexed who, uint256 burned, uint256 wethCredited, uint256 usdcCredited);
    event ClaimWeth(address indexed who, address indexed to, uint256 amount);
    event ClaimUsdc(address indexed who, address indexed to, uint256 amount);

    constructor(
        IERC20 _weth,
        IERC20 _usdc,
        uint256 _strike,
        uint256 _maturity,
        uint256 _window
    ) {
        require(_strike > 0, "strike");
        require(_maturity > block.timestamp && _window > 0, "schedule");
        weth = _weth;
        usdc = _usdc;
        strike = _strike;
        maturity = _maturity;
        exerciseEnd = _maturity + _window;
        P = new LegToken("SplitVault P", "svP");
        N = new LegToken("SplitVault N", "svN");
    }

    /// @notice USDC required to exercise `amount` wei of N. Rounds UP (vault-safe).
    function usdcOwed(uint256 amount) public view returns (uint256) {
        return (amount * strike + ONE - 1) / ONE;
    }

    /// @notice Lock `amount` WETH, mint `amount` P and `amount` N (1:1:1).
    function mint(uint256 amount) external nonReentrant {
        require(block.timestamp < maturity, "closed");
        require(amount > 0, "zero");
        require(weth.transferFrom(msg.sender, address(this), amount), "weth in");
        P.mint(msg.sender, amount);
        N.mint(msg.sender, amount);
        emit Mint(msg.sender, amount);
    }

    /// @notice Burn `amount` P + `amount` N together, get `amount` WETH back.
    /// Oracle-free, pre-maturity. This is what makes the position non-liquidatable.
    function redeemPair(uint256 amount) external nonReentrant {
        require(block.timestamp < maturity, "closed");
        require(amount > 0, "zero");
        P.burn(msg.sender, amount);
        N.burn(msg.sender, amount);
        require(weth.transfer(msg.sender, amount), "weth out");
        emit RedeemPair(msg.sender, amount);
    }

    /// @notice During the window, exercise `amount` N: pay S·amount/1e18 USDC,
    /// receive `amount` WETH. No price is read — arbitrage drives this when ITM.
    function exercise(uint256 amount) external nonReentrant {
        require(block.timestamp >= maturity && block.timestamp <= exerciseEnd, "window");
        require(amount > 0, "zero");
        uint256 owed = usdcOwed(amount);
        N.burn(msg.sender, amount);                       // J5: burns from N supply
        require(usdc.transferFrom(msg.sender, address(this), owed), "usdc in");
        require(weth.transfer(msg.sender, amount), "weth out");
        emit Exercise(msg.sender, amount, owed);
    }

    /// @notice After the window closes, freeze the pools for P holders. Anyone may call.
    function settle() external {
        require(block.timestamp > exerciseEnd, "early");
        require(!settled, "settled");
        wethPool = weth.balanceOf(address(this)); // leftover WETH (== minted - exercised)
        usdcPool = usdc.balanceOf(address(this)); // USDC collected from exercisers
        pSupplyAt = P.totalSupply();
        settled = true;
        emit Settled(wethPool, usdcPool, pSupplyAt);
    }

    /// @notice After settlement, burn P for a pro-rata share of leftover WETH + USDC.
    /// Credits internal balances (pull pattern); call claimWeth / claimUsdc to withdraw.
    /// Both legs floored -> dust stays locked (mirrors proof invariants J1/J2).
    function redeemP(uint256 amount) external nonReentrant {
        require(settled, "not settled");
        require(amount > 0, "zero");
        uint256 wethCredit = (wethPool * amount) / pSupplyAt;
        uint256 usdcCredit = (usdcPool * amount) / pSupplyAt;
        P.burn(msg.sender, amount);
        claimableWeth[msg.sender] += wethCredit;
        claimableUsdc[msg.sender] += usdcCredit;
        emit RedeemP(msg.sender, amount, wethCredit, usdcCredit);
    }

    /// @notice Withdraw your credited WETH to `to`. Independent of USDC.
    function claimWeth(address to) external nonReentrant {
        uint256 amt = claimableWeth[msg.sender];
        require(amt > 0, "nothing");
        claimableWeth[msg.sender] = 0;            // CEI: zero before transfer
        require(weth.transfer(to, amt), "weth out");
        emit ClaimWeth(msg.sender, to, amt);
    }

    /// @notice Withdraw your credited USDC to `to`. Independent of WETH.
    function claimUsdc(address to) external nonReentrant {
        uint256 amt = claimableUsdc[msg.sender];
        require(amt > 0, "nothing");
        claimableUsdc[msg.sender] = 0;            // CEI: zero before transfer
        require(usdc.transfer(to, amt), "usdc out");
        emit ClaimUsdc(msg.sender, to, amt);
    }
}
