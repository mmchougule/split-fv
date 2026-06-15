# pragma version ^0.4.0
# @license MIT
#
# Split PUT vault — FIRST-CLASS reference of the settlement core (SPEC §4, §6, §7).
# NOT a mirror of the call vault: this is a peer implementation with roles swapped.
#
#   collateral   = USDC (6 decimals)   -> held in `collat`
#   strike asset = WETH (18 decimals)  -> held in `strikeBal`
#   exercise     pays WETH strike IN, sends USDC collateral OUT
#
# Every function corresponds 1:1 to a transition in lean/Split/Transitions.lean:
#   mint        <-> Split.mint        (1 USDC unit => 1 P + 1 N)
#   redeemPair  <-> Split.redeemPair  (burn q P + q N, send q USDC out)
#   exercise    <-> Split.exercise    (CEIL WETH in, burn q N, q USDC out)
#   settle      <-> Split.settle      (snapshot + §6 residual terminal rule)
#   redeemP     <-> Split.redeemP     (burn q P, FLOOR pro-rata credit)
#   claimW      <-> Split.claimW      (zero-before-send WETH)   [strike asset]
#   claimU      <-> Split.claimU      (zero-before-send USDC)   [collateral]
#
# NO oracle, NO price input, NO UI/keeper/pricing/routing/wrappers. Settlement is
# balance/exercise-driven only. "Oracle-free" = no settlement transition reads a price.
#
# Rounding discipline (SPEC §4): CEIL on money coming IN (exercise WETH), FLOOR on
# money going OUT (redeemP credits). So rounding can only ever keep MORE in the vault,
# never less (T_RoundingMonotone). redeemPair sends exactly `q` (frozen-model semantics:
# mint pulled exactly `q` USDC, redeemPair returns exactly `q`).

from ethereum.ercs import IERC20

# ----------------------------------------------------------------------------
# Units (SPEC §1) — carried EXPLICITLY; no implicit scaling, no mixed decimals.
# ----------------------------------------------------------------------------
UNIT_U: constant(uint256) = 10 ** 6    # USDC (collateral) 6dp
UNIT_W: constant(uint256) = 10 ** 18   # WETH (strike asset) 18dp

# ----------------------------------------------------------------------------
# Immutable parameters (never change after deploy).
# ----------------------------------------------------------------------------
usdc: public(immutable(IERC20))   # collateral asset
weth: public(immutable(IERC20))   # strike asset (delivered on exercise)
# strike: WETH-wei delivered per 1 USDC collateral unit, in UNIT_U basis.
#   paid_weth = ceilDiv(q_usdc * strike, UNIT_U)
strike: public(immutable(uint256))
maturity: public(immutable(uint256))
exerciseEnd: public(immutable(uint256))
# Immutable sink for the §6 terminal rule (pSupplyAt == 0 at settle).
residualRecipient: public(immutable(address))

# ----------------------------------------------------------------------------
# Mutable accounting state — frozen field names mirror SETTLEMENT_SPEC §2.
# ----------------------------------------------------------------------------
collat: public(uint256)      # USDC units held by the vault
strikeBal: public(uint256)   # WETH units held by the vault
pSupply: public(uint256)     # outstanding P
nSupply: public(uint256)     # outstanding N
settled: public(bool)
pSupplyAt: public(uint256)   # P supply frozen at settle
collatAt: public(uint256)    # collateral (USDC) frozen at settle
strikeAt: public(uint256)    # strike balance (WETH) frozen at settle

# pull-pattern claim credits = SPEC §2 frozen fields claimW (WETH/strike) and claimU
# (USDC/collateral). NAME-CLASH NOTE: the SPEC §4 transitions are ALSO named claimW/claimU,
# and Vyper puts storage vars and functions in one `self` namespace, so the storage maps are
# stored as `_claimW`/`_claimU` and exposed via explicit getters claimableW/claimableU. The
# *transition functions* keep the frozen names claimW()/claimU() (what THEOREM_MAP references).
_claimW: HashMap[address, uint256]
_claimU: HashMap[address, uint256]
balP: public(HashMap[address, uint256])
balN: public(HashMap[address, uint256])

@view
@external
def claimableW(who: address) -> uint256:
    return self._claimW[who]

@view
@external
def claimableU(who: address) -> uint256:
    return self._claimU[who]

# ghost aggregate totals (mirror Lean totalClaimW / totalClaimU for conformance).
totalClaimW: public(uint256)
totalClaimU: public(uint256)

# reentrancy guard (claims are zero-before-send, but guard the external calls too).
_locked: bool

@deploy
def __init__(
    _usdc: IERC20,
    _weth: IERC20,
    _strike: uint256,
    _maturity: uint256,
    _window: uint256,
    _residualRecipient: address,
):
    assert _strike > 0, "strike"
    assert _maturity > block.timestamp, "maturity"
    assert _window > 0, "window"
    assert _residualRecipient != empty(address), "recipient"
    usdc = _usdc
    weth = _weth
    strike = _strike
    maturity = _maturity
    exerciseEnd = _maturity + _window
    residualRecipient = _residualRecipient

# ----------------------------------------------------------------------------
# Rounding helpers (SPEC §4): ceilDiv for IN, floorDiv for OUT.
# ----------------------------------------------------------------------------
@pure
@internal
def _ceilDiv(a: uint256, b: uint256) -> uint256:
    # b is a nonzero compile-time-ish UNIT; assert keeps it total.
    assert b != 0, "div0"
    return unsafe_div(a + b - 1, b) if a != 0 else 0

@pure
@internal
def _floorDiv(a: uint256, b: uint256) -> uint256:
    assert b != 0, "div0"
    return a // b

@view
@external
def wethRequired(q: uint256) -> uint256:
    # WETH a PutN exerciser must DELIVER to take `q` USDC collateral. CEIL (vault-safe).
    return self._ceilDiv(q * strike, UNIT_U)

# ----------------------------------------------------------------------------
# Phase guards (SPEC §3). Each transition callable ONLY in its phase (T_PhaseSafety).
# ----------------------------------------------------------------------------
@view
@internal
def _inMintRedeem() -> bool:
    return (not self.settled) and (block.timestamp < maturity)

@view
@internal
def _inExercise() -> bool:
    return (not self.settled) and (maturity <= block.timestamp) and (block.timestamp < exerciseEnd)

# ----------------------------------------------------------------------------
# 1. mint(q) [MINT_REDEEM, q>0] — pull q USDC in; mint q P + q N. (1:1:1)
# ----------------------------------------------------------------------------
@external
def mint(q: uint256):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self._inMintRedeem(), "phase"
    assert q > 0, "zero"
    # pull collateral IN
    assert extcall usdc.transferFrom(msg.sender, self, q, default_return_value=True), "usdc in"
    self.collat += q
    self.pSupply += q
    self.nSupply += q
    self.balP[msg.sender] += q
    self.balN[msg.sender] += q
    self._locked = False

# ----------------------------------------------------------------------------
# 2. redeemPair(q) [MINT_REDEEM, q>0, balP>=q & balN>=q] — burn q P + q N, send q USDC out.
# ----------------------------------------------------------------------------
@external
def redeemPair(q: uint256):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self._inMintRedeem(), "phase"
    assert q > 0, "zero"
    assert self.balP[msg.sender] >= q, "balP"
    assert self.balN[msg.sender] >= q, "balN"
    assert q <= self.collat, "collat"
    self.balP[msg.sender] -= q
    self.balN[msg.sender] -= q
    self.pSupply -= q
    self.nSupply -= q
    self.collat -= q
    assert extcall usdc.transfer(msg.sender, q, default_return_value=True), "usdc out"
    self._locked = False

# ----------------------------------------------------------------------------
# 3. exercise(q) [EXERCISE, q>0, balN>=q] — pay CEIL WETH strike IN, burn q N, send q USDC OUT.
#    paid = ceilDiv(q * strike, UNIT_U). No price read — arbitrage drives this when ETH < S.
# ----------------------------------------------------------------------------
@external
def exercise(q: uint256):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self._inExercise(), "phase"
    assert q > 0, "zero"
    assert self.balN[msg.sender] >= q, "balN"
    assert q <= self.collat, "collat"
    paid: uint256 = self._ceilDiv(q * strike, UNIT_U)  # CEIL in (vault-safe)
    # burn N first
    self.balN[msg.sender] -= q
    self.nSupply -= q
    # pull WETH strike IN
    assert extcall weth.transferFrom(msg.sender, self, paid, default_return_value=True), "weth in"
    self.strikeBal += paid
    # send USDC collateral OUT
    self.collat -= q
    assert extcall usdc.transfer(msg.sender, q, default_return_value=True), "usdc out"
    self._locked = False

# ----------------------------------------------------------------------------
# 4. settle() [now >= exerciseEnd, !settled] — snapshot pools + §6 terminal residual rule.
#    Anyone may call, but only AFTER the exercise window closes (now >= exerciseEnd) so settle
#    can never preempt an in-window exercise (matches Lean guard `exerciseEnd <= now`).
# ----------------------------------------------------------------------------
@external
def settle():
    assert not self.settled, "settled"
    assert block.timestamp >= exerciseEnd, "early"
    self.settled = True
    self.pSupplyAt = self.pSupply
    self.collatAt = self.collat
    self.strikeAt = self.strikeBal
    # §6 terminal rule: if no P outstanding at settle, the entire residual would be
    # unreachable -> credit it ALL to the immutable residualRecipient (claimable),
    # making T_ResidualLiveness total. Otherwise residual is pro-rata P-redeemable.
    if self.pSupply == 0:
        self._claimU[residualRecipient] += self.collat      # USDC collateral residual
        self._claimW[residualRecipient] += self.strikeBal   # WETH strike residual
        self.totalClaimU += self.collat
        self.totalClaimW += self.strikeBal

# ----------------------------------------------------------------------------
# 5. redeemP(q) [SETTLED, pSupplyAt>0, q>0, balP>=q] — burn q P, FLOOR pro-rata credit.
#    claimU += floor(q*collatAt/pSupplyAt) ; claimW += floor(q*strikeAt/pSupplyAt).
# ----------------------------------------------------------------------------
@external
def redeemP(q: uint256):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self.settled, "not settled"
    assert self.pSupplyAt > 0, "no basis"
    assert q > 0, "zero"
    assert self.balP[msg.sender] >= q, "balP"
    cu: uint256 = self._floorDiv(q * self.collatAt, self.pSupplyAt)   # FLOOR out (USDC)
    cw: uint256 = self._floorDiv(q * self.strikeAt, self.pSupplyAt)   # FLOOR out (WETH)
    self.balP[msg.sender] -= q
    self.pSupply -= q
    self._claimU[msg.sender] += cu
    self._claimW[msg.sender] += cw
    self.totalClaimU += cu
    self.totalClaimW += cw
    self._locked = False

# ----------------------------------------------------------------------------
# 6a. claimW() [SETTLED] — zero-before-send the caller's WETH (strike) credit. T_ClaimNoDouble.
# ----------------------------------------------------------------------------
@external
def claimW(to: address):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self.settled, "not settled"
    amt: uint256 = self._claimW[msg.sender]
    assert amt > 0, "nothing"
    assert amt <= self.strikeBal, "bal"
    self._claimW[msg.sender] = 0          # ZERO BEFORE SEND
    self.totalClaimW -= amt
    self.strikeBal -= amt
    assert extcall weth.transfer(to, amt, default_return_value=True), "weth out"
    self._locked = False

# ----------------------------------------------------------------------------
# 6b. claimU() [SETTLED] — zero-before-send the caller's USDC (collateral) credit.
# ----------------------------------------------------------------------------
@external
def claimU(to: address):
    assert not self._locked, "reentrant"
    self._locked = True
    assert self.settled, "not settled"
    amt: uint256 = self._claimU[msg.sender]
    assert amt > 0, "nothing"
    assert amt <= self.collat, "bal"
    self._claimU[msg.sender] = 0          # ZERO BEFORE SEND
    self.totalClaimU -= amt
    self.collat -= amt
    assert extcall usdc.transfer(to, amt, default_return_value=True), "usdc out"
    self._locked = False
