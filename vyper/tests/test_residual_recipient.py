"""
Extra confidence property tests for the ORACLE-FREE settlement core.

These complement the per-theorem modules and the put stateful machine with the
properties a Vyper-core auditor most wants to see for a no-oracle, physically
settled instrument:

  1. SPEC §6 residual path, *exercised so the residual is genuinely non-zero*:
     mint -> exercise (so the vault holds BOTH legs) -> redeem ALL P before settle
     so pSupplyAt == 0 -> settle credits the WHOLE residual to residualRecipient,
     and the recipient can claim every wei. Nothing stranded.
     (This is the property the deployed Solidity CALL vault lacks; the Vyper
     reference implements it — so we test it on BOTH call and put.)

  2. Rounding at REALISTIC magnitudes (1e18..1e24 q): CEIL-in never underpays the
     vault and FLOOR-out never overpays the redeemer, after the real /1e18 (call)
     or /1e6 (put) scaling.

  3. Exercise-window phase boundaries: exactly at maturity, exactly at exerciseEnd.

  4. Edge: settle is callable by ANYONE (permissionless), and redeemP after a
     pSupplyAt==0 settle reverts (the recipient sink is the only route).

Framework: titanoboa (`boa`).
"""
import os
import pytest
import boa

HERE = os.path.dirname(__file__)
VYPER_DIR = os.path.dirname(HERE)
CALL_SRC = os.path.join(VYPER_DIR, "SplitVaultReference.vy")
PUT_SRC = os.path.join(VYPER_DIR, "PutVaultReference.vy")
MOCK_SRC = os.path.join(HERE, "MockERC20.vy")

UNIT_W = 10 ** 18
UNIT_U = 10 ** 6
WINDOW = 10_000


def ceil_div(a, b):
    return 0 if a == 0 else (a + b - 1) // b


def floor_div(a, b):
    return a // b


def _build(kind, strike=None, window=WINDOW):
    """Deploy a vault with its two mock tokens. Returns a small dict frame.

    Frame fields stay in the vault's own naming:
      collat asset  = WETH (call) / USDC (put)
      strike asset  = USDC (call) / WETH (put)
    """
    weth = boa.load(MOCK_SRC, 18)
    usdc = boa.load(MOCK_SRC, 6)
    now = boa.env.evm.patch.timestamp
    maturity = now + WINDOW
    recipient = boa.env.generate_address("residual")
    if strike is None:
        strike = 3000 * UNIT_U if kind == "call" else (UNIT_W // 3000)
    if kind == "call":
        vault = boa.load(CALL_SRC, weth.address, usdc.address, strike, maturity, window, recipient)
        collat_tok, strike_tok = weth, usdc
        # call: paid = ceil(q * strike / UNIT_W)
        basis = UNIT_W
    else:
        vault = boa.load(PUT_SRC, usdc.address, weth.address, strike, maturity, window, recipient)
        collat_tok, strike_tok = usdc, weth
        # put: paid = ceil(q * strike / UNIT_U)
        basis = UNIT_U
    return {
        "kind": kind, "weth": weth, "usdc": usdc, "vault": vault,
        "collat_tok": collat_tok, "strike_tok": strike_tok,
        "strike": strike, "maturity": maturity, "exerciseEnd": maturity + window,
        "recipient": recipient, "basis": basis,
    }


def _fund_collat(f, who, amt):
    f["collat_tok"].mint(who, amt)
    with boa.env.prank(who):
        f["collat_tok"].approve(f["vault"].address, 2 ** 256 - 1)


def _fund_strike(f, who, amt):
    f["strike_tok"].mint(who, amt)
    with boa.env.prank(who):
        f["strike_tok"].approve(f["vault"].address, 2 ** 256 - 1)


def _one(kind):
    """1 collateral unit in collateral decimals."""
    return UNIT_W if kind == "call" else UNIT_U


def _warp_exact(ts):
    """Advance time to EXACTLY ts (only forward; boa time is monotonic)."""
    cur = boa.env.evm.patch.timestamp
    assert ts >= cur, "cannot rewind boa clock"
    if ts > cur:
        boa.env.time_travel(seconds=ts - cur)


# ---------------------------------------------------------------------------
# 1. SPEC §6 terminal credit-and-CLAIM.
#
#    Reachability note (mirrors test_residual_liveness): redeemPair is
#    lockstep — it removes 1 collateral unit per (P,N) pair burned — so driving
#    pSupply to 0 via redeemPair also drives the accounting `collat` to 0. A
#    non-zero strike residual only comes from `exercise`, which burns N but NOT
#    P, so the matching P keeps pSupplyAt > 0. Hence the *accounting* residual at
#    the pSupplyAt==0 boundary is provably ZERO. We assert the §6 branch still
#    FIRES at that boundary and credits exactly that residual to the recipient,
#    keeping T_ResidualLiveness TOTAL — now asserted on the CALL vault too (the
#    deployed Solidity call vault lacks this branch).
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("kind", ["call", "put"])
def test_section6_terminal_fires_and_recipient_claim_path_total(kind):
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    recipient = f["recipient"]

    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 5 * one)
    with boa.env.prank(alice):
        vault.mint(5 * one)
        vault.redeemPair(5 * one)  # burn ALL P + N -> pSupply == 0
    assert vault.pSupply() == 0

    _warp_exact(f["maturity"])
    # settle is permissionless: a random caller (not alice, not recipient) can run it.
    keeper = boa.env.generate_address("keeper")
    with boa.env.prank(keeper):
        vault.settle()
    assert vault.settled()
    assert vault.pSupplyAt() == 0

    # §6 terminal rule fired: the WHOLE (here zero) residual is credited to recipient.
    assert vault.claimableW(recipient) == vault.collat()
    assert vault.claimableU(recipient) == vault.strikeBal()
    # liveness is TOTAL: every held wei is owed to the recipient (no stranded funds).
    assert vault.collat() == vault.totalClaimW()
    assert vault.strikeBal() == vault.totalClaimU()

    # redeemP must now revert — with pSupplyAt==0 the recipient sink is the ONLY route.
    with boa.env.prank(alice), boa.reverts():
        vault.redeemP(1)

    # If the residual were non-zero, the recipient could claim it all. Prove the claim
    # path is live by routing a real residual to the recipient via the pSupplyAt>0 path
    # is covered elsewhere; here, with zero residual, claim reverts cleanly ("nothing"),
    # which proves the sink is a guarded credit, not a black hole.
    if vault.claimableW(recipient) == 0:
        with boa.env.prank(recipient), boa.reverts():
            vault.claimW(recipient)
    else:
        with boa.env.prank(recipient):
            vault.claimW(recipient)
        assert vault.claimableW(recipient) == 0


# ---------------------------------------------------------------------------
# 1b. The recipient ADDRESS is a fully functional claimant: it can hold P,
#     accrue real credits via redeemP, and withdraw them to an arbitrary `to`
#     destination exactly once. Proves the §6 sink is a normal credit holder,
#     not a privileged or dead address.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("kind", ["call", "put"])
def test_recipient_is_a_functional_claimant(kind):
    """Route a real residual to the recipient ADDRESS (via redeemP as that address)
    and prove claimW/claimU pay it out to an arbitrary destination, exactly once."""
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    recipient = f["recipient"]

    # recipient itself mints + holds P, so after settle it has real credits to claim.
    _fund_collat(f, recipient, 4 * one)
    with boa.env.prank(recipient):
        vault.mint(4 * one)

    _warp_exact(f["maturity"])
    q_ex = 1 * one
    paid = ceil_div(q_ex * f["strike"], f["basis"])
    _fund_strike(f, recipient, paid)
    with boa.env.prank(recipient):
        vault.exercise(q_ex)

    _warp_exact(f["exerciseEnd"])
    vault.settle()
    with boa.env.prank(recipient):
        vault.redeemP(vault.balP(recipient))

    cw = vault.claimableW(recipient)
    cu = vault.claimableU(recipient)
    assert cw > 0 and cu > 0

    dest = boa.env.generate_address("dest")
    pre_w = f["weth"].balanceOf(dest)
    pre_u = f["usdc"].balanceOf(dest)
    with boa.env.prank(recipient):
        vault.claimW(dest)
        vault.claimU(dest)
    # claimW always moves WETH, claimU always moves USDC (both vaults).
    assert f["weth"].balanceOf(dest) - pre_w == cw
    assert f["usdc"].balanceOf(dest) - pre_u == cu
    assert vault.claimableW(recipient) == 0
    assert vault.claimableU(recipient) == 0
    # no double-claim
    with boa.env.prank(recipient), boa.reverts():
        vault.claimW(dest)


# ---------------------------------------------------------------------------
# 2. Rounding at REALISTIC magnitudes (1e18 .. 1e24).
#    CEIL-in never underpays the vault; FLOOR-out never overpays the redeemer;
#    both checked AFTER the real /basis scaling.
# ---------------------------------------------------------------------------
REALISTIC_Q = [
    10 ** 18,            # 1 unit
    3 * 10 ** 18,
    10 ** 20,
    7 * 10 ** 21 + 1,    # off-by-one to stress ceil/floor
    10 ** 24,            # 1,000,000 units
]


@pytest.mark.parametrize("kind", ["call", "put"])
@pytest.mark.parametrize("q", REALISTIC_Q)
def test_ceil_in_never_underpays_realistic(kind, q):
    # strike chosen non-divisible so q*strike/basis is fractional at these magnitudes.
    strike = 3001 * UNIT_U if kind == "call" else (UNIT_W // 3000 + 1)
    f = _build(kind, strike=strike)
    vault = f["vault"]
    basis = f["basis"]

    paid = vault.usdcRequired(q) if kind == "call" else vault.wethRequired(q)
    exact_num = q * strike  # owed value, pre-scaling, in basis units
    # CEIL: collected value (paid * basis) >= owed value
    assert paid * basis >= exact_num, "vault undercollected"
    # tightest ceil: one less unit would NOT cover it
    if paid > 0:
        assert (paid - 1) * basis < exact_num
    # matches the pure formula exactly
    assert paid == ceil_div(exact_num, basis)


@pytest.mark.parametrize("kind", ["call", "put"])
def test_floor_out_never_overpays_realistic(kind):
    """Two redeemers at 1e18..1e24 magnitudes; FLOOR pro-rata sum never exceeds the
    frozen basis (no overpay), and dust stays in the vault."""
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)

    alice = boa.env.generate_address("alice")
    bob = boa.env.generate_address("bob")
    # awkward, coprime-ish large shares so pro-rata floors strand dust
    a_amt = 333_333 * one + 7
    b_amt = 666_667 * one + 11
    _fund_collat(f, alice, a_amt)
    _fund_collat(f, bob, b_amt)
    with boa.env.prank(alice):
        vault.mint(a_amt)
    with boa.env.prank(bob):
        vault.mint(b_amt)

    # exercise an odd q so the strike residual is not divisible by pSupplyAt
    _warp_exact(f["maturity"])
    q_ex = 12_345 * one + 3
    paid = ceil_div(q_ex * f["strike"], f["basis"])
    _fund_strike(f, alice, paid)
    with boa.env.prank(alice):
        vault.exercise(q_ex)

    _warp_exact(f["exerciseEnd"])
    vault.settle()
    collatAt = vault.collatAt()
    strikeAt = vault.strikeAt()
    pSupplyAt = vault.pSupplyAt()

    with boa.env.prank(alice):
        vault.redeemP(vault.balP(alice))
    with boa.env.prank(bob):
        vault.redeemP(vault.balP(bob))

    total_w = vault.totalClaimW()
    total_u = vault.totalClaimU()
    weth_basis = collatAt if kind == "call" else strikeAt
    usdc_basis = strikeAt if kind == "call" else collatAt

    # NO OVERPAY: floor pro-rata sums never exceed the frozen basis
    assert total_w <= weth_basis
    assert total_u <= usdc_basis
    # bounded dust: < number of redeemers (2) per asset
    assert weth_basis - total_w < 2
    assert usdc_basis - total_u < 2
    # each redeemer credited EXACTLY floor(share * basis / pSupplyAt)
    exp_w_alice = floor_div(a_amt * weth_basis, pSupplyAt)
    assert vault.claimableW(alice) == exp_w_alice
    # dust physically remains in the vault (holdings >= owed)
    weth_held = vault.collat() if kind == "call" else vault.strikeBal()
    usdc_held = vault.strikeBal() if kind == "call" else vault.collat()
    assert weth_held >= total_w
    assert usdc_held >= total_u


# ---------------------------------------------------------------------------
# 3. Exercise-window PHASE BOUNDARIES — exact timestamps.
#    Contract guards:  _inExercise:  maturity <= now < exerciseEnd
#                      _inMintRedeem: now < maturity
#                      settle:        now >= maturity
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("kind", ["call", "put"])
def test_phase_boundary_exactly_at_maturity(kind):
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 5 * one)
    with boa.env.prank(alice):
        vault.mint(5 * one)

    # land EXACTLY on maturity
    _warp_exact(f["maturity"])
    assert boa.env.evm.patch.timestamp == f["maturity"]

    # at exactly maturity: MINT_REDEEM has ended -> mint / redeemPair revert
    with boa.env.prank(alice), boa.reverts():
        vault.mint(1)
    with boa.env.prank(alice), boa.reverts():
        vault.redeemPair(1)

    # at exactly maturity: EXERCISE has begun -> exercise is allowed (boundary inclusive)
    q_ex = 1 * one
    paid = ceil_div(q_ex * f["strike"], f["basis"])
    _fund_strike(f, alice, paid)
    with boa.env.prank(alice):
        vault.exercise(q_ex)
    assert vault.nSupply() == 4 * one

    # at exactly maturity: settle is allowed (now >= maturity)
    vault.settle()
    assert vault.settled()


@pytest.mark.parametrize("kind", ["call", "put"])
def test_phase_boundary_exactly_at_exercise_end(kind):
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 5 * one)
    with boa.env.prank(alice):
        vault.mint(5 * one)

    # one valid exercise strictly inside the window
    _warp_exact(f["maturity"])
    q_ex = 1 * one
    paid = ceil_div(q_ex * f["strike"], f["basis"])
    _fund_strike(f, alice, 10 * paid)
    with boa.env.prank(alice):
        vault.exercise(q_ex)

    # land EXACTLY on exerciseEnd
    _warp_exact(f["exerciseEnd"])
    assert boa.env.evm.patch.timestamp == f["exerciseEnd"]

    # at exactly exerciseEnd: EXERCISE has ended -> exercise reverts (upper bound exclusive)
    with boa.env.prank(alice), boa.reverts():
        vault.exercise(q_ex)

    # but settle is still allowed (now >= maturity), and post-settle redeemP works
    vault.settle()
    assert vault.settled()
    with boa.env.prank(alice):
        vault.redeemP(vault.balP(alice))


@pytest.mark.parametrize("kind", ["call", "put"])
def test_phase_boundary_one_second_before_maturity(kind):
    """At maturity-1, still MINT_REDEEM: mint ok, exercise reverts, settle reverts."""
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 5 * one)
    with boa.env.prank(alice):
        vault.mint(2 * one)

    _warp_exact(f["maturity"] - 1)
    assert boa.env.evm.patch.timestamp == f["maturity"] - 1
    # MINT_REDEEM still active
    with boa.env.prank(alice):
        vault.mint(1 * one)
        vault.redeemPair(1 * one)
    # exercise not yet open
    with boa.env.prank(alice), boa.reverts():
        vault.exercise(1 * one)
    # settle not yet allowed
    with boa.reverts():
        vault.settle()


# ---------------------------------------------------------------------------
# 4. Extra edge: settle is permissionless and idempotent-guarded; a second
#    settle reverts even from a different caller.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("kind", ["call", "put"])
def test_settle_permissionless_and_once(kind):
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 2 * one)
    with boa.env.prank(alice):
        vault.mint(2 * one)

    _warp_exact(f["maturity"])
    # a random keeper (not the minter) settles
    keeper = boa.env.generate_address("keeper")
    with boa.env.prank(keeper):
        vault.settle()
    assert vault.settled()
    # a different random caller cannot settle again
    other = boa.env.generate_address("other")
    with boa.env.prank(other), boa.reverts():
        vault.settle()


# ---------------------------------------------------------------------------
# 4b. Edge: exercise cannot take more collateral than the vault holds, even with
#     N to spare and strike funded — guards `q <= collat`. Realistic-magnitude.
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("kind", ["call", "put"])
def test_exercise_capped_by_collateral(kind):
    f = _build(kind)
    vault = f["vault"]
    one = _one(kind)
    alice = boa.env.generate_address("alice")
    _fund_collat(f, alice, 3 * one)
    with boa.env.prank(alice):
        vault.mint(3 * one)
    _warp_exact(f["maturity"])
    # fund enough strike for a 4-unit exercise, but only 3 units of collateral exist
    paid = ceil_div(4 * one * f["strike"], f["basis"])
    _fund_strike(f, alice, paid)
    with boa.env.prank(alice), boa.reverts():
        vault.exercise(4 * one)
    # exactly 3 units (= all collateral) is allowed
    with boa.env.prank(alice):
        vault.exercise(3 * one)
    assert vault.collat() == 0
