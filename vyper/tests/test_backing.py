"""
T_Backing — claims never exceed holdings.

Pre-settle: nSupply <= collat (every N is collateral-backed).
Post-settle: totalClaimW <= collat AND totalClaimU <= strikeBal (credits <= holdings).

We drive the real transition surface (call AND put) and assert backing holds after EVERY
transition, including the §6 terminal residual path.
"""
import pytest

U = 10 ** 18


def _weth_held(env):
    # WETH is collateral on the call vault, strike asset on the put vault.
    return env.v("collat") if env.kind == "call" else env.v("strikeBal")


def _usdc_held(env):
    # USDC is strike asset on the call vault, collateral on the put vault.
    return env.v("strikeBal") if env.kind == "call" else env.v("collat")


def _assert_backing(env):
    if not env.v("settled"):
        # pre-settle WF (State.lean): collateral exactly backs live N (`collEqN`),
        # and N never exceeds P (`nLeP` — the gap counts exercised units). Note the
        # naive `pSupply == nSupply` is NOT an invariant: exercise lowers nSupply +
        # collat together but leaves pSupply untouched (see State.lean §WF comment).
        assert env.v("collat") == env.v("nSupply")
        assert env.v("nSupply") <= env.v("pSupply")
    else:
        # post-settle: outstanding credits never exceed the vault's holdings of that asset.
        # totalClaimW is the WETH credit; totalClaimU is the USDC credit (both vaults).
        assert env.v("totalClaimW") <= _weth_held(env)
        assert env.v("totalClaimU") <= _usdc_held(env)
    # token-ledger backing: vault's real ERC20 balance always >= internal accounting
    assert env.vault_collat_token_bal() >= env.v("collat")
    assert env.vault_strike_token_bal() >= env.v("strikeBal")


def test_backing(make_vault, accounts, kind):
    env = make_vault(kind)
    a, b = accounts[1], accounts[2]
    one = U if kind == "call" else 10 ** 6  # 1 collateral unit in collateral decimals

    env.fund_collat(a, 5 * one)
    env.mint(a, 5 * one)
    _assert_backing(env)

    env.redeemPair(a, 1 * one)
    _assert_backing(env)

    env.into_exercise()
    paid = env.required_in(2 * one)
    env.fund_strike(a, paid)
    env.exercise(a, 2 * one)
    _assert_backing(env)

    env.settle()
    _assert_backing(env)

    # a holds P (minted 5, redeemed-pair 1 -> 4 P). redeem 4 P.
    env.redeemP(a, 4 * one)
    _assert_backing(env)

    env.claimW(a)
    _assert_backing(env)
    env.claimU(a)
    _assert_backing(env)


def test_backing_residual_recipient_path(make_vault, accounts, kind):
    """§6 terminal: all P redeemed before settle -> residual credited to recipient, still backed."""
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 3 * one)
    env.mint(a, 3 * one)
    # burn ALL P+N back via redeemPair so pSupply == 0 at settle
    env.redeemPair(a, 3 * one)
    assert env.v("pSupply") == 0
    env.into_exercise()
    env.settle()
    _assert_backing(env)
    # recipient can claim whatever residual exists (here zero), backing preserved
    assert env.v("totalClaimW") <= _weth_held(env)
    assert env.v("totalClaimU") <= _usdc_held(env)
