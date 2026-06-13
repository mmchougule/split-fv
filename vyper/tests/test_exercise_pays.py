"""
T_ExercisePays — no free collateral.

exercise(q) removes q collateral OUT only after CEIL(q*strike) strike-asset was paid IN.
We assert: (a) the strike paid equals the CEIL formula, (b) collateral out == q, and
(c) exercise reverts if the caller cannot pay the strike (no collateral leaves without payment).
Call AND put.
"""
from conftest import expect_revert, UNIT_W, UNIT_U

U = 10 ** 18


def test_exercise_pays_in_before_out(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 3 * one)
    env.mint(a, 3 * one)
    env.into_exercise()

    q = 2 * one
    paid = env.required_in(q)
    # CEIL formula check against the spec basis
    strike = env.v("strike")
    if kind == "call":
        expected = -(-(q * strike) // UNIT_W)  # ceil
    else:
        expected = -(-(q * strike) // UNIT_U)
    assert paid == expected

    weth0 = env.weth.functions.balanceOf(env.vault.address).call()
    usdc0 = env.usdc.functions.balanceOf(env.vault.address).call()

    env.fund_strike(a, paid)
    env.exercise(a, q)

    weth1 = env.weth.functions.balanceOf(env.vault.address).call()
    usdc1 = env.usdc.functions.balanceOf(env.vault.address).call()

    if kind == "call":
        # USDC strike IN == paid, WETH collateral OUT == q
        assert usdc1 - usdc0 == paid
        assert weth0 - weth1 == q
    else:
        # WETH strike IN == paid, USDC collateral OUT == q
        assert weth1 - weth0 == paid
        assert usdc0 - usdc1 == q


def test_exercise_reverts_without_payment(make_vault, accounts, kind):
    """No strike-asset funded -> exercise reverts -> NO collateral leaves."""
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 2 * one)
    env.mint(a, 2 * one)
    env.into_exercise()

    collat_before = env.v("collat")
    vault_collat_tok_before = env.vault_collat_token_bal()
    # caller has N but zero strike asset and zero allowance for it -> must revert
    expect_revert(env.exercise, a, 1 * one)
    assert env.v("collat") == collat_before
    assert env.vault_collat_token_bal() == vault_collat_tok_before


def test_exercise_ceil_strands_in_vault(make_vault, accounts):
    """CEIL means a non-divisible strike rounds UP — vault collects >= exact, never less."""
    env = make_vault("call", strike=3001 * 10**6)  # odd strike to force rounding
    a = accounts[1]
    env.fund_collat(a, 1 * U)
    env.mint(a, 1 * U)
    env.into_exercise()
    # exercise a tiny q so q*strike/UNIT_W is fractional
    q = 333  # wei of WETH
    paid = env.required_in(q)
    exact = (q * 3001 * 10**6) / 10**18
    assert paid >= exact  # CEIL never undercollects
    assert paid == -(-(q * 3001 * 10**6) // 10**18)
