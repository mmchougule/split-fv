"""
T_ClaimNoDouble — credit is zeroed before transfer => the same credit can't pay twice.

We redeemP to accrue a credit, claim once (receive tokens, credit -> 0), then assert a
second claim reverts ("nothing") and no further tokens move. This is the structural
zero-before-send property; reentrancy is additionally guarded but the accounting alone
prevents double payment. Call AND put.
"""
from conftest import expect_revert

U = 10 ** 18


def test_no_double_claim(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 4 * one)
    env.mint(a, 4 * one)
    env.into_exercise()
    paid = env.required_in(1 * one)
    env.fund_strike(a, paid)
    env.exercise(a, 1 * one)
    env.settle()
    env.redeemP(a, 4 * one)

    cw = env.v("claimableW", a)
    cu = env.v("claimableU", a)
    assert cw > 0 and cu > 0

    weth0 = env.weth.functions.balanceOf(a).call()
    usdc0 = env.usdc.functions.balanceOf(a).call()

    # first claim succeeds and zeroes the credit
    env.claimW(a)
    env.claimU(a)
    assert env.v("claimableW", a) == 0
    assert env.v("claimableU", a) == 0

    weth1 = env.weth.functions.balanceOf(a).call()
    usdc1 = env.usdc.functions.balanceOf(a).call()
    assert weth1 - weth0 == cw
    assert usdc1 - usdc0 == cu

    # second claim must revert (nothing left) — no double payment
    expect_revert(env.claimW, a)
    expect_revert(env.claimU, a)

    # balances unchanged after the failed second claims
    assert env.weth.functions.balanceOf(a).call() == weth1
    assert env.usdc.functions.balanceOf(a).call() == usdc1


def test_total_credits_decrease_exactly_once(make_vault, accounts, kind):
    """Aggregate totalClaim* drops by exactly the claimed amount, once."""
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 2 * one)
    env.mint(a, 2 * one)
    env.into_exercise()
    # exercise so BOTH WETH and USDC residuals are nonzero regardless of vault kind
    paid = env.required_in(1 * one)
    env.fund_strike(a, paid)
    env.exercise(a, 1 * one)
    env.settle()
    env.redeemP(a, 2 * one)

    tw0 = env.v("totalClaimW")
    cw = env.v("claimableW", a)
    assert cw > 0
    env.claimW(a)
    assert env.v("totalClaimW") == tw0 - cw
    # claiming again does not move totals
    expect_revert(env.claimW, a)
    assert env.v("totalClaimW") == tw0 - cw
