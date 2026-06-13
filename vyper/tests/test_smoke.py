"""Lifecycle smoke test (not a theorem): mint -> exercise -> settle -> redeemP -> claim."""


def test_full_lifecycle_call(make_vault, accounts):
    env = make_vault("call")
    alice, bob = accounts[1], accounts[2]
    # alice mints 2 WETH worth
    env.fund_collat(alice, 2 * 10**18)
    env.mint(alice, 2 * 10**18)
    assert env.v("collat") == 2 * 10**18
    assert env.v("pSupply") == 2 * 10**18 and env.v("nSupply") == 2 * 10**18
    # move into exercise; bob (give him N) exercises 1 WETH
    env.vault.functions  # noqa
    # transfer 1 N from alice to bob via redeemPair path is not modeled; instead alice exercises
    env.into_exercise()
    paid = env.required_in(1 * 10**18)  # = 3000 USDC
    assert paid == 3000 * 10**6
    env.fund_strike(alice, paid)
    env.exercise(alice, 1 * 10**18)
    assert env.v("collat") == 1 * 10**18           # 1 WETH left
    assert env.v("strikeBal") == paid              # 3000 USDC in
    assert env.v("nSupply") == 1 * 10**18          # one N burned
    # settle
    env.settle()
    assert env.v("settled") is True
    assert env.v("pSupplyAt") == 2 * 10**18
    assert env.v("collatAt") == 1 * 10**18
    assert env.v("strikeAt") == paid
    # alice redeems all P (2e18 of 2e18) -> gets all residual credited
    env.redeemP(alice, 2 * 10**18)
    assert env.v("claimableW", alice) == 1 * 10**18
    assert env.v("claimableU", alice) == paid
    # claim
    env.claimW(alice)
    env.claimU(alice)
    assert env.v("collat") == 0 and env.v("strikeBal") == 0
    # alice got 1 WETH from exercise + 1 WETH from claimW = 2 WETH back (all she put in).
    assert env.collat_bal_of(alice) == 2 * 10**18
    # she paid 3000 USDC in exercise, got it all back via claimU.
    assert env.strike_bal_of(alice) == paid
