"""
T_ResidualBound — residual can't overdraw.

Post-settle, the total assets credited to P-holders via redeemP can never exceed the frozen
residual basis (collatAt / strikeAt). We mint with MANY holders, settle, have each redeem,
and assert Σ credits <= collatAt and <= strikeAt. Call AND put.
"""
U = 10 ** 18


def test_residual_bound(make_vault, accounts, kind):
    env = make_vault(kind)
    one = U if kind == "call" else 10 ** 6
    holders = accounts[1:5]
    amounts = [3 * one, 1 * one, 2 * one, 4 * one]  # distinct, non-divisible interplay

    for h, amt in zip(holders, amounts):
        env.fund_collat(h, amt)
        env.mint(h, amt)

    # do an exercise so strikeBal is nonzero and odd vs pSupply (rounding stress)
    env.into_exercise()
    paid = env.required_in(1 * one)
    env.fund_strike(holders[0], paid)
    env.exercise(holders[0], 1 * one)

    env.settle()
    collatAt = env.v("collatAt")
    strikeAt = env.v("strikeAt")
    pSupplyAt = env.v("pSupplyAt")
    assert pSupplyAt == sum(amounts)

    # everyone redeems all their P
    for h, amt in zip(holders, amounts):
        env.redeemP(h, amt)

    total_w = env.v("totalClaimW")  # WETH credits
    total_u = env.v("totalClaimU")  # USDC credits
    # WETH/USDC bases depend on the vault frame:
    #   call: collatAt = WETH, strikeAt = USDC
    #   put : collatAt = USDC, strikeAt = WETH
    weth_basis = collatAt if kind == "call" else strikeAt
    usdc_basis = strikeAt if kind == "call" else collatAt
    # FLOOR pro-rata => Σ credits <= frozen basis (never overdraw)
    assert total_w <= weth_basis
    assert total_u <= usdc_basis
    # and credits never exceed actual vault holdings of that asset either
    weth_held = env.v("collat") if kind == "call" else env.v("strikeBal")
    usdc_held = env.v("strikeBal") if kind == "call" else env.v("collat")
    assert total_w <= weth_held
    assert total_u <= usdc_held


def test_residual_bound_single_holder_exact(make_vault, accounts, kind):
    """Single holder of 100% of P gets exactly the whole basis (no dust lost when divisible)."""
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 10 * one)
    env.mint(a, 10 * one)
    env.into_exercise()
    paid = env.required_in(2 * one)
    env.fund_strike(a, paid)
    env.exercise(a, 2 * one)
    env.settle()
    collatAt = env.v("collatAt")
    strikeAt = env.v("strikeAt")
    env.redeemP(a, 10 * one)
    # q == pSupplyAt => floor(q*basis/q) == basis exactly.
    # claimW is the WETH credit, claimU the USDC credit:
    #   call: WETH=collateral (collatAt), USDC=strike (strikeAt)
    #   put : WETH=strike (strikeAt),     USDC=collateral (collatAt)
    if kind == "call":
        assert env.v("claimableW", a) == collatAt
        assert env.v("claimableU", a) == strikeAt
    else:
        assert env.v("claimableW", a) == strikeAt
        assert env.v("claimableU", a) == collatAt
