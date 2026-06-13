"""
T_RoundingMonotone — rounding can only strand dust, never drain.

CEIL on incoming strike + FLOOR on outgoing residual => the vault's holdings are never
reduced below what is owed; stranded dust after everyone redeems is bounded and stays IN
the vault (claimable by the residual-recipient terminal rule would not apply here since
pSupplyAt>0, but the dust is provably < pSupplyAt units per asset and remains in the vault).

We construct a deliberately non-divisible split and assert:
  - Σ FLOOR credits <= basis  (no drain)
  - basis - Σ credits  < number of redeeming P units (bounded dust)
  - exercise CEIL collected >= exact owed (no undercollect)
Call AND put.
"""
U = 10 ** 18


def test_floor_out_strands_bounded_dust(make_vault, accounts, kind):
    env = make_vault(kind)
    one = U if kind == "call" else 10 ** 6
    # 3 holders with coprime-ish shares so pro-rata floors leave dust
    shares = [1 * one, 1 * one, 1 * one]
    holders = accounts[1:4]
    for h, amt in zip(holders, shares):
        env.fund_collat(h, amt)
        env.mint(h, amt)

    # exercise an odd amount so strikeAt is not divisible by pSupplyAt
    env.into_exercise()
    paid = env.required_in(1 * one)
    env.fund_strike(holders[0], paid)
    env.exercise(holders[0], 1 * one)

    env.settle()
    collatAt = env.v("collatAt")
    strikeAt = env.v("strikeAt")
    pSupplyAt = env.v("pSupplyAt")

    for h, amt in zip(holders, shares):
        env.redeemP(h, amt)

    total_w = env.v("totalClaimW")  # WETH credits
    total_u = env.v("totalClaimU")  # USDC credits
    # frame-correct bases (WETH vs USDC)
    weth_basis = collatAt if kind == "call" else strikeAt
    usdc_basis = strikeAt if kind == "call" else collatAt

    # NO DRAIN: floor sums never exceed the basis
    assert total_w <= weth_basis
    assert total_u <= usdc_basis

    # BOUNDED DUST: with all P redeemed across k holders, each FLOOR strands < 1 unit of the
    # divided asset, so total stranded dust per asset is < k (the number of redeem calls).
    k = len(holders)
    dust_w = weth_basis - total_w
    dust_u = usdc_basis - total_u
    assert dust_w < k
    assert dust_u < k

    # dust physically remains IN the vault (never lost): holdings >= credits owed
    weth_held = env.v("collat") if kind == "call" else env.v("strikeBal")
    usdc_held = env.v("strikeBal") if kind == "call" else env.v("collat")
    assert weth_held - total_w >= 0
    assert usdc_held - total_u >= 0


def test_ceil_in_never_undercollects(make_vault, accounts, kind):
    env = make_vault(kind, strike=(7777 * 10**6 if kind == "call" else (U // 7)))
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 5 * one)
    env.mint(a, 5 * one)
    env.into_exercise()
    strike = env.v("strike")
    for q in [1, 3, 7, 12345, one // 3 or 1]:
        paid = env.required_in(q)
        basis = U if kind == "call" else 10**6
        exact_num = q * strike
        # CEIL: paid*basis >= exact_num  (collected value >= owed value)
        assert paid * basis >= exact_num
        # and paid is the tightest ceil: (paid-1)*basis < exact_num
        if paid > 0:
            assert (paid - 1) * basis < exact_num
