"""
T_Conservation — no debt minted, no overpay.

For every transition, the change in the vault's *token* holdings equals the value that
actually crossed the user<->vault boundary (no value created or destroyed). We assert this
by checking the ERC20 ledger deltas against the vault's internal accounting deltas around
each transition, for call AND put.
"""
U = 10 ** 18


def _snap(env):
    return {
        "v_collat_tok": env.vault_collat_token_bal(),
        "v_strike_tok": env.vault_strike_token_bal(),
        "collat": env.v("collat"),
        "strikeBal": env.v("strikeBal"),
    }


def test_conservation(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6

    # --- mint: collateral token IN by q, internal collat up by q ---
    env.fund_collat(a, 4 * one)
    s0 = _snap(env)
    env.mint(a, 4 * one)
    s1 = _snap(env)
    assert s1["v_collat_tok"] - s0["v_collat_tok"] == 4 * one
    assert s1["collat"] - s0["collat"] == 4 * one
    # internal accounting never diverges from real token holdings (no phantom value)
    assert s1["v_collat_tok"] == s1["collat"]

    # --- redeemPair: collateral token OUT by q == internal collat down by q ---
    s0 = _snap(env)
    env.redeemPair(a, 1 * one)
    s1 = _snap(env)
    assert s0["v_collat_tok"] - s1["v_collat_tok"] == 1 * one
    assert s0["collat"] - s1["collat"] == 1 * one

    # --- exercise: strike token IN == paid; collateral token OUT == q ---
    env.into_exercise()
    paid = env.required_in(1 * one)
    env.fund_strike(a, paid)
    s0 = _snap(env)
    env.exercise(a, 1 * one)
    s1 = _snap(env)
    assert s1["v_strike_tok"] - s0["v_strike_tok"] == paid
    assert s1["strikeBal"] - s0["strikeBal"] == paid
    assert s0["v_collat_tok"] - s1["v_collat_tok"] == 1 * one
    assert s0["collat"] - s1["collat"] == 1 * one

    # --- settle: NO token movement (snapshot only) ---
    s0 = _snap(env)
    env.settle()
    s1 = _snap(env)
    assert s1["v_collat_tok"] == s0["v_collat_tok"]
    assert s1["v_strike_tok"] == s0["v_strike_tok"]
    assert s1["collat"] == s0["collat"] and s1["strikeBal"] == s0["strikeBal"]

    # --- redeemP: NO token movement (only credits) ---
    s0 = _snap(env)
    env.redeemP(a, 3 * one)  # remaining P
    s1 = _snap(env)
    assert s1["v_collat_tok"] == s0["v_collat_tok"]
    assert s1["v_strike_tok"] == s0["v_strike_tok"]

    # --- claims: token OUT exactly equals credited amount; internal == real after ---
    # claimW always moves WETH; claimU always moves USDC (both vaults).
    cw = env.v("claimableW", a)  # WETH credit
    cu = env.v("claimableU", a)  # USDC credit
    weth0 = env.weth.balanceOf(env.vault.address)
    usdc0 = env.usdc.balanceOf(env.vault.address)
    env.claimW(a)
    env.claimU(a)
    weth1 = env.weth.balanceOf(env.vault.address)
    usdc1 = env.usdc.balanceOf(env.vault.address)
    assert weth0 - weth1 == cw
    assert usdc0 - usdc1 == cu
    # whatever stays in the vault is fully backed by real tokens (no overpay)
    assert env.vault_collat_token_bal() >= env.v("collat")
    assert env.vault_strike_token_bal() >= env.v("strikeBal")
