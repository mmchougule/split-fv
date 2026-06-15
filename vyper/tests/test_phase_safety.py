"""
T_PhaseSafety — each transition is callable ONLY in its phase; out-of-phase reverts.

Phases (SPEC §3):
  MINT_REDEEM : !settled and now <  maturity            -> mint, redeemPair
  EXERCISE    : !settled and maturity <= now < end      -> exercise (settle allowed once now>=maturity)
  SETTLED     : settled                                 -> redeemP, claimW, claimU

We assert every transition reverts outside its phase, for call AND put.
"""
from conftest import expect_revert

U = 10 ** 18


def test_mint_redeem_only_before_maturity(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 5 * one)
    env.mint(a, 2 * one)  # ok in MINT_REDEEM

    # move into EXERCISE: mint and redeemPair must revert
    env.into_exercise()
    expect_revert(env.mint, a, 1 * one)
    expect_revert(env.redeemPair, a, 1 * one)

    # after settle (SETTLED): still revert
    env.settle()
    expect_revert(env.mint, a, 1 * one)
    expect_revert(env.redeemPair, a, 1 * one)


def test_exercise_only_in_window(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 5 * one)
    env.mint(a, 5 * one)

    # before maturity: exercise reverts
    paid = env.required_in(1 * one)
    env.fund_strike(a, 10 * paid)
    expect_revert(env.exercise, a, 1 * one)

    # in window: ok
    env.into_exercise()
    env.exercise(a, 1 * one)

    # past exerciseEnd: exercise reverts (still !settled but now >= end)
    env.past_exercise_end()
    expect_revert(env.exercise, a, 1 * one)


def test_settle_requires_exercise_end_and_once(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 2 * one)
    env.mint(a, 2 * one)
    # Call the contract DIRECTLY (env.settle() auto-advances time). settle is gated to AFTER the
    # exercise window, so it reverts both before maturity AND during the window — it can never
    # preempt an in-window exercise.
    expect_revert(env.vault.settle)   # before maturity
    env.into_exercise()
    expect_revert(env.vault.settle)   # during the exercise window — no settle-preemption
    env.past_exercise_end()
    env.vault.settle()                # ok once, only after exerciseEnd
    expect_revert(env.vault.settle)   # second settle reverts ("settled")


def test_settled_transitions_blocked_pre_settlement(make_vault, accounts, kind):
    env = make_vault(kind)
    a = accounts[1]
    one = U if kind == "call" else 10 ** 6
    env.fund_collat(a, 3 * one)
    env.mint(a, 3 * one)
    # redeemP / claim before settlement: revert
    expect_revert(env.redeemP, a, 1 * one)
    expect_revert(env.claimW, a)
    expect_revert(env.claimU, a)
    # in exercise phase, still not settled: revert
    env.into_exercise()
    expect_revert(env.redeemP, a, 1 * one)
    expect_revert(env.claimW, a)
    expect_revert(env.claimU, a)
    # after settle: redeemP ok
    env.settle()
    env.redeemP(a, 3 * one)
