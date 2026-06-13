# split-fv — status

Honest, one-screen snapshot of what is verified and what is not. The per-theorem matrix is
`conformance/THEOREM_MAP.md`; the public summary is in `README.md`.

## Verified (green)

- **Lean (proof source of truth).** All ten safety theorems are proved over every reachable state for
  **both** the call and put vaults, depending only on `propext`/`Quot.sound`. `#print axioms` is clean —
  no `sorryAx`, no proof-position `sorry`. Residual-liveness uses the dimensionally-correct bounded-dust
  form (`+ ⌊pSupply·Xat/pSupplyAt⌋ + (pSupplyAt − pSupply)`).
- **Vyper (readable reference).** `SplitVaultReference.vy` and `PutVaultReference.vy` compile (vyper 0.4.3)
  and pass their property tests.
- **Foundry (stateful conformance vs the in-repo settlement contracts).** Call and put invariants pass,
  each mapped one-to-one to a theorem name.
- **Halmos (symbolic).** Per-selector symbolic checks pass, including the oracle-independence canary.

## Not done — stated plainly

1. **Certora**: specs typecheck only; no cloud verdict has been obtained (needs a prover key). Marked 🟡 in
   the theorem map, not ✅.
2. **Halmos nonlinear bound**: the CEIL/FLOOR `q·strike` checks are bounded to `q < 2³²` for SMT
   tractability — a solver limit, not a soundness assumption. The unbounded forms are discharged in Lean.
3. **Call-vault residual policy**: the put vault implements the SETTLEMENT_SPEC §6 `residualRecipient`
   terminal rule. The call vault relies on its exact 1:1 `redeemPair` leaving empty pools and documents the
   stray-donation edge as a known non-goal (`conformance/foundry/test/ResidualLivenessWitness.t.sol`).
4. **Not third-party audited.** This is a settlement-core safety argument, not an audit and not a TVL claim.

## Reproduce

```sh
# 1. Lean proofs (source of truth) — must build, zero proof-position sorry
( cd lean && lake build )

# 2. Vyper reference + property tests
( cd vyper && pip install vyper pytest eth-tester web3 && \
    vyper SplitVaultReference.vy && vyper PutVaultReference.vy && python -m pytest tests -q )

# 3. Foundry stateful conformance
( cd conformance/foundry && forge test )

# 4. Halmos symbolic checks
( cd conformance/halmos && forge build && halmos )
```
