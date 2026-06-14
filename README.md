# split-fv — Machine-Checked Safety for Split's Settlement Core

Split is an **oracle-free, physically-settled** options primitive. It turns collateral into two tradable
claims (P and N); traders take leverage with fixed downside; LPs take the other side. **Settlement reads
no ETH/USD price** — so settlement safety is an *accounting theorem*, not a price theorem.

> **The one-sentence thesis.** For every valid lifecycle path, claims can never redeem more than the vault
> holds, exercise can never underpay the strike, residual redemption can never overdraw the frozen pool,
> rounding can only strand bounded dust (never drain), and **no settlement transition reads an ETH/USD
> price**. We prove this in Lean (the source of truth), implement a readable Vyper reference, and show the
> shipped Solidity conforms to the same invariants.

This repo is the machine-checked argument that the settlement core is safe:

```
math spec ─▶ Lean proof (truth) ─▶ Vyper reference ─▶ Solidity conformance ─▶ Certora / audit
```

The price-manipulation drain vector — the most common one in DeFi options/lending — is removed **by
construction, not by assumption**: there is no price parameter in the settlement surface to manipulate. That
structural fact (**T_OracleIndependence**) is the property to check first; everything else is standard
accounting once it holds. See [`docs/THREAT_MODEL.md`](docs/THREAT_MODEL.md).

## What we prove (call AND put vaults)
Claims can never redeem more than the vault holds (**Backing**), value is conserved (**Conservation**),
exercise can never take collateral without paying the strike (**ExercisePays**), residual redemption can
never overdraw the frozen pool (**ResidualBound**), rounding can only strand bounded dust never drain
(**RoundingMonotone**), transitions are phase-gated (**PhaseSafety**), **no settlement transition reads a
price/oracle/DEX** (**OracleIndependence**, structural), claims can't double-spend (**ClaimNoDouble**), the
put vault proves all of the above with roles swapped (**PutSymmetry**), and after settlement no vault asset
is ever permanently stranded (**ResidualLiveness**).

## How to read this repo (reviewer path)
1. [`docs/SETTLEMENT_SPEC.md`](docs/SETTLEMENT_SPEC.md) — the frozen math model: state fields, the six
   transitions, the residual-liveness terminal rule. Every other layer maps to these exact names.
2. [`docs/SAFETY_THEOREMS.md`](docs/SAFETY_THEOREMS.md) — the ten theorems in plain English, each with a
   pointer to its formal Lean statement.
3. [`docs/ASSUMPTIONS_AND_BOUNDARY.md`](docs/ASSUMPTIONS_AND_BOUNDARY.md) — what the proofs trust, and what is
   explicitly out of scope.
4. [`docs/THREAT_MODEL.md`](docs/THREAT_MODEL.md) — the attacker, the attack→defense map, and what is *not*
   defended (pricing, keeper, MEV, facilitator).
5. [`lean/Split/`](lean/Split/) — the proofs themselves (source of truth). Then
   [`conformance/THEOREM_MAP.md`](conformance/THEOREM_MAP.md) — one row per theorem, traced across Lean →
   Vyper → Foundry → Halmos → Certora.

## How to verify (3 commands)
```bash
( cd lean && lake build )                 # Lean proofs — must be green, zero `sorry`
( cd vyper && pip install vyper && python -m pytest tests )   # reference impl + property tests
( cd conformance/foundry && forge test )  # shipped-Solidity conformance invariants
```
CI runs all of this on every push: [`.github/workflows/fv.yml`](.github/workflows/fv.yml). These are the
acceptance commands; the green bar (zero `sorry`, all tests/invariants passing) is the **definition of done**
— see the Status section below for what is and isn't there yet.

## Honest scope
**In scope:** the settlement core (mint, redeemPair, exercise, settle, redeemP, claim) for call and put.
**Out of scope (separate safety story):** pricing/quote signer, keeper, wrappers, routing, the gasless
facilitator/paymaster, LP pool economics. "Oracle-free" means *settlement* reads no price; *pricing* uses
an off-chain signed quote. We never claim otherwise.

## Status (honest)
**Lean: green, zero proof-position `sorry`.** Every one of the ten safety theorems is proved over all
reachable states for **both** the call and put vaults, depending only on `propext`/`Quot.sound`
(`#print axioms` is clean — no `sorryAx`). The Vyper reference compiles and passes its property tests; the
Solidity conformance suite (Foundry stateful invariants + Halmos symbolic checks) maps one-to-one to the
theorem names. `conformance/THEOREM_MAP.md` is the per-theorem scoreboard.

**What is NOT yet done, stated plainly:**
- **Certora**: the specs typecheck, but no cloud verdict has been obtained (requires a prover key). Those
  cells are marked 🟡 (typecheck-only), not ✅.
- **Halmos nonlinear bound**: the CEIL/FLOOR `q·strike` checks are bounded to `q < 2³²` for SMT tractability
  (a solver limit, not a soundness assumption); the unbounded forms live in the Lean track.
- **Call-vault residual policy**: the put vault implements the SETTLEMENT_SPEC §6 `residualRecipient`
  terminal rule; the call vault relies on its exact 1:1 `redeemPair` emptying the pools and documents the
  stray-donation edge as a known non-goal (`conformance/foundry/test/ResidualLivenessWitness.t.sol`).
- **Not third-party audited.** This repo is a machine-checked *settlement-core safety* argument, not an audit
  and not a TVL claim.

We do not claim full formal verification of anything outside the settlement core (see **Honest scope** above).
