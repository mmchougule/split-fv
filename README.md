# split-fv — Machine-Checked Safety for Split's Settlement Core

[![fv](https://github.com/mmchougule/split-fv/actions/workflows/fv.yml/badge.svg)](https://github.com/mmchougule/split-fv/actions/workflows/fv.yml)

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

## How to read this repo
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
( cd vyper && pip install -r requirements.txt && python -m pytest tests )  # reference impl + property tests
( cd conformance/foundry && forge test )  # shipped-Solidity conformance invariants
```
CI runs all of this on every push: [`.github/workflows/fv.yml`](.github/workflows/fv.yml). These are the
acceptance commands; the green bar (zero `sorry`, all tests/invariants passing) is the **definition of done**
— see the Status section below for what is and isn't there yet.

## Scope
**In scope:** the settlement core (mint, redeemPair, exercise, settle, redeemP, claim) for call and put.
**Out of scope (separate safety story):** pricing/quote signer, keeper, wrappers, routing, the gasless
facilitator/paymaster, LP pool economics. "Oracle-free" means *settlement* reads no price; *pricing* uses
an off-chain signed quote.

## Status
**Lean: green, zero proof-position `sorry`.** Every one of the ten safety theorems is proved over all
reachable states for **both** the call and put vaults, depending only on `propext`/`Quot.sound`
(`#print axioms` is clean — no `sorryAx`). The Vyper reference compiles and passes its property tests; the
Solidity conformance suite (Foundry stateful invariants + Halmos symbolic checks) maps one-to-one to the
theorem names. `conformance/THEOREM_MAP.md` is the per-theorem scoreboard.

**What is NOT yet done:**
- **Certora**: the specs typecheck, but no cloud verdict has been obtained (requires a prover key). Those
  cells are marked 🟡 (typecheck-only), not ✅.
- **Halmos nonlinear bound**: the CEIL/FLOOR `q·strike` checks are bounded to `q < 2³²` for SMT tractability
  (a solver limit, not a soundness assumption); the unbounded forms live in the Lean track.
- **Call-vault residual policy (model↔code gap).** The Lean *model's* `settle` credits the
  all-redeemed (`pSupply == 0`) residual to a recipient, and `T_ResidualLiveness` is proved on that. The
  deployed call `SplitVault.sol` does **not** yet implement that terminal rule — it relies on `redeemPair`'s
  exact 1:1 emptying the pools for honest paths, so a residual stranded at `pSupply == 0` (e.g. a stray
  donation) is a known edge, not a covered case (`conformance/foundry/test/ResidualLivenessWitness.t.sol`).
  The put vault already implements the §6 `residualRecipient` rule; aligning the deployed call vault to it
  is the next contract change. So call `T_ResidualLiveness` is a property of the model, not (yet) of the
  deployed call contract in that edge.
- **Not third-party audited.** This repo is a machine-checked *settlement-core safety* argument, not an audit.

Formal verification covers the settlement core only (see **Scope** above).

## Roadmap — what's next (in order)
This is **alpha**: a settlement-core *model* proof plus a partial bytecode-conformance layer, not an audit
of the deployed system, and the surrounding product (LP/quote pool, exerciser, off-chain pricer) is outside
the verified scope — that is where economic risk concentrates.

1. Align the deployed **call** vault to the `residualRecipient` terminal rule (model = code; close the gap above).
2. **Scaled-decimals rounding proof** in Lean — model the real 6dp-USDC / 18dp-WETH `/1e18` scaling, not denominator-1.
3. Run **Certora** to a real verdict — the cross-holder aggregate bounds (one holder cannot drain another) currently typecheck only.
4. Restrict the vault **factory to canonical tokens** (or add balance-delta checks) so fee-on-transfer / rebasing / malicious tokens can't break backing.
5. **External audit** — settlement core + factories first, then the pool, exerciser, and EIP-712 signing paths.
6. On-chain **deposit caps** + NAV sanity bands + a timelock on the pool's pricer/owner.

Growth in deposits is gated to **lag the pool's assurance, not the proven core** — a settlement-core proof never unlocks a higher cap for the signed-NAV pool.
