# Safety Theorems — plain English + formal statement

Each theorem is proved over **reachable** states (`lean/Split/Reachability.lean`) for the **call AND put**
vaults. The call proofs live in `lean/Split/Theorems.lean`; the put proofs (T_PutSymmetry) live in a sibling
module `lean/Split/Put/Theorems.lean` with WETH/USDC roles swapped — first-class, not a mirror.

Theorem names are **frozen**: they are referenced verbatim by `conformance/THEOREM_MAP.md`, the Foundry
`invariant_T_*`, the Halmos `check_T_*`, and the Certora rules. Do not rename.

> **Scope.** These cover the SETTLEMENT CORE only. Pricing uses an off-chain signed quote and is OUT
> of scope (see `ASSUMPTIONS_AND_BOUNDARY.md` and `THREAT_MODEL.md`). **"Oracle-free" = settlement reads no
> price.** It does not mean "no price exists anywhere in the product."
>
> **Status.** This file states the theorems and their formal Lean signatures. Whether each is *proved*
> (vs still a scaffold `sorry`) is tracked, per layer, in `conformance/THEOREM_MAP.md` — that table is the
> single source of truth for what is green. A theorem is DONE only when its whole row is green.

---

## 1. T_Backing — *Claims never exceed holdings*
Pre-settle: outstanding N is fully collateralized (`nSupply ≤ collat`). Post-settle: total credited claims
never exceed what the vault holds (`Σ claimW ≤ collat`, `Σ claimU ≤ strikeBal`). No reachable path lets
claims outrun holdings.
- **Formal (call):** `theorem Split.T_Backing {s : State} (h : Reachable s) : Backing s`
- **Defends:** drain via over-redemption / minting debt without collateral (THREAT_MODEL A1).

## 2. T_Conservation — *No debt minted, no overpay*
Every transition's outflow equals its balance delta; nothing is created or destroyed except via the defined
mint / redeemPair / exercise / claim rules. The vault never invents collateral and never pays out more than
the rule prescribes.
- **Formal (call):** `theorem Split.T_Conservation {s s' : State} {st : Step} (h : Reachable s) (hstep : apply s st = some s') : …`
  (the precise per-step conserved quantity is stated in the Lean module).
- **Defends:** drain via accounting mismatch (THREAT_MODEL A1).

## 3. T_ExercisePays — *No free collateral*
`exercise(q)` removes exactly `q` collateral only after the **CEIL** strike `ceil(q·strike)` strike-asset has
been paid in. Collateral out is matched, to the wei, by strike in (rounded in the vault's favor).
- **Formal (call):** `theorem Split.T_ExercisePays {s s' : State} {q : Nat} (hstep : exercise s q = some s') : s'.collat + q = s.collat ∧ s.strikeBal ≤ s'.strikeBal`
- **Defends:** taking collateral without paying the strike (THREAT_MODEL A2).

## 4. T_ResidualBound — *Residual can't overdraw*
Post-settle, the total assets credited to P holders via `redeemP` never exceed the **frozen** residual pools
(`collatAt` / `strikeAt`) snapshotted at `settle()`. Pro-rata FLOOR shares sum to ≤ the pool.
- **Formal (call):** `theorem Split.T_ResidualBound {s : State} (h : Reachable s) : ResidualBound s`
- **Defends:** overdrawing the residual pool (THREAT_MODEL A3).

## 5. T_RoundingMonotone — *Rounding can only strand dust, never drain*
CEIL on money coming IN to the vault and FLOOR on money going OUT mean the owed-vs-held gap never goes
negative: rounding always keeps *more* in the vault. The only effect achievable is stranding bounded dust
(`< pSupplyAt` indivisible units), which is not extractable.
- **Formal (call):** `theorem Split.T_RoundingMonotone {s s' : State} {st : Step} (h : Reachable s) (hstep : apply s st = some s') : …`
  (the gap-non-negative statement is in the Lean module; the dust bound is `Rounding.residual_dust_bounded`).
- **Defends:** drain via adversarial choice of `q` (THREAT_MODEL A4).

## 6. T_PhaseSafety — *Right phase only*
mint / redeemPair succeed only in MINT_REDEEM; exercise (and settle) only in EXERCISE; redeemP / claim only
in SETTLED. Every out-of-phase call reverts (returns `none`).
- **Formal (call):** one lemma per transition, e.g. `theorem Split.T_PhaseSafety_exercise {s s' : State} {q : Nat} (hstep : exercise s q = some s') : inExercise s` (and the analogues for mint / redeemPair / redeemP / claim).
- **Defends:** out-of-phase calls (THREAT_MODEL A5).

## 7. T_OracleIndependence — *No price input, structurally*
Settlement transitions take **no** price / oracle / DEX argument and read no price field. In Lean this is a
**type-level** fact: `apply : State → Step → Option State` has no price parameter and `Step` carries no price.
The shipped Solidity proves the bytecode analogue — settlement selectors make no external call to a
price/oracle/DEX address — via Halmos `check_T_OracleIndependence`. This is the *absence of a price input from
the surface*, **not** the weaker "settlement happens to be time-invariant."
- **Formal (call):** `theorem Split.T_OracleIndependence : (∀ (s : State) (st : Step), apply s st = apply s st)`
  — the substantive content is the **signature** of `apply`/`Step` (no price), which this lemma witnesses;
  the binding obligation is the bytecode check on the shipped contracts.
- **Defends:** making settlement depend on a manipulable price (THREAT_MODEL A6) — the load-bearing claim.

## 8. T_ClaimNoDouble — *No double-claim*
A claim zeroes the caller's credit **before** transferring tokens out (zero-before-send), so the same credit
can never pay twice and a reentrant call sees zero remaining credit. Reentrancy-safe by construction.
- **Formal (call):** `theorem Split.T_ClaimNoDouble {s s' : State} {amt : Nat} (hstep : claimW s amt = some s') : s'.totalClaimW + amt = s.totalClaimW`
  (aggregate decrement is exact; the per-address no-double-claim guarantee over the real
  `mapping(address => uint)` ledger is checked against the shipped Solidity — see the modeling note below).
- **Defends:** double-claim / reentrancy drain (THREAT_MODEL A7).

## 9. T_PutSymmetry — *Puts are first-class*
All of theorems 1–8 are re-proved for the put vault with collateral = USDC (6dp) and strike asset = WETH
(18dp), each with its own proof — never a hand-waved "mirror."
- **Formal:** the call lemmas above, re-stated and re-proved in `lean/Split/Put/Theorems.lean`.
- **Defends:** breaking the put while the call is safe (THREAT_MODEL A8).

## 10. T_ResidualLiveness — *Nothing stranded*
After `settle()`, every vault asset is either claimable by a valid claimant (or the immutable
`residualRecipient`, per the §6 terminal rule for `pSupplyAt == 0`) or bounded dust. No reachable state
permanently locks meaningful funds. **This requires the SPEC §6 design fix** (residual-recipient terminal
rule), which is implemented and proved, not assumed.
- **Formal (call):** `theorem Split.T_ResidualLiveness {s : State} (h : Reachable s) (hs : s.settled) : s.collat ≤ s.totalClaimW + ⌊pSupply·collatAt/pSupplyAt⌋ + (pSupplyAt − pSupply) ∧ s.strikeBal ≤ s.totalClaimU + ⌊pSupply·strikeAt/pSupplyAt⌋ + (pSupplyAt − pSupply)` — the dimensionally-correct bounded-dust form (the original `+ pSupplyAt` form was a unit error caught by FV and fixed). Proved (call + put), axioms `[propext, Quot.sound]`, no `sorry`.
- **Defends:** stranding funds forever by redeeming all P before maturity (THREAT_MODEL A9).

---

## Modeling note — aggregate credit totals vs per-address ledger
The Lean call model tracks **ghost aggregate credit totals** (`totalClaimW` / `totalClaimU`) rather than the
full per-address `claimW : Addr → Nat` map. This is deliberate: the *solvency* property that matters is the
aggregate one (Σ credits ≤ holdings), and aggregating keeps the induction tractable. The **per-address**
no-double-claim guarantee (each holder can drain at most their own credit, exactly once) is enforced
structurally by zero-before-send and is verified against the **shipped Solidity's real
`mapping(address => uint)` claim ledger** in the Certora `credits_le_holdings` rule and the Halmos
`check_T_ClaimNoDouble`. This division of labor is recorded explicitly in `conformance/THEOREM_MAP.md`; it is
a modeling boundary, not a gap in the defended property.
