# Theorem Map — one row per safety theorem, traced across every layer

Definition of done: every row fully linked, every cell green. (✅ proved/green · 🟡 stub/partial · ⬜ todo · ❌ known-fail — see note)

> UPDATE 2026-06-12 (integration pass): the shipped `src/PutVault.sol` NOW implements SETTLEMENT_SPEC §6's
> `residualRecipient` terminal rule (constructor takes `_residualRecipient`; `settle()` credits the entire
> frozen residual to it when `pSupplyAt == 0`; `redeemP` has an explicit `pSupplyAt > 0` guard). The prior
> ❌ put-ResidualLiveness defect is therefore CLOSED for the PUT vault: the Foundry put invariant now
> verifies the residual is fully claimable by the recipient (256×64 calls, green). The CALL vault
> (`src/SplitVault.sol`) has NO residualRecipient and still relies on its exact 1:1 WETH `redeemPair`
> leaving empty pools — genuinely live for honest transitions, but a STRAY donation to the call vault
> would strand (documented in `ResidualLivenessWitness.t.sol::test_residualLiveness_GAP_...`).
> Certora cloud verdicts (SAT/UNSAT per rule) are STILL NOT obtained — no CERTORAKEY in this environment;
> those cells remain 🟡 (typechecks only) and the Certora `no_stranded_*` rule should be re-pointed at the
> now-fixed put once a key is available.

> SCOPE OF THE NAMES (the precise content is each theorem's statement + docstring, not the short label):
> `T_Conservation` is **claim-ledger consistency** — on a claim, the holdings drop equals the credit drop
> to the wei and credits never rise without backing; it is not a single global conservation equation over
> deposits/withdrawals. `T_RoundingMonotone`'s strike leg is modeled at denominator 1 (the 6dp-USDC /
> 18dp-WETH decimal scaling is abstracted away); the substantive content is the FLOOR-out share leg.
> `T_OracleIndependence` is a **model-level** non-interference fact (call + put: settlement factors
> through no external world); the deployed-bytecode obligation is the separate Halmos canary + static
> call-target pass. `T_ClaimNoDouble` is the **aggregate-ledger** form (per-address credit reuse is
> checked against the shipped Solidity, not in the Lean model).

| Theorem | Lean lemma | Vyper test | Foundry invariant | Halmos check | Certora rule |
|---|---|---|---|---|---|
| T_Backing | `Split.T_Backing` ✅ (call+put; axioms=propext,Quot.sound) | `test_backing` ✅ (call+put) | `invariant_T_Backing` ✅ (call+put) | `check_T_Backing_mint`/`_exercise` ✅ call · `check_T_Backing_mint_put` ✅ put (q<2³²) | `credits_le_holdings_weth`/`_usdc` 🟡 (typechecks; needs key to verify) |
| T_Conservation | `Split.T_Conservation` ✅ (call+put) | `test_conservation` ✅ (call+put) | `invariant_T_Conservation` ✅ (call+put) | `check_T_Conservation_mint`/`_redeemPair` ✅ call · `check_T_Conservation_mint_put` ✅ put | `conservation` ⬜ |
| T_ExercisePays | `Split.T_ExercisePays` ✅ (call+put) | `test_exercise_pays` ✅ (call+put) | `invariant_T_ExercisePays` ✅ (call+put) | `check_T_ExercisePays` ✅ call · `check_T_ExercisePays_put` ✅ put (q<2³²) | — |
| T_ResidualBound | `Split.T_ResidualBound` ✅ (call+put) | `test_residual_bound` ✅ (call+put) | `invariant_T_ResidualBound` ✅ (call+put) | `check_T_ResidualBound` ✅ call · `check_T_ResidualBound_put` ✅ put (q<2³²) | `residual_le_pool_weth`/`_usdc` 🟡 (typechecks; needs key to verify) |
| T_RoundingMonotone | `Split.T_RoundingMonotone` ✅ (call+put) | `test_rounding` ✅ (call+put) | `invariant_T_RoundingMonotone` ✅ (call+put) | `check_T_RoundingMonotone` ✅ call · `check_T_RoundingMonotone_put` ✅ put (q<2³²) | — |
| T_PhaseSafety | `Split.T_PhaseSafety_*` ✅ (call+put, all 6 transitions) | `test_phase_safety` ✅ (call+put) | `invariant_T_PhaseSafety` ✅ (call+put) | `check_T_PhaseSafety_*` ✅ call (4 reverts) · `_put` ✅ put (2 reverts) | — |
| T_OracleIndependence | `Split.T_OracleIndependence` ✅ (non-interference: `∀ w₁ w₂, applyIn w₁ s st = applyIn w₂ s st` over an arbitrary external `World` of prices/oracle answers/DEX reserves) | n/a | n/a | `check_T_OracleIndependence` ✅ (call) · `_put` ✅ — symbolic-storage + `createCalldata` over every selector, OracleCanary never touched; companion static-bytecode proof `oracle_independence_static.py` ✅ | — |
| T_ClaimNoDouble | `Split.T_ClaimNoDouble` ✅ (call+put) | `test_no_double_claim` ✅ (call+put) | `invariant_T_ClaimNoDouble` ✅ (call+put) | `check_T_ClaimNoDouble` ✅ call · `_put` ✅ put | `claim_zeroes_credit_*` + `no_double_claim_*` 🟡 (typechecks; needs key to verify) |
| T_PutSymmetry | `Split.Put.T_PutSymmetry` ✅ + full put suite (axioms=propext,Quot.sound) | put property tests ✅ (`test_put_reference` stateful + put params) | put invariants ✅ 8/8 (PutVaultConformanceTest; ResidualLiveness now GREEN — §6 fix landed) | all `check_*_put` ✅ (8/8 in `PutVaultSymbolic.t.sol`) | `PutVault.spec` (all put rules) 🟡 (typechecks; needs key to verify) |
| T_ResidualLiveness | `Split.T_ResidualLiveness` ✅ (call+put, axiom-clean; canonical statement is the dimensionally-correct bounded-dust form, proved via `T_ResidualLiveness_sound`) | `test_residual_liveness` ✅ (call+put; incl §6 recipient path) | `invariant_T_ResidualLiveness` ✅ call+put (put §6 fix LANDED in shipped code — recipient gets full residual) | n/a (liveness/reachability — not single-selector symbolic; covered by Foundry stateful + Certora) | `no_stranded_residualLiveness_SPEC_v6` 🟡 (put §6 fix has LANDED in shipped code, so this rule should now hold for PutVault — but the cloud verdict is unobtained, no CERTORAKEY; re-point + run to confirm UNSAT. Call vault still has no recipient.) · `no_stranded_currentImpl_safety` 🟡 (safety-only fact code does satisfy) |

The Lean column is the proof source of truth. Foundry/Halmos/Certora verify the SHIPPED Solidity behaves the
same. Vyper is the readable reference. A theorem is DONE only when its whole row is green.

> **Halmos note (`conformance/halmos/`):** `halmos` (with the pinned `halmos.toml`: solver=z3,
> 90s/assertion) is **GREEN — 25/25 symbolic checks pass** across `SplitVaultSymbolic.t.sol` (12),
> `PutVaultSymbolic.t.sol` (8), `OracleIndependence.t.sol` (2 symbolic) + the static `oracle_independence_static.py`.
> These are SYMBOLIC (not fuzz): inputs are `svm.createUint256` symbols, so a pass = property holds for EVERY
> value in the stated bound. **Symbolic bounds:** the nonlinear-multiplication checks (the CEIL/FLOOR
> `q*strike` facts: RoundingMonotone, ExercisePays, ResidualBound, Backing-mint) bound the symbolic amount to
> `q < 2³²`. This is a **solver-tractability limit, not a soundness assumption** — full 256-bit nonlinear
> bitvector reasoning is SMT-intractable (yices AND z3 both TIMEOUT at 2⁴⁸–2⁹⁶ even at 120s; verified). The
> CEIL/FLOOR identities are scale-free, so a 2³²-wide symbolic `q` (≫ any real position) is a faithful
> witness; the UNBOUNDED statements are discharged in the Lean track and the aggregate Σ-bounds in Certora.
> Each bound is documented inline in its test with a "SYMBOLIC DOMAIN (bound)" comment. The
> `ResidualBound` checks assert the SAFETY form `credit <= pool` + the single-division share identity
> (not the re-multiplied `credit*pAt <= pool*qr`, which is the SMT-intractable redundant restatement of EVM
> FLOOR division). Each phase/claim/oracle check is FULLY unbounded (no `q<2³²`) — only the nonlinear-product
> ones carry the bound. Reproduce: `cd conformance/halmos && forge build && halmos` (+ `python3 oracle_independence_static.py`).

> **Foundry note (`conformance/foundry/`):** stateful invariants run against the SHIPPED
> `src/SplitVault.sol` / `src/PutVault.sol` (symlinked), 256 runs × depth 64 = 16,384 calls per invariant.
> **Call vault: 8/8 green** — incl. a NON-VACUOUS `T_ResidualLiveness`: the directed `hDrainAllThenSettle`
> driver provably reaches the `pSupplyAt==0` settled state (verified with an expected-to-fail reachability
> probe) and the call vault's exact 1:1 WETH `redeemPair` strands nothing.
> **Put vault: 8/8 green (as of 2026-06-12).** The shipped `PutVault` now implements the SETTLEMENT_SPEC §6
> `residualRecipient` terminal rule, so the prior mint→redeemPair ceil-dust no longer strands: when
> `settle()` runs with `pSupplyAt==0` the entire frozen residual is credited to the immutable recipient.
> `invariant_T_ResidualLiveness` was rewritten from the old RED known-fail to verify the TRUE §6 property
> (`claimableUsdc/Weth[recipient] == usdcPool/wethPool`) and is GREEN across 16,384 calls. Constructor call
> sites in the test suite were updated to the new 6-arg signature. Witness/characterization in
> `foundry/test/ResidualLivenessWitness.t.sol`; its GAP test still documents that a STRAY donation to the
> CALL vault (which has no recipient) strands — that remains true.
> Full tally: `forge test` = 18/18 tests pass (8 call invariants + 8 put invariants + 2 witness).
