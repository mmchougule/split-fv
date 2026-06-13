# Certora conformance — aggregate invariants

Certora CVL rules for the aggregate safety properties that Halmos struggles with: properties that
quantify over the WHOLE claim mapping (Σ over every holder), not a single caller. These verify the
**shipped** Solidity (`../../../src/SplitVault.sol`, `../../../src/PutVault.sol`).

## Files
- `CallVault.spec` — call vault (SplitVault.sol) aggregate rules.
- `PutVault.spec`  — put vault (PutVault.sol) aggregate rules, roles swapped (T_PutSymmetry).
- `CallVault.conf` / `PutVault.conf` — run configs (paths relative to the **splitvault repo root**).

## Rules → theorems (see ../THEOREM_MAP.md)
| Rule / invariant | Theorem |
|---|---|
| `residual_le_pool_weth` / `residual_le_pool_usdc` | T_ResidualBound (Σ credits ≤ frozen pool) |
| `credits_le_holdings_weth` / `credits_le_holdings_usdc` | T_Backing / T_ClaimNoDouble (aggregate) |
| `claim_zeroes_credit_*`, `no_double_claim_*` | T_ClaimNoDouble |
| `no_stranded_residualLiveness_SPEC_v6` | T_ResidualLiveness (FROZEN SPEC §6) — **expected FAIL, see gap** |
| `no_stranded_currentImpl_safety` | T_ResidualLiveness (weaker safety-only fact the current code satisfies) |

The Σ-over-mapping reasoning uses the standard CVL ghost-sum pattern: a `ghost mathint sumClaimW/U`
kept in sync with the credit mappings via `Sstore` hooks, plus `Sload` hooks tying single-key reads
to the running total.

## How to run
Certora needs `CERTORAKEY` (cloud prover) and `solc` 0.8.24 on PATH (aliased as `solc8.24`). From the
**splitvault repo root**:
```bash
export CERTORAKEY=<your key>
certoraRun split-fv/conformance/certora/CallVault.conf
certoraRun split-fv/conformance/certora/PutVault.conf
```

### Local validation without a key (done — green)
`certora-cli` compiles the Solidity and runs the CVL typechecker locally before any cloud upload
(needs a JDK for the typechecker). This was run and PASSES (EXIT=0, no errors) for BOTH specs:
```bash
# from splitvault repo root, with solc8.24 + a JDK on PATH:
certoraRun split-fv/conformance/certora/CallVault.conf --compilation_steps_only
certoraRun split-fv/conformance/certora/PutVault.conf  --compilation_steps_only
```
So the specs are well-formed and typecheck against the real contracts. The *verification verdict*
(SAT/UNSAT per rule) requires `CERTORAKEY` and the cloud prover, which were not available in this
environment — run the two commands above WITHOUT `--compilation_steps_only` once a key is present.

## HONEST GAP — residual liveness (do not paper over)
The shipped `SplitVault.sol` / `PutVault.sol` do **NOT** implement SETTLEMENT_SPEC §6's
`residualRecipient` terminal rule. `redeemP` divides by `pSupplyAt` with no `pSupplyAt > 0` guard, so
when all P is redeemed before maturity (`pSupplyAt == 0` at settle) the frozen residual is unreachable
(every `redeemP` reverts on division-by-zero).

Consequences, stated plainly:
- `no_stranded_residualLiveness_SPEC_v6` is written to the **frozen spec** and is therefore EXPECTED
  TO FAIL against the current Solidity. It is the conformance TARGET for the §6 fix — it is NOT
  deleted/weakened to make CI look green.
- `no_stranded_currentImpl_safety` is the weaker property the current code DOES satisfy: in the
  `pSupplyAt == 0` branch `redeemP` reverts, so no credit can be mis-created — the funds are frozen
  (liveness broken) but never over-drawn or double-credited (safety preserved).

To close the gap: add an immutable `residualRecipient` and, in `settle()`, when `pSupplyAt == 0`
credit the entire `wethPool`/`usdcPool` to it. Then `no_stranded_residualLiveness_SPEC_v6` should
verify and `no_stranded_currentImpl_safety` becomes vacuous/removable.
