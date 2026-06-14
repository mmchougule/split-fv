# Foundry conformance — stateful invariants on the settlement-core Solidity

Verifies the settlement-core contracts (`SplitVault.sol`, `PutVault.sol`) against
the frozen settlement theorems in
[`../THEOREM_MAP.md`](../THEOREM_MAP.md) / `docs/SAFETY_THEOREMS.md`.

The contracts are referenced via symlink under `src/` (not copied), so the Foundry
and Halmos tracks verify the exact same in-repo settlement source — the repo is
self-contained and reproducible on a fresh clone:

```
src/SplitVault.sol -> ../../halmos/src/SplitVault.sol
src/PutVault.sol   -> ../../halmos/src/PutVault.sol
```

## How to run

```
forge build
forge test                         # all suites
forge test --match-contract Conformance   # just the stateful invariants
```

`foundry.toml`: `runs=256, depth=64` → 16,384 calls per invariant.
`fail_on_revert=false` because the handler deliberately probes out-of-phase calls
to prove `T_PhaseSafety` (a revert is a valid no-op step, not a property failure).

## Layout

| File | What it does |
|---|---|
| `test/SplitVaultConformance.t.sol` | CALL vault: `CallHandler` fuzzes the real transition surface (mint/redeemPair/exercise/settle/redeemP/claim* + out-of-phase probes + directed zero-P driver); `invariant_T_*` for all 8 theorems. |
| `test/PutVaultConformance.t.sol` | PUT vault (T_PutSymmetry): same 8 invariants with USDC/WETH roles swapped. |
| `test/ResidualLivenessWitness.t.sol` | Directed tests proving the `pSupplyAt==0`-at-settle state is reachable and characterizing the §6 residual rule. |
| `test/lib/`, `test/mocks/` | Dependency-free MiniTest + MockERC20 (no forge-std submodule). |

Each `invariant_<TheoremName>` matches the frozen names in `../THEOREM_MAP.md`.

## Conformance result (honest)

**Call vault: 8/8 invariants pass.** All 16,384-call runs green, including a
NON-VACUOUS `T_ResidualLiveness` — the directed `hDrainAllThenSettle` driver
provably reaches the `pSupplyAt==0` settled state (verified with an
expected-to-fail reachability probe), and the call vault's exact 1:1 WETH
redeemPair leaves the frozen pools empty, so nothing is stranded.

**Put vault: 8/8 invariants pass.** The put vault implements SETTLEMENT_SPEC §6:
its `mint` pulls `usdcRequired = ceil(amount·strike/1e18)` USDC IN (CEIL-in) while
`redeemPair` returns `usdcOut = floor(amount·strike/1e18)` USDC OUT (FLOOR-out), so
a mint→redeemPair round-trip can strand up to 1 USDC-unit of ceil dust. The §6
terminal rule closes this: at `settle()` with `pSupplyAt == 0` the entire frozen
residual is credited to an immutable `residualRecipient` (constructor arg), and
`redeemP` carries an explicit `pSupplyAt > 0` guard. `invariant_T_ResidualLiveness`
verifies the residual is therefore always fully claimable — no value is stranded.

> History (kept for honesty): an earlier revision of the shipped Solidity did **not**
> implement §6, and this suite caught it — the put `T_ResidualLiveness` invariant
> failed with a fuzzer-found minimal counterexample (`mint(…)` ceil-in vs
> `redeemPair(…)` floor-out leaving `Settled(usdcPool: 1, pSupply: 0)`, 1 unit frozen
> with no claimant). The §6 `residualRecipient` rule — already present in the Lean
> model and the Vyper reference — was then landed in the Solidity, and the invariant
> went green. The directed witness in `ResidualLivenessWitness.t.sol` still documents
> the rounding edge that the rule resolves.

`T_OracleIndependence` is structural and is handled in the Halmos track
(`check_T_OracleIndependence`); there is no Foundry invariant for it.
