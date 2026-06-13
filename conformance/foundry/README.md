# Foundry conformance — stateful invariants on the SHIPPED Solidity

Verifies the **production** contracts (`SplitVault.sol`, `PutVault.sol`) against
the frozen settlement theorems in
[`../THEOREM_MAP.md`](../THEOREM_MAP.md) / `docs/SAFETY_THEOREMS.md`.

The shipped contracts are referenced via symlink under `src/` (not copied), so
conformance always tracks the real production code:

```
src/SplitVault.sol -> ../../../src/SplitVault.sol
src/PutVault.sol   -> ../../../src/PutVault.sol
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
| `test/ResidualLivenessWitness.t.sol` | Directed tests proving the `pSupplyAt==0`-at-settle state is reachable and characterizing the §6 residual gap. |
| `test/lib/`, `test/mocks/` | Dependency-free MiniTest + MockERC20 (no forge-std submodule). |

Each `invariant_<TheoremName>` matches the frozen names in `../THEOREM_MAP.md`.

## Conformance result (honest)

**Call vault: 8/8 invariants pass.** All 16,384-call runs green, including a
NON-VACUOUS `T_ResidualLiveness` — the directed `hDrainAllThenSettle` driver
provably reaches the `pSupplyAt==0` settled state (verified with an
expected-to-fail reachability probe), and the call vault's exact 1:1 WETH
redeemPair leaves the frozen pools empty, so nothing is stranded.

**Put vault: 7/8 pass — `invariant_T_ResidualLiveness` FAILS (real defect).**
This is a genuine finding, not faked green. The shipped `PutVault`:
- `mint` pulls `usdcRequired = ceil(amount·strike/1e18)` USDC IN (CEIL-in);
- `redeemPair` returns `usdcOut = floor(amount·strike/1e18)` USDC OUT (FLOOR-out).

Every mint→redeemPair round-trip therefore strands up to 1 USDC-unit of ceil
dust in the vault. When all PutP+PutN are redeemed and `settle()` runs with
`pSupplyAt==0`, that accumulated dust is frozen with **no claimant and no
`residualRecipient`** (the shipped code does not implement SETTLEMENT_SPEC §6).
Minimal counterexample found by the fuzzer:

```
mint(327648762657031552024983)  -> usdcIn  = 982946287971095   (ceil)
redeemPair(same)                -> usdcOut = 982946287971094   (floor, -1)
settle()                        -> Settled(usdcPool: 1, pSupply: 0)  // 1 unit stranded forever
```

The call vault avoids this because its `redeemPair` returns WETH 1:1 (no
rounding). **Fix required (SETTLEMENT_SPEC §6):** at `settle()` with
`pSupplyAt==0`, credit the entire residual to an immutable `residualRecipient`.
Once the shipped `PutVault` implements that terminal rule, `invariant_T_ResidualLiveness`
will go green for the put as well. The Vyper reference and Lean model implement
the §6 rule; the shipped Solidity does not yet — this row stays RED until it does.

`T_OracleIndependence` is structural and is handled in the Halmos track
(`check_T_OracleIndependence`); there is no Foundry invariant for it.
