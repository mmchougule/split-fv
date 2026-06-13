# Halmos conformance — symbolic checks on the SHIPPED Solidity

Symbolic (not fuzz) conformance of the shipped `SplitVault.sol` / `PutVault.sol` settlement core to the
frozen safety theorems (`docs/SAFETY_THEOREMS.md`). Inputs are `svm.createUint256` symbols: a passing
`check_*` means the property holds for EVERY value in the stated bound, not for sampled inputs.

## Run

```bash
cd conformance/halmos
forge build                       # halmos reads the out/ artifacts (AST + storageLayout)
halmos                            # picks up halmos.toml (solver=z3, 90s/assertion)
python3 oracle_independence_static.py   # static-bytecode half of T_OracleIndependence
```

Status (last run): **25/25 symbolic checks PASS** + static oracle proof PASS.

## What's checked (names map 1:1 to SAFETY_THEOREMS.md / THEOREM_MAP.md)

| File | Checks |
|---|---|
| `test/SplitVaultSymbolic.t.sol` | call vault: Backing, Conservation, ExercisePays, ResidualBound, RoundingMonotone, PhaseSafety (×4), ClaimNoDouble |
| `test/PutVaultSymbolic.t.sol`   | put vault (T_PutSymmetry, roles swapped): Backing, Conservation, ExercisePays, ResidualBound, RoundingMonotone, PhaseSafety (×2), ClaimNoDouble |
| `test/OracleIndependence.t.sol` | `check_T_OracleIndependence` (+ `_put`): structural — symbolic storage + `svm.createCalldata` over EVERY settlement selector; an `OracleCanary` (mimics `latestAnswer`/`getReserves`/fallback) is asserted NEVER touched on ANY path. |
| `oracle_independence_static.py` | static-bytecode complement: no DELEGATECALL/CALLCODE, no hardcoded oracle/DEX address literal, all CALL targets derive only from the immutable `{weth,usdc,P,N}` handles (set once in the constructor, no setter). |

## T_OracleIndependence — the load-bearing structural claim

"Settlement reads no price" is proved two independent ways, both green:
1. **Dynamic (halmos):** every reachable path of every settlement selector, under fully symbolic vault
   storage, makes no call that touches the oracle canary.
2. **Static (python):** the runtime bytecode contains no proxy escape and no pinnable price target; call
   targets are structurally fixed to the four token contracts.

## Honest bound disclosure (no green-washing)

The nonlinear-multiplication checks (CEIL/FLOOR over `q*strike`: RoundingMonotone, ExercisePays,
ResidualBound, Backing-mint) bound the symbolic amount to `q < 2³²`. This is a **solver-tractability
limit, not a soundness assumption**: full 256-bit nonlinear bitvector reasoning is SMT-intractable —
both yices and z3 TIMEOUT at `2⁴⁸`–`2⁹⁶` even after 120 s (verified). The CEIL/FLOOR identities are
scale-free, so a `2³²`-wide symbolic `q` (≫ any real WETH/USDC position) is a faithful witness. The
**unbounded** statements are discharged in the Lean track; the **aggregate** Σ-bounds in Certora. Every
bounded check carries an inline `SYMBOLIC DOMAIN (honest bound)` comment stating exactly this. The
phase-safety, claim-no-double, and oracle-independence checks are FULLY unbounded.

`ResidualBound` asserts the safety form `credit <= pool` plus the single-division share identity
`credit == (pool*qr)/pAt` — NOT the re-multiplied `credit*pAt <= pool*qr`, which is the SMT-intractable
redundant restatement of EVM FLOOR division (and is what made the check time out before).

## Why z3 (pinned in `halmos.toml`)

The default solver (yices) stalls on the bounded nonlinear queries; z3 decides them in ~6–42 s each.
`solver_timeout_assertion = 90000` ms keeps CI from hanging while leaving headroom over the slowest check.
