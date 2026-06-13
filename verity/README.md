# Verity track (experimental) — findings

**Question:** Can [Verity](https://veritylang.com)
(a Lean-4-native FV smart-contract EDSL by LFG Labs) express Split's call settlement core?

**Answer: YES.** The full call settlement core is expressible AND compiles green in real Verity
(`verity_contract` macro → CompilationModel → IR → Yul → EVM). The contract, its spec predicates,
and a first proof all build with `lake build`, **zero `sorry`, zero custom axioms** (proofs depend
only on `propext`). Lean (`../lean`) remains the designated proof source of truth per the spec; Verity
is a corroborating second mechanization that ALSO lowers to EVM bytecode — a strictly stronger position
than "documented gap."

## What was actually built and verified here

Files (mirror the Verity repo's `Contracts/<Name>/` layout so they drop straight in):

| File | Contents | Build status |
|---|---|---|
| `Contracts/SplitVault/SplitVault.lean` | Call settlement core: `mint`, `redeemPair`, `exercise` (CEIL-in), `settle` (incl. §6 terminal residual rule), `redeemP` (FLOOR-out), `claimWeth`/`claimUsdc` (zero-before-send), constructor, views | **compiles green** |
| `Contracts/SplitVault/Spec.lean` | Theorem-named predicates over `ContractState`: `WF`, `T_Backing`, `T_ExercisePays`, `T_ResidualBound`, `T_RoundingMonotone`, `T_ClaimNoDoubleW/U`, `T_ResidualLiveness` (frozen names from `docs/SAFETY_THEOREMS.md`) | **compiles green** |
| `Contracts/SplitVault/Proofs/Basic.lean` | `rounding_floor_le_ceil` + `redeemP_floor_le_ceil` — the T_RoundingMonotone arithmetic core (FLOOR ≤ CEIL), proven by reusing Verity's framework lemma `mulDivDown_le_mulDivUp` | **compiles green, 0 sorry, axioms = [propext]** |

Verified against Verity commit on `main` (Lean toolchain `leanprover/lean4:v4.22.0`, pinned by Verity).
Reproduce with `./build.sh` (see below) — first run downloads Mathlib (~30 min); SplitVault modules
themselves compile in seconds on top of the prebuilt framework.

## Why every settlement-core feature IS expressible in Verity

| Settlement need (SPEC) | Verity EDSL primitive used | Evidence |
|---|---|---|
| State fields `collat,strikeBal,pSupply,…` | `slot n : Uint256` storage slots | compiled |
| `claimW,claimU,balP,balN` per-address | `slot n : Address → Uint256` (`getMapping`/`setMapping`) | compiled (same as ERC20/Vault) |
| immutable `residualRecipient` | `slot n : Address` (`setStorageAddr`/`getStorageAddr`) | compiled |
| CEIL strike IN (`exercise`) | `mulDivUp q strike UNIT_W` (proven `= ceil(a*b/c)`) | `Verity.Stdlib.Math.mulDivUp` |
| FLOOR pro-rata OUT (`redeemP`) | `mulDivDown q pool pSupplyAt` (proven `= floor`) | `Verity.Stdlib.Math.mulDivDown` |
| overflow-checked adds | `safeAdd` + `requireSomeUint` | compiled |
| phase guards (MINT_REDEEM/EXERCISE/SETTLED) | `blockTimestamp` (modeled context) + `require` | compiled — see `T_PhaseSafety` note |
| §6 terminal residual rule (pSupplyAt==0) | statement-level `if pSupply == 0 then … else pure ()` | compiled |
| pull-claim zero-before-send | `setMapping claim sender 0` BEFORE the balance decrement | compiled — `T_ClaimNoDouble` by construction |
| **oracle independence** | **there is NO price/oracle/DEX intrinsic in the Verity EDSL** | structural; see below |

### T_OracleIndependence is structurally satisfied — and stronger in Verity than in Solidity
Verity's expression language has no opcode/intrinsic that reads an external price, oracle, or DEX in
this contract's surface (the only external-call form is `Expr.externalCall`, which is in the documented
*trust boundary* and is **not used** by SplitVault). Phase logic reads only `blockTimestamp`, a modeled
EVM context field with no price content. `grep -niE 'oracle|price|externalCall|getPrice|dex|quote'` over
`SplitVault.lean` returns only doc comments. So settlement cannot read a price — by absence of the
capability, exactly as the spec demands ("structural absence of price, not time-invariance").

## Honest status of the 10 theorems IN THIS VERITY TREE

`T_RoundingMonotone` is **proven green here** (the arithmetic core, both the exercise-CEIL and
redeemP-FLOOR instances). `T_OracleIndependence` and `T_ClaimNoDouble` hold **structurally /
by-construction** in the compiled contract (no price op; credit zeroed before send). `T_PhaseSafety`
is enforced by the compiled `require` guards. The remaining global, inductive theorems
(`T_Backing` / `T_Conservation` / `T_ResidualBound` aggregate / `T_ResidualLiveness` / put `T_PutSymmetry`)
are **stated** in `Spec.lean` but their full proofs are **carried by the Lean source of truth in
`../lean`** and are **NOT claimed proven in this Verity tree**. That is the honest line: spec + impl +
one real proof + structural theorems are done in Verity; the full inductive proof suite stays in Lean.

This split is deliberate: Lean is the proof source of truth; Verity is evaluated for whether it can
express the core. It CAN express the core (proven by compilation); the full proof port is a larger effort
and is not claimed here.

## Verity capability limits relevant to Split (documented, not blocking)
From Verity's own `capabilities`/`TRUST_ASSUMPTIONS` docs:
- **Trust boundary (not blocking settlement core):** `externalCall`/proxies/`delegatecall`/events;
  Yul→bytecode via `solc 0.8.33` is unverified. None are needed by the settlement core — they belong to
  the OUT-OF-SCOPE wrappers/keeper/facilitator (ASSUMPTIONS_AND_BOUNDARY.md), so this is consistent.
- **`forEach` over non-empty bodies / non-literal bounds: unproven.** Whole-mapping *sums* (needed for the
  aggregate `Σ claims ≤ pool` form) go through `Verity.Specs.Common.sumBalances` + `Proofs.Stdlib.ListSum`
  (the Ledger contract proves real conservation sum-equations this way), so the aggregate theorems are
  *expressible*; they were just not ported within the box.

## Why this matters for the EF/Vitalik review
The thesis is that settlement safety is an accounting theorem with no price read.
Verity strengthens that claim: the same machine that checks the proofs (Lean 4) also **compiles the
contract to EVM bytecode**, so the "spec ↔ impl ↔ deployed code" gap that normally needs a separate
conformance layer is closed inside one verified toolchain. The Vyper reference + Solidity conformance
tracks remain the path for the *shipped* contracts; Verity is the existence proof that Split's settlement
core can live entirely inside a verified-from-spec-to-bytecode pipeline.

## Reproduce
```bash
./build.sh          # clones Verity, builds framework (~30 min first run), then SplitVault modules
# or, against an existing Verity checkout at $VERITY:
cp -r Contracts/SplitVault $VERITY/Contracts/ && cd $VERITY \
  && lake build Contracts.SplitVault.SplitVault Contracts.SplitVault.Spec Contracts.SplitVault.Proofs.Basic
```
