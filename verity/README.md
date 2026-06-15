# Verity track (EXPERIMENTAL) — findings

> **Scope, up front.** This is an *experimental second mechanization* of Split's
> settlement core in [Verity](https://veritylang.com) (a Lean-4-native FV smart-contract
> EDSL by LFG Labs). What is established here: the settlement-call core (a) is *expressible*
> in the Verity EDSL and (b) *compiles* through Verity's pipeline (`verity_contract` macro →
> CompilationModel → IR → Yul → EVM), plus **one real arithmetic proof** (FLOOR ≤ CEIL).
> What is **NOT** done here: the full inductive safety suite (backing / conservation /
> residual-bound / liveness over all reachable states). Those proofs live in the main Lean
> track (`../lean`), which remains the designated proof source of truth. Do not read this
> track as "Split is proven safe in Verity" — read it as "Verity *can* host Split's core,
> shown by a green compile + one ported proof."

**Question:** Can Verity express Split's call settlement core, and does it compile?

**Answer: YES — the core is expressible and the modules compile green** (zero `sorry`,
zero project-local custom axioms; verified by source inspection — no `sorry`/`admit`/`axiom`/
`native_decide` in this tree). A `lake build` of the three modules produces `.olean` artifacts
and the proof file emits `#print axioms` so the exact axiom footprint is self-reported (it
inherits the reused Mathlib-backed framework lemma's axioms — expect the standard
`propext, Classical.choice, Quot.sound`, not anything project-local).

## What was actually built and verified here

Files (mirror the Verity repo's `Contracts/<Name>/` layout so they drop straight in):

| File | Contents | Build status |
|---|---|---|
| `Contracts/SplitVault/SplitVault.lean` | Call settlement core: `mint`, `redeemPair`, `exercise` (CEIL-in), `settle` (incl. §6 terminal residual rule), `redeemP` (FLOOR-out), `claimWeth`/`claimUsdc` (zero-before-send), constructor, views | **compiles green** |
| `Contracts/SplitVault/Spec.lean` | Theorem-named predicates over `ContractState`: `WF`, `T_Backing`, `T_ExercisePays`, `T_ResidualBound`, `T_RoundingMonotone`, `T_ClaimNoDoubleW/U`, `T_ResidualLiveness` (frozen names from `docs/SAFETY_THEOREMS.md`) | **compiles green** |
| `Contracts/SplitVault/Proofs/Basic.lean` | `rounding_floor_le_ceil` + `redeemP_floor_le_ceil` — the T_RoundingMonotone arithmetic core (FLOOR ≤ CEIL), proven by reusing Verity's framework lemma `mulDivDown_le_mulDivUp` | **compiles green, 0 sorry; `#print axioms` self-reports the footprint** |

Reproduce with `./build.sh` (see below) against Verity `main` (Lean toolchain
`leanprover/lean4:v4.22.0`, pinned by Verity). First run downloads Mathlib (~30 min);
the SplitVault modules themselves compile in seconds on top of the prebuilt framework.
A PASS establishes: the contract macro expands and compiles, the spec predicates typecheck,
and the rounding proof is accepted by the Lean kernel with no `sorry` (its axiom footprint
printed inline). It does **not** establish the inductive safety theorems — see below.

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

### T_OracleIndependence is structurally satisfied (by absence of the capability)
Verity's expression language has no opcode/intrinsic that reads an external price, oracle, or DEX in
this contract's surface (the only external-call form is `Expr.externalCall`, which is in the documented
*trust boundary* and is **not used** by SplitVault). Phase logic reads only `blockTimestamp`, a modeled
EVM context field with no price content. `grep -niE 'oracle|price|externalCall|getPrice|dex|quote'` over
`SplitVault.lean` returns only doc comments. So settlement cannot read a price — by absence of the
capability, exactly as the spec demands ("structural absence of price, not time-invariance").

## Status of the theorems IN THIS VERITY TREE

Exactly **one** theorem is *machine-checked by the Lean kernel* in this tree:
`T_RoundingMonotone` (the arithmetic core — both the exercise-CEIL and redeemP-FLOOR instances).
Three more hold by **structural argument about the compiled contract, not a Lean proof object**:
`T_OracleIndependence` (no price/oracle intrinsic exists to call), `T_ClaimNoDouble` (credit is
zeroed before the outflow, by construction), and `T_PhaseSafety` (enforced by the compiled `require`
guards). Treat those three as code-review-grade structural claims, not as discharged proofs.
The remaining global, inductive theorems
(`T_Backing` / `T_Conservation` / `T_ResidualBound` aggregate / `T_ResidualLiveness` / put `T_PutSymmetry`)
are **stated** in `Spec.lean` but their full proofs are **carried by the Lean source of truth in
`../lean`** and are **NOT claimed proven in this Verity tree**. Spec + impl +
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

## Why this matters for review
The thesis is that settlement safety is an accounting theorem with no price read.
Verity is interesting because the same machine that checks the proofs (Lean 4) also *compiles the
contract through to Yul/EVM*, so spec, implementation, and lowered code live in one tool rather than
three. Two caveats keep this from being "verified spec→bytecode":
1. **Only the rounding proof is machine-checked against this contract here.** The inductive safety
   properties are not proven against the Verity contract in this tree — they are carried by `../lean`.
   So the spec↔impl link is established for *one* property, not the full suite.
2. **The final Yul→bytecode step is itself unverified** (Verity emits Yul, then leans on `solc 0.8.33`;
   see the trust-boundary note above). So the pipeline is verified *up to* the Yul boundary, not all
   the way to deployed bytecode.

The Vyper reference + Solidity conformance tracks remain the path for the *shipped* contracts. Verity's
contribution is narrower but real: an existence proof that Split's settlement core can be *expressed and
compiled* inside a Lean-native FV pipeline, with one safety-relevant arithmetic fact already ported.

## Reproduce
```bash
./build.sh          # clones Verity, builds framework (~30 min first run), then SplitVault modules
# or, against an existing Verity checkout at $VERITY:
cp -r Contracts/SplitVault $VERITY/Contracts/ && cd $VERITY \
  && lake build Contracts.SplitVault.SplitVault Contracts.SplitVault.Spec Contracts.SplitVault.Proofs.Basic
```
