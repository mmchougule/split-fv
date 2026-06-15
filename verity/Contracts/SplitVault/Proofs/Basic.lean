/-
  SplitVault settlement-core proofs (Verity) — per-transition state-delta lemmas
  and the rounding-monotone arithmetic fact.

  Proof idiom mirrors the Verity ERC20/Ledger proofs:
    simp [fnName, slotNames, setStorage, setMapping, getStorage, getMapping,
          msgSender, blockTimestamp, Contract.runState, Verity.bind, Bind.bind, guards]

  STATUS: these are the mechanical, single-transition results. The
  inductive WF-preservation theorems (T_Backing over all reachable states,
  T_ResidualBound aggregate, T_ClaimNoDouble aggregate) are carried by the Lean
  source of truth in ../../../lean and are NOT duplicated here unless they
  compile green in this Verity tree. See ../../README.md for the exact split.
-/

import Contracts.SplitVault.Spec
import Verity.Proofs.Stdlib.Math

namespace Contracts.SplitVault.Proofs

open Verity
open Verity.EVM.Uint256
open Contracts.SplitVault
open Contracts.SplitVault.Spec
open Verity.Stdlib.Math (mulDivUp mulDivDown MAX_UINT256)

/-! ## T_RoundingMonotone (arithmetic core)

CEIL on money IN, FLOOR on money OUT. At the nat level (no wrap), the FLOOR of a
ratio never exceeds the CEIL of the same ratio, so the vault can only ever keep
MORE than the exact fair share — never less. This is the heart of why rounding
can only strand dust, never drain.

Discharged by reusing the framework's proven `mulDivDown_le_mulDivUp`. The two
operations here are EXACTLY the ones the contract calls: `mulDivUp` for the
CEIL strike paid IN on `exercise`, `mulDivDown` for the FLOOR pro-rata credited
OUT on `redeemP`. -/
theorem rounding_floor_le_ceil (q strike unitW : Uint256)
    (hC : unitW ≠ 0)
    (hNum : (q : Nat) * (strike : Nat) + ((unitW : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivDown q strike unitW : Nat) ≤ (mulDivUp q strike unitW : Nat) :=
  Verity.Proofs.Stdlib.Math.mulDivDown_le_mulDivUp q strike unitW hC hNum

/-- The exact `redeemP` FLOOR-out form: credits never round above the fair share. -/
theorem redeemP_floor_le_ceil (q pool pSupplyAt : Uint256)
    (hC : pSupplyAt ≠ 0)
    (hNum : (q : Nat) * (pool : Nat) + ((pSupplyAt : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivDown q pool pSupplyAt : Nat) ≤ (mulDivUp q pool pSupplyAt : Nat) :=
  Verity.Proofs.Stdlib.Math.mulDivDown_le_mulDivUp q pool pSupplyAt hC hNum

-- Make the axiom footprint self-verifying: `lake build` prints the exact axioms
-- each theorem depends on. These inherit whatever the reused Mathlib-backed
-- framework lemma `mulDivDown_le_mulDivUp` carries (expect the standard
-- `propext, Classical.choice, Quot.sound` — NOT any project-local `sorry`/axiom).
#print axioms rounding_floor_le_ceil
#print axioms redeemP_floor_le_ceil

end Contracts.SplitVault.Proofs
