import Verity.Specs.Common
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.SplitVault.SplitVault

/-!
# SplitVault — settlement-core specs (Verity)

Theorem-named predicates over `ContractState`, frozen to the names in
`split-fv/docs/SAFETY_THEOREMS.md`. The proof theorems (`Proofs/`) show each
transition's executed result (`((fn args).run s).snd`) satisfies these.

Slot map (must match SplitVault.lean exactly):
  0 strike · 1 maturity · 2 exerciseEnd · 3 unitW · 4 collat · 5 strikeBal
  6 pSupply · 7 nSupply · 8 settled · 9 pSupplyAt · 10 collatAt · 11 strikeAt
  12 totalClaimW · 13 totalClaimU · 14 residualRecipient (addr)
  15 claimW · 16 claimU · 17 balP · 18 balN
-/

namespace Contracts.SplitVault.Spec

open Verity
open Verity.EVM.Uint256

-- slot accessors (Uint256 storage)
abbrev sCollat      (s : ContractState) : Uint256 := s.storage 4
abbrev sStrikeBal   (s : ContractState) : Uint256 := s.storage 5
abbrev sPSupply     (s : ContractState) : Uint256 := s.storage 6
abbrev sNSupply     (s : ContractState) : Uint256 := s.storage 7
abbrev sSettled     (s : ContractState) : Uint256 := s.storage 8
abbrev sPSupplyAt   (s : ContractState) : Uint256 := s.storage 9
abbrev sCollatAt    (s : ContractState) : Uint256 := s.storage 10
abbrev sStrikeAt    (s : ContractState) : Uint256 := s.storage 11
abbrev sTotalClaimW (s : ContractState) : Uint256 := s.storage 12
abbrev sTotalClaimU (s : ContractState) : Uint256 := s.storage 13

/-- A state is "settled" iff slot 8 holds 1. -/
def isSettled (s : ContractState) : Prop := sSettled s = 1

/-! ## Well-formedness `WF` (SPEC §5) — the invariant bundle preserved by every transition. -/
structure WF (s : ContractState) : Prop where
  -- pre-settle: collateral fully backs N (every N can take 1 collateral or be matched in a pair)
  backN      : ¬ isSettled s → (sNSupply s : Nat) ≤ (sCollat s : Nat)
  -- P and N are coupled 1:1 in MINT_REDEEM
  coupled    : ¬ isSettled s → sPSupply s = sNSupply s
  -- post-settle: aggregate credit totals never exceed vault holdings
  claimSafeW : isSettled s → (sTotalClaimW s : Nat) ≤ (sCollat s : Nat)
  claimSafeU : isSettled s → (sTotalClaimU s : Nat) ≤ (sStrikeBal s : Nat)

/-! ## T_Backing — claims never exceed holdings. -/
def T_Backing (s : ContractState) : Prop :=
  (¬ isSettled s → (sNSupply s : Nat) ≤ (sCollat s : Nat)) ∧
  (isSettled s → (sTotalClaimW s : Nat) ≤ (sCollat s : Nat)
              ∧ (sTotalClaimU s : Nat) ≤ (sStrikeBal s : Nat))

/-! ## T_ExercisePays — collateral leaves only after the CEIL strike was paid in.
    paid = mulDivUp q strike UNIT_W (ceil); strikeBal grows by exactly `paid`,
    collat shrinks by exactly `q`. -/
def T_ExercisePays (q : Uint256) (s s' : ContractState) : Prop :=
  (sStrikeBal s' : Nat) = (sStrikeBal s : Nat)
      + (Verity.Stdlib.Math.mulDivUp q (s.storage 0) (s.storage 3) : Nat) ∧
  (sCollat s' : Nat) + (q : Nat) = (sCollat s : Nat)

/-! ## T_ResidualBound — redeemP credits never overdraw the frozen pool.
    Each credit is floor(q * frozenPool / pSupplyAt) ≤ q/pSupplyAt * frozenPool. -/
def T_ResidualBound (q : Uint256) (s s' : ContractState) : Prop :=
  (sTotalClaimW s' : Nat) =
      (sTotalClaimW s : Nat) + (Verity.Stdlib.Math.mulDivDown q (sCollatAt s) (sPSupplyAt s) : Nat) ∧
  (sTotalClaimU s' : Nat) =
      (sTotalClaimU s : Nat) + (Verity.Stdlib.Math.mulDivDown q (sStrikeAt s) (sPSupplyAt s) : Nat)

/-! ## T_RoundingMonotone — CEIL-in/FLOOR-out ⇒ vault never loses more than owed.
    For exercise: amount taken in (ceil) ≥ exact fair share (floor) of the same ratio. -/
def T_RoundingMonotone (q strike unitW : Uint256) : Prop :=
  (Verity.Stdlib.Math.mulDivDown q strike unitW : Nat)
    ≤ (Verity.Stdlib.Math.mulDivUp q strike unitW : Nat)

/-! ## T_ClaimNoDouble — claim zeroes the credit before the outflow (per-address). -/
def T_ClaimNoDoubleW (caller : Address) (s' : ContractState) : Prop :=
  s'.storageMap 15 caller = 0

def T_ClaimNoDoubleU (caller : Address) (s' : ContractState) : Prop :=
  s'.storageMap 16 caller = 0

/-! ## T_ResidualLiveness (SPEC §6) — at settle with pSupplyAt == 0, the entire residual
    is credited to the residual recipient (never stranded). -/
def T_ResidualLiveness (s s' : ContractState) : Prop :=
  sPSupply s = 0 →
    s'.storageMap 15 (s.storageAddr 14)
      = Verity.EVM.Uint256.add (s.storageMap 15 (s.storageAddr 14)) (sCollat s) ∧
    s'.storageMap 16 (s.storageAddr 14)
      = Verity.EVM.Uint256.add (s.storageMap 16 (s.storageAddr 14)) (sStrikeBal s)

end Contracts.SplitVault.Spec
