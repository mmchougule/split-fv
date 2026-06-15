/-
  Split settlement core — Transitions (SPEC §4). Each returns `Option State`;
  `none` models a revert (guard failed). Pure functions of State.
-/
import Split.State
namespace Split

/-- Phase predicates (SPEC §3). -/
def inMintRedeem (s : State) : Prop := ¬ s.settled ∧ s.now < s.maturity
def inExercise   (s : State) : Prop := ¬ s.settled ∧ s.maturity ≤ s.now ∧ s.now < s.exerciseEnd

/-- 1. mint q: 1 collateral ⇒ 1 P + 1 N. -/
def mint (s : State) (q : Nat) : Option State :=
  if ¬ s.settled ∧ s.now < s.maturity ∧ 0 < q then
    some { s with collat := s.collat + q, pSupply := s.pSupply + q, nSupply := s.nSupply + q }
  else none

/-- 2. redeemPair q: burn q P + q N, take q collateral out. -/
def redeemPair (s : State) (q : Nat) : Option State :=
  if ¬ s.settled ∧ s.now < s.maturity ∧ 0 < q ∧ q ≤ s.pSupply ∧ q ≤ s.nSupply ∧ q ≤ s.collat then
    some { s with collat := s.collat - q, pSupply := s.pSupply - q, nSupply := s.nSupply - q }
  else none

/-- 3. exercise q: pay CEIL strike IN, take q collateral OUT, burn q N. -/
def exercise (s : State) (q : Nat) : Option State :=
  if ¬ s.settled ∧ s.maturity ≤ s.now ∧ s.now < s.exerciseEnd ∧ 0 < q ∧ q ≤ s.nSupply ∧ q ≤ s.collat then
    let paid := ceilDiv (q * s.strike) 1  -- unit factor folded into `strike`; see SPEC §1 note
    some { s with collat := s.collat - q, strikeBal := s.strikeBal + paid, nSupply := s.nSupply - q }
  else none

/-- 4. settle: only AFTER the exercise window closes (`exerciseEnd ≤ now`) so it can never
    preempt an in-window exercise; snapshot; apply the §6 residual terminal rule when pSupplyAt == 0. -/
def settle (s : State) : Option State :=
  if ¬ s.settled ∧ s.exerciseEnd ≤ s.now then
    let s1 := { s with settled := true, pSupplyAt := s.pSupply, collatAt := s.collat, strikeAt := s.strikeBal }
    if s.pSupply = 0 then
      -- residual routes to the immutable recipient (credited; claimable). Ghost totals capture it.
      some { s1 with totalClaimW := s1.totalClaimW + s.collat, totalClaimU := s1.totalClaimU + s.strikeBal }
    else some s1
  else none

/-- 5. redeemP q: burn q P, credit FLOOR pro-rata of the frozen residual pools. -/
def redeemP (s : State) (q : Nat) : Option State :=
  if s.settled ∧ 0 < s.pSupplyAt ∧ 0 < q ∧ q ≤ s.pSupply then
    let cw := floorDiv (q * s.collatAt) s.pSupplyAt
    let cu := floorDiv (q * s.strikeAt) s.pSupplyAt
    some { s with pSupply := s.pSupply - q, totalClaimW := s.totalClaimW + cw, totalClaimU := s.totalClaimU + cu }
  else none

/-- 6a. claimW amt: zero-before-send modeled as decrement of total + collateral out. -/
def claimW (s : State) (amt : Nat) : Option State :=
  if s.settled ∧ amt ≤ s.totalClaimW ∧ amt ≤ s.collat then
    some { s with totalClaimW := s.totalClaimW - amt, collat := s.collat - amt }
  else none

/-- 6b. claimU amt. -/
def claimU (s : State) (amt : Nat) : Option State :=
  if s.settled ∧ amt ≤ s.totalClaimU ∧ amt ≤ s.strikeBal then
    some { s with totalClaimU := s.totalClaimU - amt, strikeBal := s.strikeBal - amt }
  else none

/-- One transition label, for reachability induction. -/
inductive Step where
  | mint (q : Nat)
  | redeemPair (q : Nat)
  | exercise (q : Nat)
  | settle
  | redeemP (q : Nat)
  | claimW (amt : Nat)
  | claimU (amt : Nat)
  | tick (t : Nat)   -- advance `now` (env), the only price-free time input

def apply (s : State) : Step → Option State
  | .mint q       => mint s q
  | .redeemPair q => redeemPair s q
  | .exercise q   => exercise s q
  | .settle       => settle s
  | .redeemP q    => redeemP s q
  | .claimW a     => claimW s a
  | .claimU a     => claimU s a
  | .tick t       => some { s with now := s.now + t }

end Split
