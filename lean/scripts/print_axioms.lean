/-
  Axiom audit. Run from the `lean/` directory:

      lake env lean scripts/print_axioms.lean

  A clean result prints only `propext`, `Classical.choice`, `Quot.sound` (and NO
  `sorryAx`) for every theorem below. Any `sorryAx` would mean a proof hole.
-/
import Split.Theorems
import Split.Put.Theorems

open Split

#print axioms T_Backing
#print axioms T_Conservation
#print axioms T_ExercisePays
#print axioms T_ResidualBound
#print axioms T_RoundingMonotone
#print axioms T_PhaseSafety_exercise
#print axioms T_OracleIndependence
#print axioms T_ClaimNoDouble
#print axioms T_ResidualLiveness

#print axioms Split.Put.T_PutSymmetry
#print axioms Split.Put.T_ResidualLiveness
