-- Aggregate import so `lake build` checks the whole settlement proof.
import Split.State
import Split.Transitions
import Split.Invariants
import Split.Reachability
import Split.Rounding
import Split.Theorems
-- Put vault (T_PutSymmetry) — first-class proofs, roles swapped (collateral=USDC, strike=WETH).
import Split.Put.Theorems
