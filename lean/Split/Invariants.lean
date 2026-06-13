/-
  Named invariant predicates referenced by the theorems. Keep these as the single
  definition site so Theorems.lean and the conformance THEOREM_MAP use identical names.
-/
import Split.State
namespace Split

/-- Backing: collateral covers live N (pre-settle) / outstanding credits (post-settle). -/
def Backing (s : State) : Prop :=
  (¬ s.settled → s.nSupply ≤ s.collat) ∧ (s.settled → s.totalClaimW ≤ s.collat)

/-- Claim safety: aggregate credits never exceed vault holdings. -/
def ClaimSafe (s : State) : Prop :=
  s.totalClaimW ≤ s.collat ∧ s.totalClaimU ≤ s.strikeBal

/-- Residual bound (SAFETY_THEOREMS T_ResidualBound, SPEC §5): post-settle, the total
    P-credited assets can never exceed the FROZEN residual pools (`collatAt` / `strikeAt`).
    Both asset legs are bounded — WETH credits by the frozen collateral basis, USDC credits
    by the frozen strike basis. -/
def ResidualBound (s : State) : Prop :=
  s.settled → s.totalClaimW ≤ s.collatAt ∧ s.totalClaimU ≤ s.strikeAt

end Split
