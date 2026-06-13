/-
  PUT VAULT rounding lemmas (first-class). CEIL on money IN (WETH strike), FLOOR on
  money OUT (USDC collateral / WETH residual) ⇒ the vault can only ever STRAND bounded
  dust, never DRAIN. Re-proved independently in `Split.Put`.
-/
import Split.Put.State
namespace Split.Put

/-- Ceil never under-collects: ceilDiv a b * b ≥ a (for b > 0). -/
theorem ceil_ge (a b : Nat) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  have hbne : b ≠ 0 := Nat.not_eq_zero_of_lt hb
  unfold ceilDiv
  rw [if_neg hbne]
  have hdm := Nat.div_add_mod (a + b - 1) b
  have hmod : (a + b - 1) % b < b := Nat.mod_lt _ hb
  have hcomm : ((a + b - 1) / b) * b = b * ((a + b - 1) / b) := Nat.mul_comm _ _
  omega

/-- Floor never over-pays: floorDiv a b * b ≤ a. -/
theorem floor_le (a b : Nat) : floorDiv a b * b ≤ a := by
  unfold floorDiv
  by_cases hb : b = 0
  · rw [if_pos hb]; simp
  · rw [if_neg hb]
    have hdm := Nat.div_add_mod a b
    have hcomm : (a / b) * b = b * (a / b) := Nat.mul_comm _ _
    omega

/-- Dust from a FLOOR pro-rata split is bounded by `basis` units. -/
theorem residual_dust_bounded (q pool basis : Nat) (hb : 0 < basis) :
    q * pool - (floorDiv (q * pool) basis) * basis < basis := by
  have hbne : basis ≠ 0 := Nat.not_eq_zero_of_lt hb
  unfold floorDiv
  rw [if_neg hbne]
  have hdm := Nat.div_add_mod (q * pool) basis
  have hmod : (q * pool) % basis < basis := Nat.mod_lt _ hb
  have hcomm : ((q * pool) / basis) * basis = basis * ((q * pool) / basis) := Nat.mul_comm _ _
  omega

/-- Quotient sub-additivity up to 1: `(x+y)/b ≤ x/b + y/b + 1` (b>0). -/
theorem div_add_le (x y b : Nat) (hb : 0 < b) : (x + y) / b ≤ x / b + y / b + 1 := by
  have hxlt : x < b * (x / b) + b := by
    have h := Nat.div_add_mod x b; have hr : x % b < b := Nat.mod_lt _ hb; omega
  have hylt : y < b * (y / b) + b := by
    have h := Nat.div_add_mod y b; have hr : y % b < b := Nat.mod_lt _ hb; omega
  have hexp : b * (x / b + y / b + 2) = b * (x / b) + b * (y / b) + (b + b) := by
    rw [Nat.mul_add, Nat.mul_add]
    have : b * 2 = b + b := by omega
    rw [this]
  have hsum : x + y < b * (x / b + y / b + 2) := by rw [hexp]; omega
  have hlt : (x + y) / b < x / b + y / b + 2 := by
    rw [Nat.div_lt_iff_lt_mul hb]; rw [Nat.mul_comm] at hsum; exact hsum
  omega

/-- Sub-additivity of floor division up to 1. -/
theorem floorDiv_add_le (x y b : Nat) (hb : 0 < b) :
    floorDiv (x + y) b ≤ floorDiv x b + floorDiv y b + 1 := by
  have hbne : b ≠ 0 := Nat.not_eq_zero_of_lt hb
  unfold floorDiv
  rw [if_neg hbne, if_neg hbne, if_neg hbne]
  exact div_add_le x y b hb

/-- Division is monotone in the numerator. -/
theorem div_mono (a a' b : Nat) (h : a ≤ a') : a / b ≤ a' / b := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    rw [Nat.le_div_iff_mul_le hbpos]
    exact Nat.le_trans (Nat.div_mul_le_self a b) h

/-- Super-additivity of floor division: `⌊x/b⌋ + ⌊y/b⌋ ≤ ⌊(x+y)/b⌋`. -/
theorem le_div_add (x y b : Nat) : x / b + y / b ≤ (x + y) / b := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hxle : b * (x / b) ≤ x := by have := Nat.div_add_mod x b; omega
    have hyle : b * (y / b) ≤ y := by have := Nat.div_add_mod y b; omega
    have hsum : b * (x / b + y / b) ≤ x + y := by rw [Nat.mul_add]; omega
    have hmono := div_mono (b * (x / b + y / b)) (x + y) b hsum
    rwa [Nat.mul_div_cancel_left _ hbpos] at hmono

/-- Floor of a pro-rata split is monotone in the numerator factor. -/
theorem floorDiv_le_floorDiv_of_le (a a' b : Nat) (h : a ≤ a') :
    floorDiv a b ≤ floorDiv a' b := by
  unfold floorDiv
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb]; omega
  · rw [if_neg hb, if_neg hb]; exact div_mono a a' b h

/-- `floorDiv x b + floorDiv y b ≤ floorDiv (x+y) b` (super-additivity, floorDiv form). -/
theorem floorDiv_add_le' (x y b : Nat) :
    floorDiv x b + floorDiv y b ≤ floorDiv (x + y) b := by
  unfold floorDiv
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb, if_pos hb]; omega
  · rw [if_neg hb, if_neg hb, if_neg hb]; exact le_div_add x y b

end Split.Put
