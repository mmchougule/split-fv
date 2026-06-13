/-
  PUT VAULT reachability (first-class). States produced by finite valid transition
  sequences from `init`. WF is proved to be an inductive invariant for the put — holds
  at init, preserved by every step. Backbone of all put theorems — ZERO `sorry`.
  Re-proved independently in `Split.Put`, not imported from the call.
-/
import Split.Put.State
import Split.Put.Transitions
import Split.Put.Rounding
namespace Split.Put

/-- `Reachable s` : s arises from some genesis by a finite sequence of valid steps. -/
inductive Reachable : State → Prop
  | init (strike maturity exerciseEnd : Nat) : Reachable (init strike maturity exerciseEnd)
  | step {s s' : State} {st : Step} : Reachable s → apply s st = some s' → Reachable s'

/-- WF holds at genesis. -/
theorem wf_init (strike maturity exerciseEnd : Nat) : WF (init strike maturity exerciseEnd) := by
  constructor <;> intro h <;> simp [init] at h ⊢

/-- mint preserves WF. -/
theorem wf_step_mint {s s' : State} {q : Nat} (h : WF s) (hstep : mint s q = some s') : WF s' := by
  unfold mint at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hns, _, _⟩ := hg
    injection hstep with hs'; subst hs'
    have hce := h.collEqN hns
    have hnp := h.nLeP hns
    have hcw := h.preNoCredW hns
    have hcu := h.preNoCredU hns
    constructor <;> intro hc <;> simp_all
  · exact absurd hstep (by simp)

/-- redeemPair preserves WF. -/
theorem wf_step_redeemPair {s s' : State} {q : Nat} (h : WF s)
    (hstep : redeemPair s q = some s') : WF s' := by
  unfold redeemPair at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hns, _, _, hqp, hqn, hqc⟩ := hg
    injection hstep with hs'; subst hs'
    have hce := h.collEqN hns
    have hnp := h.nLeP hns
    have hcw := h.preNoCredW hns
    have hcu := h.preNoCredU hns
    constructor <;> intro hc <;> simp_all <;> omega
  · exact absurd hstep (by simp)

/-- exercise preserves WF. -/
theorem wf_step_exercise {s s' : State} {q : Nat} (h : WF s)
    (hstep : exercise s q = some s') : WF s' := by
  unfold exercise at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hns, _, _, _, hqn, hqc⟩ := hg
    injection hstep with hs'; subst hs'
    have hce := h.collEqN hns
    have hnp := h.nLeP hns
    have hcw := h.preNoCredW hns
    have hcu := h.preNoCredU hns
    constructor <;> intro hc <;> simp_all <;> omega
  · exact absurd hstep (by simp)

/-- settle preserves WF. Two sub-cases on `pSupply = 0` (the §6 terminal rule). -/
theorem wf_step_settle {s s' : State} (h : WF s) (hstep : settle s = some s') : WF s' := by
  unfold settle at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hns, hmat⟩ := hg
    have hce := h.collEqN hns
    have hnp := h.nLeP hns
    have hcw := h.preNoCredW hns
    have hcu := h.preNoCredU hns
    split at hstep
    · rename_i hp0
      injection hstep with hs'; subst hs'
      constructor <;> intro hc <;> simp_all [floorDiv]
    · rename_i hp0
      injection hstep with hs'; subst hs'
      have hppos : 0 < s.pSupply := Nat.pos_of_ne_zero hp0
      have hcancelW : floorDiv (s.pSupply * s.collat) s.pSupply = s.collat := by
        rw [floorDiv, if_neg hp0, Nat.mul_div_cancel_left _ hppos]
      have hcancelU : floorDiv (s.pSupply * s.strikeBal) s.pSupply = s.strikeBal := by
        rw [floorDiv, if_neg hp0, Nat.mul_div_cancel_left _ hppos]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;>
        simp_all <;> omega
  · exact absurd hstep (by simp)

/-- redeemP preserves WF — the hard case. Uses floor super- and sub-additivity. -/
theorem wf_step_redeemP {s s' : State} {q : Nat} (h : WF s)
    (hstep : redeemP s q = some s') : WF s' := by
  unfold redeemP at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hset, hP0pos, hqpos, hqle⟩ := hg
    injection hstep with hs'; subst hs'
    have hsplitW : q * s.collatAt + (s.pSupply - q) * s.collatAt = s.pSupply * s.collatAt := by
      rw [← Nat.add_mul]; congr 1; omega
    have hsplitU : q * s.strikeAt + (s.pSupply - q) * s.strikeAt = s.pSupply * s.strikeAt := by
      rw [← Nat.add_mul]; congr 1; omega
    have hsuperW :
        floorDiv (q * s.collatAt) s.pSupplyAt
          + floorDiv ((s.pSupply - q) * s.collatAt) s.pSupplyAt
          ≤ floorDiv (s.pSupply * s.collatAt) s.pSupplyAt := by
      have := floorDiv_add_le' (q * s.collatAt) ((s.pSupply - q) * s.collatAt) s.pSupplyAt
      rwa [hsplitW] at this
    have hsuperU :
        floorDiv (q * s.strikeAt) s.pSupplyAt
          + floorDiv ((s.pSupply - q) * s.strikeAt) s.pSupplyAt
          ≤ floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt := by
      have := floorDiv_add_le' (q * s.strikeAt) ((s.pSupply - q) * s.strikeAt) s.pSupplyAt
      rwa [hsplitU] at this
    have hsubW :
        floorDiv (s.pSupply * s.collatAt) s.pSupplyAt
          ≤ floorDiv (q * s.collatAt) s.pSupplyAt
            + floorDiv ((s.pSupply - q) * s.collatAt) s.pSupplyAt + 1 := by
      by_cases hP0 : s.pSupplyAt = 0
      · simp [floorDiv, hP0]
      · have hP0' : 0 < s.pSupplyAt := Nat.pos_of_ne_zero hP0
        have := floorDiv_add_le (q * s.collatAt) ((s.pSupply - q) * s.collatAt) s.pSupplyAt hP0'
        rwa [hsplitW] at this
    have hsubU :
        floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt
          ≤ floorDiv (q * s.strikeAt) s.pSupplyAt
            + floorDiv ((s.pSupply - q) * s.strikeAt) s.pSupplyAt + 1 := by
      by_cases hP0 : s.pSupplyAt = 0
      · simp [floorDiv, hP0]
      · have hP0' : 0 < s.pSupplyAt := Nat.pos_of_ne_zero hP0
        have := floorDiv_add_le (q * s.strikeAt) ((s.pSupply - q) * s.strikeAt) s.pSupplyAt hP0'
        rwa [hsplitU] at this
    have hbackW := h.backW hset
    have hbackU := h.backU hset
    have hresW := h.resW hset
    have hresU := h.resU hset
    have hple := h.pLePAt hset
    have hliveW := h.liveW hset
    have hliveU := h.liveU hset
    have hns : s.settled = true := hset
    have hdust : s.pSupplyAt - (s.pSupply - q) = (s.pSupplyAt - s.pSupply) + q := by omega
    clear hsplitW hsplitU
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;>
      simp only [hns, not_true_eq_false] at hc ⊢ <;>
      omega
  · exact absurd hstep (by simp)

/-- claimW preserves WF (zero-before-send). -/
theorem wf_step_claimW {s s' : State} {amt : Nat} (h : WF s)
    (hstep : claimW s amt = some s') : WF s' := by
  unfold claimW at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hset, hamtc, hamtcol⟩ := hg
    injection hstep with hs'; subst hs'
    have hple := h.pLePAt hset
    have hbackW := h.backW hset
    have hbackU := h.backU hset
    have hresW := h.resW hset
    have hresU := h.resU hset
    have hliveW := h.liveW hset
    have hliveU := h.liveU hset
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;> simp_all <;> omega
  · exact absurd hstep (by simp)

/-- claimU preserves WF. -/
theorem wf_step_claimU {s s' : State} {amt : Nat} (h : WF s)
    (hstep : claimU s amt = some s') : WF s' := by
  unfold claimU at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hset, hamtc, hamtcol⟩ := hg
    injection hstep with hs'; subst hs'
    have hple := h.pLePAt hset
    have hbackW := h.backW hset
    have hbackU := h.backU hset
    have hresW := h.resW hset
    have hresU := h.resU hset
    have hliveW := h.liveW hset
    have hliveU := h.liveU hset
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hc <;> simp_all <;> omega
  · exact absurd hstep (by simp)

/-- tick preserves WF: only `now` changes. -/
theorem wf_step_tick {s s' : State} {t : Nat} (h : WF s)
    (hstep : apply s (.tick t) = some s') : WF s' := by
  simp only [apply] at hstep
  injection hstep with hs'; subst hs'
  constructor <;> intro hc <;> simp only [] <;>
    first
    | exact h.collEqN hc
    | exact h.nLeP hc
    | exact h.preNoCredW hc
    | exact h.preNoCredU hc
    | exact h.pLePAt hc
    | exact h.backW hc
    | exact h.backU hc
    | exact h.resW hc
    | exact h.resU hc
    | exact h.liveW hc
    | exact h.liveU hc

/-- WF is preserved by every valid transition. -/
theorem wf_step {s s' : State} {st : Step} (h : WF s) (hstep : apply s st = some s') : WF s' := by
  cases st with
  | mint q       => exact wf_step_mint h hstep
  | redeemPair q => exact wf_step_redeemPair h hstep
  | exercise q   => exact wf_step_exercise h hstep
  | settle       => exact wf_step_settle h hstep
  | redeemP q    => exact wf_step_redeemP h hstep
  | claimW a     => exact wf_step_claimW h hstep
  | claimU a     => exact wf_step_claimU h hstep
  | tick t       => exact wf_step_tick h hstep

/-- Therefore WF holds in every reachable state. -/
theorem wf_reachable {s : State} (h : Reachable s) : WF s := by
  induction h with
  | init s m e => exact wf_init s m e
  | step _ hstep ih => exact wf_step ih hstep

end Split.Put
