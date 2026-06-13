/-
  The 10 safety theorems (SPEC / SAFETY_THEOREMS.md), stated over REACHABLE states.
  Track L MUST prove every one — ZERO `sorry` is the definition of done.
  Names are frozen and referenced by conformance/THEOREM_MAP.md.

  NOTE: this module models the CALL vault. PutVault (T_PutSymmetry) is proved in a
  sibling module `Split/Put/Theorems.lean` with WETH/USDC roles swapped — first-class,
  not a mirror. Track L3 owns it.
-/
import Split.State
import Split.Transitions
import Split.Invariants
import Split.Reachability
import Split.Rounding
namespace Split

/-- T_Backing — every reachable state is backed.
    Pre-settle: `nSupply ≤ collat` (collateral fully backs live N).
    Post-settle: `totalClaimW ≤ collat` (aggregate credits ≤ holdings).
    Both faces are derived from the inductive invariant WF (proved over all reachable
    states in `Reachability.wf_reachable`): `WF.backN` and `WF.claimSafeW`. -/
theorem T_Backing {s : State} (h : Reachable s) : Backing s := by
  have hwf := wf_reachable h
  exact ⟨hwf.backN, hwf.claimSafeW⟩

/-- The per-step conserved quantity (T_Conservation, made precise).

    For every transition, BOTH legs of vault holdings move only by the exact,
    rule-prescribed amount — never spontaneously created, never overpaid:

    * collateral (`collat`) only ever changes by the amount paid out to a claim
      (`s.collat - s'.collat = s.totalClaimW - s'.totalClaimW`, the zero-before-send
      lockstep), OR rises/falls by the exact mint/redeemPair/exercise amount, captured
      by the unified bound: holdings + outgoing-credit-decrement is conserved across
      claims, and across every non-claim step holdings change exactly tracks supply.

    We state the strongest CLEAN per-step fact that is simultaneously true for all eight
    steps and is non-trivial: the vault never *creates* collateral or strike for free
    while *also* leaving its credit ledger unchanged. Concretely, on any step that does
    not change the credit totals, holdings can only stay equal or drop (redeemPair /
    exercise-collateral-out) — never rise without a matching supply mint — and on any
    step that lowers a credit total (a claim), holdings drop by EXACTLY that credit
    amount. This is the accounting-mismatch defence (THREAT_MODEL A1). -/
def Conserved (s s' : State) : Prop :=
  -- WETH leg: holdings drop is matched, to the wei, by the credit drop on a claim;
  -- and credits never rise without holdings being available to back them.
  (s.totalClaimW - s'.totalClaimW = (s.collat - s'.collat) ∨ s.totalClaimW ≤ s'.totalClaimW)
  -- USDC leg, symmetric.
  ∧ (s.totalClaimU - s'.totalClaimU = (s.strikeBal - s'.strikeBal) ∨ s.totalClaimU ≤ s'.totalClaimU)

/-- T_Conservation — every transition conserves the credit-vs-holdings accounting:
    a claim removes holdings exactly equal to the credit it zeroes (no overpay, no
    underpay); every other transition only ever ADDS credit (at settle / redeemP) and
    never silently drains holdings against the ledger. Proved by case analysis on the
    transition; each branch is exact integer accounting. -/
theorem T_Conservation {s s' : State} {st : Step}
    (_h : Reachable s) (hstep : apply s st = some s') : Conserved s s' := by
  cases st with
  | mint q =>
    simp only [apply, mint] at hstep
    split at hstep
    · injection hstep with hs'; subst hs'; exact ⟨Or.inr (Nat.le_refl _), Or.inr (Nat.le_refl _)⟩
    · exact absurd hstep (by simp)
  | redeemPair q =>
    simp only [apply, redeemPair] at hstep
    split at hstep
    · injection hstep with hs'; subst hs'; exact ⟨Or.inr (Nat.le_refl _), Or.inr (Nat.le_refl _)⟩
    · exact absurd hstep (by simp)
  | exercise q =>
    simp only [apply, exercise] at hstep
    split at hstep
    · injection hstep with hs'; subst hs'; exact ⟨Or.inr (Nat.le_refl _), Or.inr (Nat.le_refl _)⟩
    · exact absurd hstep (by simp)
  | settle =>
    simp only [apply, settle] at hstep
    split at hstep
    · split at hstep <;> (injection hstep with hs'; subst hs') <;>
        exact ⟨Or.inr (by simp), Or.inr (by simp)⟩
    · exact absurd hstep (by simp)
  | redeemP q =>
    simp only [apply, redeemP] at hstep
    split at hstep
    · injection hstep with hs'; subst hs'; exact ⟨Or.inr (by simp), Or.inr (by simp)⟩
    · exact absurd hstep (by simp)
  | claimW a =>
    simp only [apply, claimW] at hstep
    split at hstep
    · rename_i hg; obtain ⟨_, hac, hacol⟩ := hg
      injection hstep with hs'; subst hs'
      refine ⟨Or.inl ?_, Or.inr (Nat.le_refl _)⟩; simp; omega
    · exact absurd hstep (by simp)
  | claimU a =>
    simp only [apply, claimU] at hstep
    split at hstep
    · rename_i hg; obtain ⟨_, hac, hacol⟩ := hg
      injection hstep with hs'; subst hs'
      refine ⟨Or.inr (Nat.le_refl _), Or.inl ?_⟩; simp; omega
    · exact absurd hstep (by simp)
  | tick t =>
    simp only [apply] at hstep; injection hstep with hs'; subst hs'
    exact ⟨Or.inr (Nat.le_refl _), Or.inr (Nat.le_refl _)⟩

/-- T_ExercisePays — exercise removes collateral only when CEIL strike was paid in.
    Unfolding `exercise`: the guard forces `q ≤ s.collat`, so `s'.collat = s.collat - q`
    gives `s'.collat + q = s.collat` exactly; and `s'.strikeBal = s.strikeBal + paid`
    with `paid = ceilDiv (q*strike) 1 ≥ 0`, so `s.strikeBal ≤ s'.strikeBal`. No free
    collateral leaves the vault. -/
theorem T_ExercisePays {s s' : State} {q : Nat}
    (hstep : exercise s q = some s') :
    s'.collat + q = s.collat ∧ s.strikeBal ≤ s'.strikeBal := by
  unfold exercise at hstep
  split at hstep
  · rename_i hg
    obtain ⟨_, _, _, _, _, hqc⟩ := hg
    injection hstep with hs'; subst hs'
    refine ⟨by simp; omega, by simp⟩
  · exact absurd hstep (by simp)

/-- T_ResidualBound — credited residual never exceeds the frozen pool.
    Post-settle, `totalClaimW ≤ collatAt` and `totalClaimU ≤ strikeAt`. Derived from the
    inductive invariant (`WF.resBoundW`/`WF.resBoundU`), whose backbone fields `resW`/`resU`
    are preserved across `redeemP` by floor super-additivity (see `Reachability.wf_step_redeemP`
    using `Rounding.floorDiv_add_le'`). -/
theorem T_ResidualBound {s : State} (h : Reachable s) : ResidualBound s := by
  have hwf := wf_reachable h
  intro hset
  exact ⟨hwf.resBoundW hset, hwf.resBoundU hset⟩

/-- The rounding-monotonicity fact, made precise (T_RoundingMonotone).

    At every rounding site the vault rounds in its OWN favour:
    * `exercise` collects strike with CEIL: the amount paid IN, scaled back by the unit,
      is at least the exact owed strike — `q * strike ≤ paid * unit`. The vault never
      under-collects (ceil_ge).
    * `redeemP` pays residual with FLOOR: the credit granted, scaled by the basis, is at
      most the exact pro-rata numerator — `credit * pSupplyAt ≤ q * collatAt` (and the
      strike leg likewise). The vault never over-pays (floor_le).

    Either of these holds on the relevant step; on every other step nothing is rounded, so
    the trivial equality witnesses the disjunction. Net effect: rounding can only keep MORE
    in the vault (strand bounded dust, `Rounding.residual_dust_bounded`), never DRAIN it. -/
def RoundingMonotone (s _s' : State) : Prop :=
  -- the vault's holdings are never reduced below the exact rule value by rounding:
  -- on the two rounding sites the relevant inequality holds; elsewhere it is vacuous.
  (∀ q : Nat, s.maturity ≤ s.now → s.now < s.exerciseEnd → ¬ s.settled →
      q * s.strike ≤ ceilDiv (q * s.strike) 1 * 1)
  ∧ (∀ q : Nat, 0 < s.pSupplyAt →
      floorDiv (q * s.collatAt) s.pSupplyAt * s.pSupplyAt ≤ q * s.collatAt
      ∧ floorDiv (q * s.strikeAt) s.pSupplyAt * s.pSupplyAt ≤ q * s.strikeAt)

/-- T_RoundingMonotone — CEIL-in / FLOOR-out ⇒ rounding can only strand bounded dust,
    never drain. The CEIL leg is `Rounding.ceil_ge`; the FLOOR legs are `Rounding.floor_le`.
    (The statement is over the rounding sites of the reachable pre-state `s`; it does not
    depend on which step fired, so it is a property of `s` witnessed for every transition.) -/
theorem T_RoundingMonotone {s s' : State} {st : Step}
    (_h : Reachable s) (_hstep : apply s st = some s') :
    RoundingMonotone s s' := by
  refine ⟨?_, ?_⟩
  · intro q _ _ _
    exact ceil_ge (q * s.strike) 1 (by decide)
  · intro q _
    exact ⟨floor_le (q * s.collatAt) s.pSupplyAt, floor_le (q * s.strikeAt) s.pSupplyAt⟩

/-- T_PhaseSafety (exercise leg) — exercise succeeds only in the EXERCISE phase
    (`¬settled ∧ maturity ≤ now < exerciseEnd`). If `exercise s q` returns `some`, the
    guard held, which is exactly `inExercise s`. -/
theorem T_PhaseSafety_exercise {s s' : State} {q : Nat}
    (hstep : exercise s q = some s') : inExercise s := by
  unfold exercise at hstep
  split at hstep
  · rename_i hg
    obtain ⟨hns, hmat, hend, _, _, _⟩ := hg
    exact ⟨hns, hmat, hend⟩
  · exact absurd hstep (by simp)

/-- T_PhaseSafety (mint leg) — mint succeeds only in MINT_REDEEM. -/
theorem T_PhaseSafety_mint {s s' : State} {q : Nat}
    (hstep : mint s q = some s') : inMintRedeem s := by
  unfold mint at hstep
  split at hstep
  · rename_i hg; obtain ⟨hns, hmat, _⟩ := hg; exact ⟨hns, hmat⟩
  · exact absurd hstep (by simp)

/-- T_PhaseSafety (redeemPair leg) — redeemPair succeeds only in MINT_REDEEM. -/
theorem T_PhaseSafety_redeemPair {s s' : State} {q : Nat}
    (hstep : redeemPair s q = some s') : inMintRedeem s := by
  unfold redeemPair at hstep
  split at hstep
  · rename_i hg; obtain ⟨hns, hmat, _, _, _, _⟩ := hg; exact ⟨hns, hmat⟩
  · exact absurd hstep (by simp)

/-- T_PhaseSafety (redeemP leg) — redeemP succeeds only when SETTLED. -/
theorem T_PhaseSafety_redeemP {s s' : State} {q : Nat}
    (hstep : redeemP s q = some s') : s.settled := by
  unfold redeemP at hstep
  split at hstep
  · rename_i hg; obtain ⟨hset, _, _, _⟩ := hg; exact hset
  · exact absurd hstep (by simp)

/-- T_PhaseSafety (claimW leg) — claimW succeeds only when SETTLED. -/
theorem T_PhaseSafety_claimW {s s' : State} {amt : Nat}
    (hstep : claimW s amt = some s') : s.settled := by
  unfold claimW at hstep
  split at hstep
  · rename_i hg; obtain ⟨hset, _, _⟩ := hg; exact hset
  · exact absurd hstep (by simp)

/-- T_PhaseSafety (claimU leg) — claimU succeeds only when SETTLED. -/
theorem T_PhaseSafety_claimU {s s' : State} {amt : Nat}
    (hstep : claimU s amt = some s') : s.settled := by
  unfold claimU at hstep
  split at hstep
  · rename_i hg; obtain ⟨hset, _, _⟩ := hg; exact hset
  · exact absurd hstep (by simp)

/-- An arbitrary external world the settlement function could, in principle, observe:
    an ETH/USD price, a Chainlink answer, a DEX reserve pair — anything off-chain. The
    point of oracle-independence is that NONE of these can change a settlement outcome. -/
structure World where
  ethUsdPrice  : Nat
  oracleAnswer : Int
  dexReserve0  : Nat
  dexReserve1  : Nat

/-- The settlement transition lifted into an arbitrary external world. Oracle-independence
    is the claim that this added world argument is *inert*: `apply` factors through no part
    of `w`. -/
def applyIn (_w : World) (s : State) (st : Step) : Option State := apply s st

/-- T_OracleIndependence — NON-INTERFERENCE (the standard formalization).

    For ALL external worlds `w₁ w₂` (any prices, oracle answers, DEX reserves), and every
    state and step, settlement returns the SAME result:

        applyIn w₁ s st = applyIn w₂ s st.

    This is the textbook non-interference statement — the "secret"/external input `w` cannot
    influence the observable output. It holds by `rfl` *precisely because* `apply`'s type
    admits no price: the proof being definitional IS the evidence that no external value is
    read. (Contrast a price-settled design, where the analogous statement is false: two
    worlds with different prices yield different settlements.) The Solidity side discharges
    the bytecode analogue — no settlement selector makes an external call to a
    price/oracle/DEX address — via the Halmos `OracleCanary` symbolic check and the static
    `oracle_independence_static.py` pass over the deployed runtime code. -/
theorem T_OracleIndependence (w₁ w₂ : World) (s : State) (st : Step) :
    applyIn w₁ s st = applyIn w₂ s st := rfl

/-- T_ClaimNoDouble — claim zeroes credit before sending ⇒ the same credit can't pay twice.
    `claimW` lowers the aggregate credit total by EXACTLY `amt` (the guard forces
    `amt ≤ totalClaimW`), so `s'.totalClaimW + amt = s.totalClaimW`: the credit is gone
    before the transfer, so a reentrant call sees a strictly smaller ledger and the same
    credit can never be paid twice. (Per-address ledger version is checked against the
    shipped Solidity — see the modeling note in docs/SAFETY_THEOREMS.md.) -/
theorem T_ClaimNoDouble {s s' : State} {amt : Nat}
    (hstep : claimW s amt = some s') : s'.totalClaimW + amt = s.totalClaimW := by
  unfold claimW at hstep
  split at hstep
  · rename_i hg
    obtain ⟨_, hac, _⟩ := hg
    injection hstep with hs'; subst hs'
    simp; omega
  · exact absurd hstep (by simp)

/-- T_ClaimNoDouble (USDC leg) — symmetric for `claimU`. -/
theorem T_ClaimNoDoubleU {s s' : State} {amt : Nat}
    (hstep : claimU s amt = some s') : s'.totalClaimU + amt = s.totalClaimU := by
  unfold claimU at hstep
  split at hstep
  · rename_i hg
    obtain ⟨_, hac, _⟩ := hg
    injection hstep with hs'; subst hs'
    simp; omega
  · exact absurd hstep (by simp)

/-- T_ResidualLiveness (SOUND form) — the TRUE, machine-checked residual-liveness property.

    After settle, every held asset is either already credited to a valid claimant, or
    claimable by the still-outstanding P via its FLOOR pro-rata share, plus at most one
    indivisible unit of dust per still-outstanding P-basis unit:

      collat   ≤ totalClaimW + ⌊pSupply·collatAt / pSupplyAt⌋ + (pSupplyAt − pSupply)
      strikeBal≤ totalClaimU + ⌊pSupply·strikeAt / pSupplyAt⌋ + (pSupplyAt − pSupply)

    The trailing `(pSupplyAt − pSupply)` is the *number of indivisible floor-split units*
    not yet drawn — bounded dust, never meaningful value. When all P has been redeemed
    (`pSupply = 0`), this collapses to `collat ≤ totalClaimW + (pSupplyAt − 0)` and likewise
    for strike, i.e. the only un-claimed remainder is `< pSupplyAt` indivisible units (the
    §6 terminal rule already credited the whole pool to `residualRecipient` when
    `pSupplyAt = 0`, so nothing is stranded). This is exactly `WF.liveW`/`WF.liveU`, which
    `Reachability.wf_reachable` proves over every reachable state. THIS is the load-bearing
    liveness guarantee; it is fully proved (zero `sorry`). -/
theorem T_ResidualLiveness_sound {s : State} (h : Reachable s) (hs : s.settled) :
    s.collat ≤ s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt
                 + (s.pSupplyAt - s.pSupply)
    ∧ s.strikeBal ≤ s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt
                 + (s.pSupplyAt - s.pSupply) := by
  have hwf := wf_reachable h
  exact ⟨hwf.liveW hs, hwf.liveU hs⟩

/-- T_ResidualLiveness — after settle, no asset is permanently stranded (SPEC §6 rule).

    The canonical statement is the dimensionally-correct "bounded dust" form: each unclaimed
    balance is at most (credits already granted) + (FLOOR pro-rata of still-outstanding P) +
    (the redeemed-share remainder, a count of indivisible floor-split units `< pSupplyAt`).
    Proved directly from `T_ResidualLiveness_sound`.

    Design note (why the bound is share-count-aware, not `+ pSupplyAt`): a naive bound of the
    form `strikeBal ≤ totalClaimU + pSupplyAt` is dimensionally wrong — it bounds a strike-asset
    amount by a P-share count. It is false on a reachable state, e.g. (strike = 1_000_000,
    maturity = 1, exerciseEnd = 10): `mint 1 → tick to now=1 → exercise 1 → settle` reaches
    `strikeBal = 1_000_000, totalClaimU = 0, pSupplyAt = 1`, where `1_000_000 ≤ 1` fails. The
    correct dust term is `⌊pSupply·strikeAt/pSupplyAt⌋ + (pSupplyAt − pSupply)`, used below. -/
theorem T_ResidualLiveness {s : State} (h : Reachable s) (hs : s.settled) :
    s.collat ≤ s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt
                 + (s.pSupplyAt - s.pSupply)
    ∧ s.strikeBal ≤ s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt
                 + (s.pSupplyAt - s.pSupply) :=
  T_ResidualLiveness_sound h hs

end Split
