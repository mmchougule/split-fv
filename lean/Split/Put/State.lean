/-
  Split settlement core — PUT VAULT State (first-class, NOT a re-export of the call).
  Frozen field names mirror docs/SETTLEMENT_SPEC.md §2/§7, with ROLES SWAPPED:

    * collateral asset = USDC (6dp)   — held in `collat`
    * strike asset     = WETH (18dp)  — held in `strikeBal`
    * exercise pays the WETH strike IN and receives USDC collateral OUT.

  The accounting algebra is identical to the call vault (it is asset-agnostic at the
  Nat level), but every definition and theorem is re-stated and re-proved here in the
  `Split.Put` namespace — there is no `import Split.State` re-use. The put vault is
  first-class: not a re-export, and not a "same as the call, later".

  Ghost-total modeling: as in the call model, per-address ERC-20 maps are summarized by
  ghost totals (`totalClaimW` = aggregate WETH claim credits = strike-asset on the put;
  `totalClaimU` = aggregate USDC claim credits = collateral-asset on the put). Field NAMES
  are kept identical to the frozen spec so THEOREM_MAP rows line up; the SEMANTIC role of
  each asset is swapped versus the call vault and documented above.
-/
namespace Split.Put

abbrev U : Type := Nat

/-- Ceil division: money coming INTO the vault rounds up (never under-collects). -/
def ceilDiv (a b : Nat) : Nat := if b = 0 then 0 else (a + b - 1) / b

/-- Floor division: money going OUT of the vault rounds down (never over-pays). -/
def floorDiv (a b : Nat) : Nat := if b = 0 then 0 else a / b

structure State where
  -- immutable params
  strike      : Nat
  maturity    : Nat
  exerciseEnd : Nat
  -- mutable accounting (PUT roles: collat = USDC, strikeBal = WETH)
  collat      : Nat   -- collateral units held (USDC, 6dp on the put)
  strikeBal   : Nat   -- strike-asset units held (WETH, 18dp on the put)
  pSupply     : Nat
  nSupply     : Nat
  settled     : Bool
  pSupplyAt   : Nat
  collatAt    : Nat
  strikeAt    : Nat
  totalClaimW : Nat   -- ghost: Σ WETH(=strike) claim credits
  totalClaimU : Nat   -- ghost: Σ USDC(=collateral) claim credits
  now         : Nat
  deriving Repr

/-- The genesis state (everything zero, not yet settled). -/
def init (strike maturity exerciseEnd : Nat) : State :=
  { strike, maturity, exerciseEnd,
    collat := 0, strikeBal := 0, pSupply := 0, nSupply := 0,
    settled := false, pSupplyAt := 0, collatAt := 0, strikeAt := 0,
    totalClaimW := 0, totalClaimU := 0, now := 0 }

/-- Well-formedness for the PUT vault: the inductive invariant bundle every transition
    must preserve (SPEC §5/§7). Structurally identical to the call WF but re-stated here
    as a first-class predicate over `Split.Put.State`.

    Pre-settle (`¬settled`):
    * `collEqN`   : `collat = nSupply` — USDC collateral exactly backs live N.
    * `nLeP`      : `nSupply ≤ pSupply` — the gap counts exercised units.
    * `preNoCredW/U` : credits only exist post-settle.

    Post-settle (`settled`):
    * `pLePAt`    : `pSupply ≤ pSupplyAt`.
    * `backW/backU` : strong backing — holdings cover credits given PLUS remaining-P floor share.
    * `resW/resU`   : credits + remaining-P floor share ≤ frozen residual pool.
    * `liveW/liveU` : still-unclaimed holdings ≤ remaining-P floor share + bounded dust. -/
structure WF (s : State) : Prop where
  collEqN    : ¬ s.settled → s.collat = s.nSupply
  nLeP       : ¬ s.settled → s.nSupply ≤ s.pSupply
  preNoCredW : ¬ s.settled → s.totalClaimW = 0
  preNoCredU : ¬ s.settled → s.totalClaimU = 0
  pLePAt     : s.settled → s.pSupply ≤ s.pSupplyAt
  backW      : s.settled →
                 s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt ≤ s.collat
  backU      : s.settled →
                 s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt ≤ s.strikeBal
  resW       : s.settled →
                 s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt ≤ s.collatAt
  resU       : s.settled →
                 s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt ≤ s.strikeAt
  liveW      : s.settled →
                 s.collat ≤ s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt
                            + (s.pSupplyAt - s.pSupply)
  liveU      : s.settled →
                 s.strikeBal ≤ s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt
                            + (s.pSupplyAt - s.pSupply)

/-- ClaimSafe (collateral=USDC-out leg via `collat`): aggregate credits ≤ holdings. -/
theorem WF.claimSafeW {s : State} (h : WF s) : s.settled → s.totalClaimW ≤ s.collat := by
  intro hset; have := h.backW hset; omega

/-- ClaimSafe (strike=WETH leg via `strikeBal`): derived from `backU`. -/
theorem WF.claimSafeU {s : State} (h : WF s) : s.settled → s.totalClaimU ≤ s.strikeBal := by
  intro hset; have := h.backU hset; omega

/-- Pre-settle backing: `nSupply ≤ collat`. -/
theorem WF.backN {s : State} (h : WF s) : ¬ s.settled → s.nSupply ≤ s.collat := by
  intro hns; have := h.collEqN hns; omega

/-- ResidualBound (collateral leg): credits ≤ frozen collateral pool. -/
theorem WF.resBoundW {s : State} (h : WF s) : s.settled → s.totalClaimW ≤ s.collatAt := by
  intro hset; have := h.resW hset; omega

/-- ResidualBound (strike leg): credits ≤ frozen strike pool. -/
theorem WF.resBoundU {s : State} (h : WF s) : s.settled → s.totalClaimU ≤ s.strikeAt := by
  intro hset; have := h.resU hset; omega

/-- Named invariant predicate: Backing (put). -/
def Backing (s : State) : Prop :=
  (¬ s.settled → s.nSupply ≤ s.collat) ∧ (s.settled → s.totalClaimW ≤ s.collat)

/-- Named invariant predicate: ClaimSafe (put). -/
def ClaimSafe (s : State) : Prop :=
  s.totalClaimW ≤ s.collat ∧ s.totalClaimU ≤ s.strikeBal

/-- Named invariant predicate: ResidualBound (put). -/
def ResidualBound (s : State) : Prop :=
  s.settled → s.totalClaimW ≤ s.collatAt ∧ s.totalClaimU ≤ s.strikeAt

end Split.Put
