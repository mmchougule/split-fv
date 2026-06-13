/-
  Split settlement core — State (pure-Nat model, call vault primary).
  Frozen field names mirror docs/SETTLEMENT_SPEC.md §2.

  Modeling choice: per-address ERC-20 maps are summarized by GHOST TOTALS
  (`totalClaimW/U`, `pSupply`, `nSupply`) so the global safety theorems are
  stateable without a Finset/mathlib dependency. The per-address layer
  (ClaimNoDouble at the individual level) is added by Track L in a later module.
-/
namespace Split

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
  -- mutable accounting
  collat      : Nat   -- collateral units held
  strikeBal   : Nat   -- strike-asset units held
  pSupply     : Nat
  nSupply     : Nat
  settled     : Bool
  pSupplyAt   : Nat
  collatAt    : Nat
  strikeAt    : Nat
  totalClaimW : Nat   -- ghost: Σ claimW credits
  totalClaimU : Nat   -- ghost: Σ claimU credits
  now         : Nat
  deriving Repr

/-- The genesis state (everything zero, not yet settled). -/
def init (strike maturity exerciseEnd : Nat) : State :=
  { strike, maturity, exerciseEnd,
    collat := 0, strikeBal := 0, pSupply := 0, nSupply := 0,
    settled := false, pSupplyAt := 0, collatAt := 0, strikeAt := 0,
    totalClaimW := 0, totalClaimU := 0, now := 0 }

/-- Well-formedness: the bundle every transition must preserve (SPEC §5).

    This is the *inductive* invariant — strengthened from the original three-line
    sketch so that it is actually preserved by the real transition set (in
    particular `exercise`, which lowers `nSupply` and `collat` together but leaves
    `pSupply` untouched, so the naive `pSupply = nSupply` coupling is NOT inductive
    and is replaced by the exact `collat = nSupply` / `nSupply ≤ pSupply` pair).

    Pre-settle (`¬settled`):
    * `collEqN`   : `collat = nSupply` — collateral exactly backs live N. (mint/redeem
                    move them together; exercise lowers both by `q`.) Implies `backN`.
    * `nLeP`      : `nSupply ≤ pSupply` — every exercised N retired a unit of P-claimable
                    backing; the gap `pSupply - nSupply` counts exercised units.
    * `preNoCredW/U` : `totalClaimW = 0`, `totalClaimU = 0` — credits only exist post-settle.

    Post-settle (`settled`):
    * `pLePAt`    : `pSupply ≤ pSupplyAt` — outstanding P never exceeds the frozen basis.
    * `claimSafeW/U` : `totalClaimW ≤ collat`, `totalClaimU ≤ strikeBal` — credits ≤ holdings.
    * `resBoundW/U`  : `totalClaimW ≤ collatAt`, `totalClaimU ≤ strikeAt` — credits ≤ frozen pool.
    * `liveW/U`   : the *exact* liveness/dust accounting. With `c0 := collatAt`, `P0 := pSupplyAt`:
        `collat - totalClaimW ≤ floorDiv (pSupply * c0) P0 + (P0 - pSupply)`.
      It says the still-unclaimed collateral is at most what remaining P can still draw
      (`floorDiv (pSupply*c0) P0`) plus at most one wei of dust per outstanding P-basis
      unit. At `pSupply = 0` this collapses to `collat ≤ totalClaimW + P0` (dust < P0). -/
structure WF (s : State) : Prop where
  -- pre-settle
  collEqN    : ¬ s.settled → s.collat = s.nSupply
  nLeP       : ¬ s.settled → s.nSupply ≤ s.pSupply
  preNoCredW : ¬ s.settled → s.totalClaimW = 0
  preNoCredU : ¬ s.settled → s.totalClaimU = 0
  -- post-settle
  pLePAt     : s.settled → s.pSupply ≤ s.pSupplyAt
  -- backW/backU : STRONG backing — current holdings cover credits already given PLUS what the
  --   remaining P can still draw (its floor pro-rata share). This is the inductive backbone of
  --   claim safety: it is preserved by redeemP (super-additivity of floor) and by claim
  --   (holdings and credits drop in lock-step). `claimSafeW`/`claimSafeU` (Σ credits ≤ holdings,
  --   the T_Backing post-settle face) are DERIVED from these (see theorems below).
  backW      : s.settled →
                 s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt ≤ s.collat
  backU      : s.settled →
                 s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt ≤ s.strikeBal
  -- resW/resU : credits already given PLUS what remaining P can still draw never exceed
  --             the frozen residual pool. This is the residual-bound backbone.
  resW       : s.settled →
                 s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt ≤ s.collatAt
  resU       : s.settled →
                 s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt ≤ s.strikeAt
  -- liveW/liveU : the still-unclaimed holdings are at most what remaining P can draw plus
  --               bounded dust (≤ pSupplyAt-pSupply). Drives ResidualLiveness.
  liveW      : s.settled →
                 s.collat ≤ s.totalClaimW + floorDiv (s.pSupply * s.collatAt) s.pSupplyAt
                            + (s.pSupplyAt - s.pSupply)
  liveU      : s.settled →
                 s.strikeBal ≤ s.totalClaimU + floorDiv (s.pSupply * s.strikeAt) s.pSupplyAt
                            + (s.pSupplyAt - s.pSupply)

/-- ClaimSafe (WETH leg): aggregate credits never exceed current holdings (T_Backing
    post-settle). Derived from the strong backing field `backW`. -/
theorem WF.claimSafeW {s : State} (h : WF s) : s.settled → s.totalClaimW ≤ s.collat := by
  intro hset; have := h.backW hset; omega

/-- ClaimSafe (USDC leg): derived from `backU`. -/
theorem WF.claimSafeU {s : State} (h : WF s) : s.settled → s.totalClaimU ≤ s.strikeBal := by
  intro hset; have := h.backU hset; omega

/-- `backN` (the original pre-settle backing) is a derived fact: `collat = nSupply ≥ nSupply`. -/
theorem WF.backN {s : State} (h : WF s) : ¬ s.settled → s.nSupply ≤ s.collat := by
  intro hns; have := h.collEqN hns; omega

/-- ResidualBound (WETH leg): credits never exceed the frozen collateral pool — derived from `resW`. -/
theorem WF.resBoundW {s : State} (h : WF s) : s.settled → s.totalClaimW ≤ s.collatAt := by
  intro hset; have := h.resW hset; omega

/-- ResidualBound (USDC leg): credits never exceed the frozen strike pool — derived from `resU`. -/
theorem WF.resBoundU {s : State} (h : WF s) : s.settled → s.totalClaimU ≤ s.strikeAt := by
  intro hset; have := h.resU hset; omega

end Split
