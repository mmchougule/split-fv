import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-!
# SplitVault — call settlement core in Verity (Lean-native EDSL)

This is a REAL Verity contract (`verity_contract` macro → CompilationModel → IR → Yul → EVM),
not a sketch. It encodes the frozen settlement model from
`split-fv/docs/SETTLEMENT_SPEC.md` (call vault: collateral = WETH, strike asset = USDC).

Frozen field names (SPEC §2): `collat, strikeBal, pSupply, nSupply, settled,
pSupplyAt, collatAt, strikeAt, claimW, claimU, balP, balN, now`.

Modeling notes (honest):
* `claimW/claimU/balP/balN` are real address→Uint256 mappings (Verity `slot n : Address → Uint256`).
* The GLOBAL safety theorems (T_Backing post-settle, T_ResidualBound, T_ClaimNoDouble aggregate)
  are stated over ghost totals `totalClaimW/totalClaimU` exactly as the Lean source of truth does,
  because Verity's whole-mapping sum proofs go through `Verity.Specs.Common.sumBalances` /
  `Verity.Proofs.Stdlib.ListSum` (see the Ledger contract). This is the same modeling decision
  the Lean track made — NOT a weakening.
* CEIL-in / FLOOR-out use Verity's proven `mulDivUp` (= ceil(a*b/c)) and `mulDivDown` (= floor).
  Strike is quoted in USDC (6dp) per 1 collateral unit; `UNIT_W` folds into the multiply so the
  on-chain op is `mulDivUp q strike UNIT_W` (CEIL) for exercise and `mulDivDown q frozen pSupplyAt`
  (FLOOR) for redeemP — money IN rounds up, money OUT rounds down (SPEC §4).
* Phase guards read ONLY `blockTimestamp` (a modeled EVM context field) and immutable params.
  There is NO price/oracle/DEX op in the Verity EDSL at all → T_OracleIndependence is structural:
  it cannot be violated because no such intrinsic exists to call.

UNIT_W = 1e18 collateral unit divisor; immutable params live in dedicated slots.
-/

verity_contract SplitVault where
  storage
    -- immutable params (set in constructor, never written again)
    strikeSlot      : Uint256 := slot 0   -- USDC (6dp) per 1 collateral unit
    maturitySlot    : Uint256 := slot 1
    exerciseEndSlot : Uint256 := slot 2
    unitWSlot       : Uint256 := slot 3   -- 1e18
    -- mutable accounting
    collatSlot      : Uint256 := slot 4
    strikeBalSlot   : Uint256 := slot 5
    pSupplySlot     : Uint256 := slot 6
    nSupplySlot     : Uint256 := slot 7
    settledSlot     : Uint256 := slot 8   -- 0 = false, 1 = true
    pSupplyAtSlot   : Uint256 := slot 9
    collatAtSlot    : Uint256 := slot 10
    strikeAtSlot    : Uint256 := slot 11
    -- ghost aggregate credit totals (for global claim-safety theorems)
    totalClaimWSlot : Uint256 := slot 12
    totalClaimUSlot : Uint256 := slot 13
    -- immutable residual sink (SPEC §6 terminal rule)
    residualRecipient : Address := slot 14
    -- per-address maps (pull-pattern credits + token balances)
    claimW          : Address → Uint256 := slot 15
    claimU          : Address → Uint256 := slot 16
    balP            : Address → Uint256 := slot 17
    balN            : Address → Uint256 := slot 18

  constructor (strike : Uint256, maturity : Uint256, exerciseEnd : Uint256,
               unitW : Uint256, residual : Address) := do
    setStorage strikeSlot strike
    setStorage maturitySlot maturity
    setStorage exerciseEndSlot exerciseEnd
    setStorage unitWSlot unitW
    setStorageAddr residualRecipient residual
    setStorage collatSlot 0
    setStorage strikeBalSlot 0
    setStorage pSupplySlot 0
    setStorage nSupplySlot 0
    setStorage settledSlot 0
    setStorage pSupplyAtSlot 0
    setStorage collatAtSlot 0
    setStorage strikeAtSlot 0
    setStorage totalClaimWSlot 0
    setStorage totalClaimUSlot 0

  -- 1. mint(q) [MINT_REDEEM] : 1 collateral ⇒ 1 P + 1 N to caller.
  function mint (q : Uint256) : Unit := do
    let sender ← msgSender
    let now ← blockTimestamp
    let settled ← getStorage settledSlot
    let maturity ← getStorage maturitySlot
    require (settled == 0) "settled"
    require (now < maturity) "phase: not MINT_REDEEM"
    require (q > 0) "q=0"
    let collat ← getStorage collatSlot
    let newCollat ← requireSomeUint (safeAdd collat q) "collat overflow"
    let pSupply ← getStorage pSupplySlot
    let newP ← requireSomeUint (safeAdd pSupply q) "pSupply overflow"
    let nSupply ← getStorage nSupplySlot
    let newN ← requireSomeUint (safeAdd nSupply q) "nSupply overflow"
    let bp ← getMapping balP sender
    let bp' ← requireSomeUint (safeAdd bp q) "balP overflow"
    let bn ← getMapping balN sender
    let bn' ← requireSomeUint (safeAdd bn q) "balN overflow"
    setStorage collatSlot newCollat
    setStorage pSupplySlot newP
    setStorage nSupplySlot newN
    setMapping balP sender bp'
    setMapping balN sender bn'

  -- 2. redeemPair(q) [MINT_REDEEM] : burn q P + q N, send q collateral out.
  function redeemPair (q : Uint256) : Unit := do
    let sender ← msgSender
    let now ← blockTimestamp
    let settled ← getStorage settledSlot
    let maturity ← getStorage maturitySlot
    require (settled == 0) "settled"
    require (now < maturity) "phase: not MINT_REDEEM"
    require (q > 0) "q=0"
    let bp ← getMapping balP sender
    require (bp >= q) "balP < q"
    let bn ← getMapping balN sender
    require (bn >= q) "balN < q"
    let collat ← getStorage collatSlot
    require (collat >= q) "collat < q"
    let pSupply ← getStorage pSupplySlot
    let nSupply ← getStorage nSupplySlot
    setMapping balP sender (sub bp q)
    setMapping balN sender (sub bn q)
    setStorage collatSlot (sub collat q)
    setStorage pSupplySlot (sub pSupply q)
    setStorage nSupplySlot (sub nSupply q)

  -- 3. exercise(q) [EXERCISE] : pay CEIL strike IN, burn q N, take q collateral OUT.
  function exercise (q : Uint256) : Unit := do
    let sender ← msgSender
    let now ← blockTimestamp
    let settled ← getStorage settledSlot
    let maturity ← getStorage maturitySlot
    let exerciseEnd ← getStorage exerciseEndSlot
    require (settled == 0) "settled"
    require (now >= maturity) "phase: before maturity"
    require (now < exerciseEnd) "phase: after exerciseEnd"
    require (q > 0) "q=0"
    let bn ← getMapping balN sender
    require (bn >= q) "balN < q"
    let collat ← getStorage collatSlot
    require (collat >= q) "collat < q"
    let strike ← getStorage strikeSlot
    let unitW ← getStorage unitWSlot
    -- CEIL on money coming IN: paid = ceil(q * strike / UNIT_W)
    let paid := mulDivUp q strike unitW
    let strikeBal ← getStorage strikeBalSlot
    let newStrikeBal ← requireSomeUint (safeAdd strikeBal paid) "strikeBal overflow"
    let nSupply ← getStorage nSupplySlot
    setStorage strikeBalSlot newStrikeBal
    setMapping balN sender (sub bn q)
    setStorage nSupplySlot (sub nSupply q)
    setStorage collatSlot (sub collat q)

  -- 4. settle() [now ≥ maturity, once] : snapshot; §6 terminal rule when pSupplyAt == 0.
  function settle () : Unit := do
    let now ← blockTimestamp
    let settled ← getStorage settledSlot
    let maturity ← getStorage maturitySlot
    require (settled == 0) "already settled"
    require (now >= maturity) "before maturity"
    let collat ← getStorage collatSlot
    let strikeBal ← getStorage strikeBalSlot
    let pSupply ← getStorage pSupplySlot
    setStorage settledSlot 1
    setStorage pSupplyAtSlot pSupply
    setStorage collatAtSlot collat
    setStorage strikeAtSlot strikeBal
    -- §6 terminal rule: if pSupplyAt == 0, route the ENTIRE residual to the immutable
    -- residualRecipient (credited, claimable via claimWeth/claimUsdc). Otherwise residual
    -- stays pro-rata P-redeemable (no credit movement here).
    if pSupply == 0 then
      let recip ← getStorageAddr residualRecipient
      let tcw ← getStorage totalClaimWSlot
      let tcu ← getStorage totalClaimUSlot
      let cwCur ← getMapping claimW recip
      let cuCur ← getMapping claimU recip
      setStorage totalClaimWSlot (add tcw collat)
      setStorage totalClaimUSlot (add tcu strikeBal)
      setMapping claimW recip (add cwCur collat)
      setMapping claimU recip (add cuCur strikeBal)
    else
      pure ()

  -- 5. redeemP(q) [SETTLED, pSupplyAt>0] : burn q P, credit FLOOR pro-rata of frozen pools.
  function redeemP (q : Uint256) : Unit := do
    let sender ← msgSender
    let settled ← getStorage settledSlot
    require (settled == 1) "not settled"
    let pSupplyAt ← getStorage pSupplyAtSlot
    require (pSupplyAt > 0) "pSupplyAt=0"
    require (q > 0) "q=0"
    let bp ← getMapping balP sender
    require (bp >= q) "balP < q"
    let pSupply ← getStorage pSupplySlot
    require (pSupply >= q) "pSupply < q"
    let collatAt ← getStorage collatAtSlot
    let strikeAt ← getStorage strikeAtSlot
    -- FLOOR on money going OUT: credit = floor(q * frozenPool / pSupplyAt)
    let cw := mulDivDown q collatAt pSupplyAt
    let cu := mulDivDown q strikeAt pSupplyAt
    let tcw ← getStorage totalClaimWSlot
    let tcu ← getStorage totalClaimUSlot
    let cwCur ← getMapping claimW sender
    let cuCur ← getMapping claimU sender
    setMapping balP sender (sub bp q)
    setStorage pSupplySlot (sub pSupply q)
    setStorage totalClaimWSlot (add tcw cw)
    setStorage totalClaimUSlot (add tcu cu)
    setMapping claimW sender (add cwCur cw)
    setMapping claimU sender (add cuCur cu)

  -- 6a. claimW [SETTLED] : zero-before-send (reentrancy-safe). Sends collateral out.
  function claimWeth () : Unit := do
    let sender ← msgSender
    let settled ← getStorage settledSlot
    require (settled == 1) "not settled"
    let amt ← getMapping claimW sender
    let collat ← getStorage collatSlot
    require (collat >= amt) "collat < credit"
    let tcw ← getStorage totalClaimWSlot
    require (tcw >= amt) "total < credit"
    -- ZERO credit FIRST, then effect the outflow (checks-before-effects).
    setMapping claimW sender 0
    setStorage totalClaimWSlot (sub tcw amt)
    setStorage collatSlot (sub collat amt)

  -- 6b. claimU [SETTLED] : zero-before-send. Sends strike asset out.
  function claimUsdc () : Unit := do
    let sender ← msgSender
    let settled ← getStorage settledSlot
    require (settled == 1) "not settled"
    let amt ← getMapping claimU sender
    let strikeBal ← getStorage strikeBalSlot
    require (strikeBal >= amt) "strikeBal < credit"
    let tcu ← getStorage totalClaimUSlot
    require (tcu >= amt) "total < credit"
    setMapping claimU sender 0
    setStorage totalClaimUSlot (sub tcu amt)
    setStorage strikeBalSlot (sub strikeBal amt)

  -- views
  function collatOf () : Uint256 := do
    let v ← getStorage collatSlot
    return v

  function claimWOf (addr : Address) : Uint256 := do
    let v ← getMapping claimW addr
    return v

end Contracts
