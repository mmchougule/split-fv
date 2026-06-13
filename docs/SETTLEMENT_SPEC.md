# Settlement Spec — the frozen model

This is the source model every track maps to. **Names here are frozen.** Lean types, Vyper functions,
Solidity invariants, and Certora rules all reference these exact names. Call vault is primary; the put vault
(§6) swaps roles and gets its own first-class proofs.

## 1. Constants & units
- WETH: 18 decimals (`UNIT_W = 1e18`). USDC: 6 decimals (`UNIT_U = 1e6`).
- A vault is parameterized by immutable `strike` (USDC per 1 collateral unit, 6dp basis), `maturity` (unix),
  `exerciseEnd` (unix). These never change after deploy.
- **Call vault:** collateral = WETH, strike asset = USDC.
- **Put vault:** collateral = USDC, strike asset = WETH.

## 2. State (frozen field names)
```
collat    : Nat            -- collateral units held by the vault
strikeBal : Nat            -- strike-asset units held by the vault
pSupply   : Nat            -- outstanding P
nSupply   : Nat            -- outstanding N
settled   : Bool           -- settlement snapshot taken?
pSupplyAt : Nat            -- P supply frozen at settle (0 before)
collatAt  : Nat            -- collateral frozen at settle (residual basis)
strikeAt  : Nat            -- strike balance frozen at settle
claimW    : Addr → Nat     -- pull-pattern WETH claim credits
claimU    : Addr → Nat     -- pull-pattern USDC claim credits
balP      : Addr → Nat     -- P balances
balN      : Addr → Nat     -- N balances
now       : Nat            -- env time (phase guards only)
```
`residualRecipient : Addr` — immutable sink for the `pSupplyAt == 0` terminal case (see §5/§6).

## 3. Phases
```
MINT_REDEEM : ¬settled ∧ now <  maturity
EXERCISE    : ¬settled ∧ maturity ≤ now < exerciseEnd      -- settle() also allowed once now ≥ maturity
SETTLED     : settled
```

## 4. Transitions (frozen signatures) — `State → Option State` (None = revert)
1. `mint(caller, q)` [MINT_REDEEM, q>0]: `collat += q; pSupply += q; nSupply += q; balP[caller]+=q; balN[caller]+=q`.
2. `redeemPair(caller, q)` [MINT_REDEEM, q>0, balP≥q ∧ balN≥q]: burn q P + q N; `collat -= q; pSupply-=q; nSupply-=q`; send q collateral to caller.
3. `exercise(caller, q)` [EXERCISE, q>0, balN≥q]: `paid = ceilDiv(q*strike, UNIT_collateralToStrike)`; pull `paid` strike-asset in (`strikeBal += paid`); burn q N (`nSupply-=q`, `balN-=q`); send q collateral out (`collat -= q`).
4. `settle()` [now ≥ maturity, ¬settled]: `settled=true; pSupplyAt=pSupply; collatAt=collat; strikeAt=strikeBal`.
   - **Terminal rule (§6):** if `pSupplyAt == 0`, credit the entire residual to `residualRecipient`:
     `claimW[residualRecipient]+=collat (call) ; claimU[residualRecipient]+=strikeBal`. (Exact asset split per vault.)
5. `redeemP(caller, q)` [SETTLED, pSupplyAt>0, q>0, balP≥q]: burn q P (`pSupply-=q, balP-=q`);
   `claimW[caller] += floorDiv(q*collatAt, pSupplyAt)`; `claimU[caller] += floorDiv(q*strikeAt, pSupplyAt)`.
6. `claimW(caller)` / `claimU(caller)` [SETTLED]: `amt = claimW[caller]; claimW[caller]=0`; send `amt` out
   (`collat -= amt` for WETH on the call vault / appropriate asset). **Zero-before-send** (reentrancy-safe).

`ceilDiv(a,b) = (a + b - 1) / b` ; `floorDiv(a,b) = a / b`. CEIL on money coming IN to the vault, FLOOR on
money going OUT — so rounding can only ever keep more in the vault, never less.

## 5. Well-formedness `WF` (preserved by every transition)
- **Backing (pre-settle):** `collat ≥ nSupply` and `collat ≥ pSupply` are coupled via `pSupply == nSupply`
  while in MINT_REDEEM (mint/redeemPair move them together); exercise reduces `nSupply` and `collat` in lock-step.
- **Backing (post-settle):** `collat ≥ Σ_addr claimW[addr] + floorShare(remaining P)` and likewise for strike.
- **Claim safety:** `Σ_addr claimW[addr] ≤ collat` and `Σ_addr claimU[addr] ≤ strikeBal` in all SETTLED states.
- **Supply coupling:** mint adds 1 P + 1 N per unit; redeemPair removes 1+1; exercise removes only N; redeemP only P.
- **Decimals:** every ceil/floor uses the correct unit; no mixed-decimal arithmetic.

## 6. Residual-liveness rule (the design fix — DECIDE & FREEZE)
Risk: if all P is redeemed before maturity, `pSupplyAt == 0` at settle and the frozen residual would be
unreachable. **Chosen rule (frozen):** at `settle()`, if `pSupplyAt == 0`, the entire residual is credited to
the immutable `residualRecipient` (claimable via claimW/claimU). Otherwise residual is pro-rata P-redeemable.
This makes **ResidualLiveness** total: after settle, every asset is claimable by a valid claimant or the
residual recipient — never stranded. (Alternative considered: make `pSupplyAt==0` unreachable by requiring
`pSupply>0` to call settle; rejected because it can deadlock settlement. The recipient rule is liveness-safe.)

## 7. Put vault
Identical machine with collateral = USDC (6dp), strike asset = WETH (18dp). `exercise` pays WETH strike to
receive USDC collateral. All §5 invariants and all theorems are re-proved independently (no "mirror" hand-wave).

## 8. Reachability
Init state: all balances 0, `¬settled`, `now=0`. A state is *reachable* iff produced by a finite sequence of
valid transitions from init. All theorems quantify over **reachable** states (proved by induction: WF holds
at init and is preserved by every transition — see `lean/Split/Reachability.lean`).
