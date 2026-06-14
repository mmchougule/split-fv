# Threat Model — Split settlement core

This document states, plainly, **who the attacker is, what they can do, what the settlement-core proofs
defend against, and what they explicitly do not.** It is the bridge between the machine-checked theorems
(`SAFETY_THEOREMS.md`) and the real deployment. Read it alongside `ASSUMPTIONS_AND_BOUNDARY.md`: that file
lists the *trust assumptions* the proofs rest on; this file lists the *adversary* and maps each attacker goal
to the theorem (or the explicit boundary) that answers it.

The scope is the **settlement core only**: `mint, redeemPair, exercise, settle, redeemP, claimW, claimU` on
the call vault and the put vault. Pricing, the quote signer, the keeper/roller, wrappers, routing, the gasless
facilitator/paymaster, and LP-pool economics are **out of scope** and have a separate safety story (see §5).

---

## 1. Assets at risk

The only assets the settlement core custodies are the two ERC-20 balances it holds:

- **Collateral** — WETH (18dp) on the call vault, USDC (6dp) on the put vault.
- **Strike asset** — USDC (6dp) on the call vault, WETH (18dp) on the put vault.

The attacker's economic goal is always one of: (a) **withdraw more than they are owed** (drain), (b) **make
the vault insolvent** so an honest holder cannot withdraw what they are owed (strand/brick), or (c) **make
settlement depend on a price they control** (oracle manipulation). The theorems are organized exactly around
denying (a), (b), and (c).

---

## 2. Attacker capabilities (what we assume the adversary CAN do)

We assume a strong, economically rational on-chain adversary:

1. **Call any settlement function, in any order, with any arguments, from any address, at any time.** This
   includes out-of-phase calls, zero/huge amounts, calls before maturity, after `exerciseEnd`, and repeated
   calls. The model treats every transition as a partial function `State → Option State` where `none` is a
   revert; the proofs quantify over *every* reachable sequence of calls (`Reachability.lean`).
2. **Hold, transfer, and split P and N tokens freely**, including holding only P, only N, or unequal amounts,
   and being the residual recipient.
3. **Reenter.** The adversary may deploy a contract that calls back into the vault during any external token
   transfer it can trigger (i.e. during a claim that sends tokens to it). Defended by the pull-claim,
   zero-before-send pattern (T_ClaimNoDouble) — credit is debited *before* the transfer, so a reentrant call
   sees zero remaining credit.
4. **Choose amounts to exploit rounding.** The adversary may pick `q` to try to round a strike payment down
   or a residual payout up. Defended by CEIL-in / FLOOR-out (T_RoundingMonotone): rounding can only ever
   leave *more* in the vault, never less; the only effect the adversary can achieve is stranding bounded dust
   (`< pSupplyAt` indivisible units), which is not extractable.
5. **Be the keeper / pricer / a privileged off-chain actor that misbehaves.** A malicious or absent keeper,
   or a pricer that signs a bad price, **cannot** break settlement-core safety — because no settlement
   transition reads a price, a quote, or a keeper input at all (T_OracleIndependence, structural). It can
   cost *traders* money (they may overpay for a position, or an ITM position may go un-exercised and forfeit),
   but it cannot make the vault pay out more than it holds or under-collateralize a claim. The economic
   correctness of the price is a pricing-layer property, out of scope here (§5).
6. **Front-run, reorder, and time transactions** within the bounds of normal block production (see §3 for the
   timestamp assumption).
7. **Grief the exercise window.** The adversary may try to MEV the exercise window (e.g. back-run an ITM
   exercise). This is an *economic* concern for traders, not a solvency concern: every exercise pays the full
   CEIL strike in before any collateral leaves (T_ExercisePays), so no sequence of exercises can drain.

---

## 3. Attacker limits (what we assume the adversary CANNOT do — the trust boundary)

These are the assumptions in `ASSUMPTIONS_AND_BOUNDARY.md`, restated as adversary limits. **An audit's job is
to attack exactly these** — if any fails, a theorem's hypothesis is void.

1. **Cannot subvert WETH/USDC.** The collateral and strike tokens behave as standard ERC-20s: `transfer` /
   `transferFrom` move exactly the stated amount or revert; no transfer hooks/callbacks, no rebasing, no
   fee-on-transfer, no arbitrary mint. Recipient *blacklisting* is tolerated only because the pull-claim
   pattern means a blocked recipient strands **only their own credit**, never the vault or other holders.
2. **Cannot forge integer arithmetic.** Solidity ≥0.8 reverts on overflow; Vyper bounds are explicit; the
   Lean model is over `Nat` (no overflow by construction) and the conformance layer enforces the
   bounded-domain match. The adversary cannot wrap a balance around.
3. **Cannot move the block clock outside consensus tolerance.** Phase guards read `now` (the block
   timestamp), which is assumed monotonic and within normal validator tolerance. The adversary can nudge
   `now` by a few seconds (and the proofs are robust to that — phases are half-open intervals), but cannot
   set it arbitrarily.
4. **Cannot change the immutable parameters** `strike`, `maturity`, `exerciseEnd`, `residualRecipient` after
   deploy.

If all of §3 holds, the §2 adversary cannot achieve drain, strand, or oracle-dependence. That implication is
what the theorems machine-check.

---

## 4. Attack → defense map

Each row is an attacker goal and the theorem (or boundary) that denies it. Theorem statements live in
`SAFETY_THEOREMS.md`; the per-layer proof links live in `conformance/THEOREM_MAP.md`.

| # | Attacker goal | Concrete attempt | Denied by |
|---|---|---|---|
| A1 | Withdraw more than the vault holds | redeemP/claim past the pool; mint debt without collateral | **T_Backing**, **T_Conservation** |
| A2 | Take collateral without paying | call `exercise` and skip / underpay the strike | **T_ExercisePays** (CEIL strike in before collateral out) |
| A3 | Overdraw the residual pool | redeemP a larger pro-rata share than the frozen pool allows | **T_ResidualBound** |
| A4 | Drain via rounding | pick `q` to round strike down / residual up | **T_RoundingMonotone** (CEIL-in/FLOOR-out; only strands dust) |
| A5 | Call a transition in the wrong phase | exercise before maturity; redeemP before settle; mint after settle | **T_PhaseSafety** (out-of-phase ⇒ revert) |
| A6 | Make settlement depend on a price they control | feed/oracle-manipulate a price into settlement | **T_OracleIndependence** (structural: no price input exists) |
| A7 | Double-claim / reentrancy-drain a credit | reenter `claimW`/`claimU` during the outgoing transfer | **T_ClaimNoDouble** (zero-before-send) |
| A8 | Break the put vault while the call is safe | run A1–A7 against the put vault | **T_PutSymmetry** (all of A1–A7 re-proved, roles swapped) |
| A9 | Strand meaningful funds forever | redeem all P before maturity so the residual is unreachable | **T_ResidualLiveness** + the §6 residual-recipient terminal rule |

> Note on A1 vs the Lean model: the Lean model tracks **ghost aggregate credit totals**
> (`totalClaimW`/`totalClaimU`) rather than the full per-address `claimW/claimU` map. This is the *aggregate*
> claim-safety statement (Σ credits ≤ holdings), which is the property that matters for solvency. The
> per-address no-double-claim guarantee (A7) is enforced structurally by zero-before-send and is checked
> against the **shipped Solidity** in the Certora `credits_le_holdings` rule and the Halmos
> `check_T_ClaimNoDouble` over the real `mapping(address => uint)` claim ledger. This split is called out
> honestly in `THEOREM_MAP.md`; it is a modeling boundary, not a gap in the defended property.

---

## 5. Explicitly NOT defended by the settlement-core proofs

These are real risks. They are **out of scope for the settlement-core proofs** and have their own safety
story. We list them so no reader mistakes "settlement is proven safe" for "the whole product is proven safe."

- **Pricing correctness.** What a P or N costs to buy/sell is set by an **off-chain pricer that signs an
  EIP-712 quote**, verified on-chain *at trade time* — not at settlement. A mispriced quote is a loss for the
  market maker (or an arbitrage gain for a trader), never a solvency event for the vault. The vault settles on
  *balances and exercises*, never on the quote. "Oracle-free" means **settlement reads no price**; it does
  **not** mean "no price exists anywhere in the product."
- **Keeper / roller liveness and correctness.** Daily desks rely on a keeper to roll series and (ideally) to
  auto-exercise ITM positions at expiry. An absent or buggy keeper can cause a trader to **forfeit an
  un-exercised ITM position** to the P holder. This is an economic UX failure, captured by the protocol's own
  rules (un-exercised N forfeits to P), not a drain or under-collateralization. Auto-exercise is a known
  operational gap on the product side and is not a settlement-core theorem.
- **The gasless facilitator / paymaster / bundler** (gasless execution). It can fail to relay a transaction
  (liveness), but cannot alter settlement accounting.
- **MEV in the exercise window.** Reordering exercises is economically relevant to traders; it cannot drain
  (every exercise is fully paid, T_ExercisePays) or under-collateralize.
- **Wrappers, routing, referrals, market-making, distribution.** None are read by settlement.
- **LP-pool return profile.** *Who profits* from writing covered calls is an economic question, not a
  settlement-safety one. The *accounting* safety of LP deposits/redemptions (no overdraw, conservation) is in
  scope via the same backing/claim invariants; the *yield/return* is not.
- **Governance / key compromise** of owner roles. Owner roles in the shipped product rotate keys and route
  inventory; they have **no withdraw path that bypasses the claim ledger** in the verified core. Compromise of
  off-chain signer/keeper keys is a pricing/liveness risk per the rows above, not a settlement-core drain.
- **Economic demand / business viability.** Out of scope entirely — not a safety property.

---

## 6. Why "oracle-free" is the load-bearing claim

A price oracle is the single most common drain vector in DeFi options/lending (manipulate the price feed,
then borrow/exercise against the manipulated value). Split's settlement core removes that vector **by
construction, not by assumption**: there is no price *parameter* to manipulate. T_OracleIndependence proves
this **structurally** — at the type level in Lean (the transition functions have no price argument and read
no price field) and at the bytecode level in the conformance layer (the settlement selectors make no external
call to a price/oracle/DEX address). This is *not* the weaker "settlement happens to be time-invariant"
argument; it is the absence of a price input from the surface itself. That is the property an external reviewer
should check first, because everything else (backing, conservation, no-overpay) is standard accounting once
the price-manipulation vector is gone.
