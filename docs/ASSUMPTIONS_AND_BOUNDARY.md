# Assumptions & Boundary

This file lists the **trust assumptions** the settlement-core proofs rest on and the **out-of-scope** surface
they must not depend on. For the adversary itself — what an attacker can do, and which theorem denies each
attack — see [`THREAT_MODEL.md`](THREAT_MODEL.md). The two are complementary: an assumption here is exactly an
*attacker limit* there, and an audit's job is to attack these assumptions.

## Trusted assumptions (the proof relies on these; an audit must attack them)
- **ERC-20 semantics** for WETH and USDC are standard: `transfer`/`transferFrom` move exactly the stated
  amount or revert; balances are non-negative integers.
- **WETH/USDC are immutable and non-malicious:** no transfer hooks/callbacks, no rebasing, no fee-on-transfer.
  Recipient blacklisting is tolerated only because settlement uses the **pull-claim** pattern (a blocked
  recipient strands only their own credit, never the vault).
- **Block timestamps** are monotonic and within normal consensus tolerance (phase guards use `now`).
- **Integer arithmetic** is checked: Solidity ≥0.8 reverts on overflow; Vyper bounds are explicit; the Lean
  model is over `Nat` (no overflow) and the conformance layer enforces the bounded-domain match.
- **Immutable parameters.** `strike`, `maturity`, `exerciseEnd`, and `residualRecipient` are set at deploy and
  never change. The residual-liveness terminal rule (SETTLEMENT_SPEC §6) assumes `residualRecipient` is a
  valid, non-reverting claimant address (it can still only ever withdraw via the pull-claim ledger).

## Out of scope (separate safety story — must NOT be relied on by the settlement proof)
- Pricing / the off-chain quote signer (NAV, ask/bid). Settlement reads balances + exercise, never a price.
- Keeper / roller, wrappers, routing, referrals, market-making, distribution.
- The gasless facilitator / paymaster / bundler (gasless execution layer).
- LP pool economics (who profits) — the *accounting* safety of deposits/redemptions is in scope via the
  same claim/backing invariants; the *return profile* is not a settlement-safety property.

## What "oracle-free" means precisely
**Settlement** (mint/redeemPair/exercise/settle/redeemP/claim) takes no ETH/USD price input and makes no
oracle/DEX read — this is theorem **T_OracleIndependence**, proved *structurally* (the absence of a price
input from the transition surface, not "settlement happens to be time-invariant"; see `SAFETY_THEOREMS.md`
§7). **Pricing** (what a claim costs to buy) uses an off-chain pricer-signed EIP-712 quote, verified on-chain
*at trade time*, never at settlement. A mispriced quote is a loss for the market maker, not a solvency event
for the vault. Prices exist in the product; *settlement correctness* is independent of any
price. This is the load-bearing claim, because the price feed is the usual drain vector in DeFi
options/lending, and here there is no price feed to manipulate.
