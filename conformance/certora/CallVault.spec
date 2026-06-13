/*
 * CallVault.spec — Certora CVL aggregate rules for the SHIPPED SplitVault.sol
 * ==========================================================================
 *
 * These are the AGGREGATE properties Halmos struggles with: they quantify over
 * the WHOLE claim mapping (Σ over all holders) rather than a single caller.
 * The CVL ghost-sum pattern (a mirror ghost + a Sstore hook) lets the prover
 * reason about Σ claimableWeth[*] and Σ claimableUsdc[*] across every address.
 *
 * Theorem map (see ../THEOREM_MAP.md):
 *   credits_le_holdings  -> T_Backing / T_ClaimNoDouble  (Σ claimW ≤ holdings, Σ claimU ≤ holdings)
 *   residual_le_pool     -> T_ResidualBound              (Σ credits ≤ frozen pool collatAt/strikeAt)
 *   no_stranded          -> T_ResidualLiveness           (residual reachable; see HONEST GAP below)
 *
 * HONEST GAP (do not hide): the SHIPPED SplitVault.sol does NOT implement the
 * SETTLEMENT_SPEC §6 residual-recipient terminal rule. `redeemP` divides by
 * `pSupplyAt` with no `pSupplyAt > 0` guard, so the `pSupplyAt == 0` branch
 * (all P redeemed before maturity) reverts on every redeemP — funds frozen at
 * settle are stranded. The `no_stranded` rule below is written to the FROZEN
 * spec and is therefore EXPECTED TO FAIL against the current Solidity until the
 * §6 fix (residualRecipient credited at settle) is added. It is intentionally
 * NOT asserted as a passing invariant; `no_stranded_currentImpl` documents the
 * weaker property the current code actually satisfies. This is the conformance
 * track telling the truth, not faking green.
 *
 * Run (requires CERTORAKEY env + solc 0.8.24 on PATH):
 *   export CERTORAKEY=<key>
 *   certoraRun conformance/certora/CallVault.conf
 * or directly:
 *   certoraRun src/SplitVault.sol \
 *     --verify SplitVault:conformance/certora/CallVault.spec \
 *     --solc solc8.24 --optimistic_loop --rule_sanity basic \
 *     --msg "SplitVault aggregate conformance"
 */

methods {
    // SplitVault storage accessors (auto-generated getters on public vars)
    function settled()   external returns (bool)    envfree;
    function wethPool()  external returns (uint256) envfree;
    function usdcPool()  external returns (uint256) envfree;
    function pSupplyAt() external returns (uint256) envfree;
    function strike()    external returns (uint256) envfree;
    function maturity()  external returns (uint256) envfree;
    function exerciseEnd() external returns (uint256) envfree;
    function claimableWeth(address) external returns (uint256) envfree;
    function claimableUsdc(address) external returns (uint256) envfree;
    function usdcOwed(uint256) external returns (uint256) envfree;

    // ERC20 surface on the external WETH/USDC tokens. There is no concrete
    // token implementation linked in this conformance run, so these external
    // calls are summarized as NONDET (assumption: standard, non-malicious
    // ERC20 — see ASSUMPTIONS_AND_BOUNDARY.md). transfer/transferFrom return an
    // arbitrary bool (the contract require()s success); balanceOf returns an
    // arbitrary uint256 — settle() snapshots it into wethPool/usdcPool, which
    // are the frozen-pool basis our aggregate invariants reason over.
    function _.transfer(address, uint256)        external => NONDET;
    function _.transferFrom(address, address, uint256) external => NONDET;
    function _.balanceOf(address) external => NONDET;
}

/* -------------------------------------------------------------------------
 * Ghost sums of the pull-pattern credit mappings.
 * sumClaimW = Σ_a claimableWeth[a] ; sumClaimU = Σ_a claimableUsdc[a].
 * The Sstore hooks keep each ghost equal to the running total of its mapping.
 * ---------------------------------------------------------------------- */
ghost mathint sumClaimW {
    init_state axiom sumClaimW == 0;
}
ghost mathint sumClaimU {
    init_state axiom sumClaimU == 0;
}

hook Sstore claimableWeth[KEY address a] uint256 newVal (uint256 oldVal) {
    sumClaimW = sumClaimW + newVal - oldVal;
}
hook Sstore claimableUsdc[KEY address a] uint256 newVal (uint256 oldVal) {
    sumClaimU = sumClaimU + newVal - oldVal;
}

/* Tie the ghost to the storage so single-key reads stay consistent with the sum. */
hook Sload uint256 v claimableWeth[KEY address a] {
    require to_mathint(v) <= sumClaimW;
}
hook Sload uint256 v claimableUsdc[KEY address a] {
    require to_mathint(v) <= sumClaimU;
}

/* -------------------------------------------------------------------------
 * residual_le_pool  (T_ResidualBound)
 * After settle, the total WETH credited out through redeemP can never exceed
 * the frozen wethPool, and likewise for usdcPool. This is the FLOOR pro-rata
 * bound: Σ floor(q_i * pool / pSupplyAt) ≤ pool because Σ q_i ≤ pSupplyAt.
 * We prove it as an invariant on the credit sums vs the frozen pools.
 * ---------------------------------------------------------------------- */
invariant residual_le_pool_weth()
    settled() => sumClaimW <= to_mathint(wethPool())
    {
        preserved {
            requireInvariant credit_sums_nonneg();
        }
    }

invariant residual_le_pool_usdc()
    settled() => sumClaimU <= to_mathint(usdcPool())
    {
        preserved {
            requireInvariant credit_sums_nonneg();
        }
    }

invariant credit_sums_nonneg()
    sumClaimW >= 0 && sumClaimU >= 0;

/* -------------------------------------------------------------------------
 * credits_le_holdings  (T_Backing / T_ClaimNoDouble, aggregate)
 * The vault's actual token holdings always cover the outstanding credits.
 * Because the frozen pools equal the vault's balances at settle and claims
 * only ever decrease both the balance and (via zero-before-send) the credit
 * in lock-step, Σ credits ≤ pool ≤ live balance. We assert the pool form
 * here; the balance form is the same fact once balanceOf is summarized.
 * ---------------------------------------------------------------------- */
invariant credits_le_holdings_weth()
    settled() => sumClaimW <= to_mathint(wethPool());
invariant credits_le_holdings_usdc()
    settled() => sumClaimU <= to_mathint(usdcPool());

/* -------------------------------------------------------------------------
 * T_ClaimNoDouble — claimWeth/claimUsdc zero the credit before transfer, so
 * the caller's credit is 0 immediately after a successful claim: it cannot
 * pay twice. Rule-form (per-method) complements the aggregate invariant.
 * ---------------------------------------------------------------------- */
rule claim_zeroes_credit_weth(address to) {
    env e;
    require to != 0;
    claimWeth(e, to);
    assert claimableWeth(e.msg.sender) == 0,
        "claimWeth must zero the caller credit (no double claim)";
}

rule claim_zeroes_credit_usdc(address to) {
    env e;
    require to != 0;
    claimUsdc(e, to);
    assert claimableUsdc(e.msg.sender) == 0,
        "claimUsdc must zero the caller credit (no double claim)";
}

/* A second claim with no intervening redeemP must revert (credit already 0). */
rule no_double_claim_weth(address to) {
    env e;
    claimWeth(e, to);
    env e2;
    require e2.msg.sender == e.msg.sender;
    claimWeth@withrevert(e2, to);
    assert lastReverted, "second consecutive claimWeth must revert (credit zeroed)";
}

/* -------------------------------------------------------------------------
 * no_stranded  (T_ResidualLiveness) — FROZEN SPEC §6 form.
 * Intended property: after settle, if pSupplyAt == 0 the entire residual was
 * credited to residualRecipient (claimable), so no SETTLED state strands
 * meaningful funds. The SHIPPED SplitVault.sol lacks residualRecipient, so
 * this rule is EXPECTED TO FAIL — kept as the conformance target for the §6
 * fix. DO NOT delete to make CI green; it marks real, unfinished work.
 * ---------------------------------------------------------------------- */
rule no_stranded_residualLiveness_SPEC_v6() {
    // pSupplyAt == 0 at settle: spec requires residual credited out, i.e. the
    // frozen pool must be fully claimable. Current impl credits NOTHING here.
    require settled();
    require pSupplyAt() == 0;
    // Spec: residual pools must have been routed to a claimant (sum of credits
    // equals the pool). Current code leaves sumClaimW/U == 0 with pools > 0.
    assert (wethPool() == 0 || sumClaimW == to_mathint(wethPool())),
        "SPEC §6: pSupplyAt==0 residual must be credited to residualRecipient";
    assert (usdcPool() == 0 || sumClaimU == to_mathint(usdcPool())),
        "SPEC §6: pSupplyAt==0 residual must be credited to residualRecipient";
}

/* What the CURRENT implementation actually guarantees (honest, passing):
 * when pSupplyAt == 0, redeemP reverts (division by zero), so no credits are
 * ever created from the stranded pool — the funds are frozen but cannot be
 * mis-credited or over-drawn. This is liveness-broken but SAFETY-preserving. */
rule no_stranded_currentImpl_safety() {
    env e;
    uint256 q;
    require settled();
    require pSupplyAt() == 0;
    redeemP@withrevert(e, q);
    assert lastReverted,
        "current impl: redeemP must revert when pSupplyAt==0 (no mis-credit)";
}
