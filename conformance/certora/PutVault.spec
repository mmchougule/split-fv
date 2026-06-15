/*
 * PutVault.spec — Certora CVL aggregate rules for the SHIPPED PutVault.sol
 * =======================================================================
 *
 * First-class put proofs (T_PutSymmetry): roles swapped vs the call vault —
 * collateral = USDC, strike asset = WETH. Same aggregate properties:
 *   credits_le_holdings  -> T_Backing / T_ClaimNoDouble (put)
 *   residual_le_pool     -> T_ResidualBound             (put)
 *   no_stranded          -> T_ResidualLiveness          (put; SPEC §6, see GAP)
 *
 * PutVault.redeemP credits usdcCredit = floor(usdcPool*q/pSupplyAt) and
 * wethCredit = floor(wethPool*q/pSupplyAt). Same FLOOR pro-rata bound applies.
 *
 * Known gap: identical to the call vault — PutVault.sol has NO residualRecipient
 * and redeemP divides by pSupplyAt with no guard. `no_stranded_residualLiveness_SPEC_v6`
 * is EXPECTED TO FAIL until the §6 fix lands; `no_stranded_currentImpl_safety`
 * documents the weaker safety-only property the current code satisfies.
 *
 * Run:
 *   export CERTORAKEY=<key>
 *   certoraRun src/PutVault.sol \
 *     --verify PutVault:conformance/certora/PutVault.spec \
 *     --solc solc8.24 --optimistic_loop --rule_sanity basic \
 *     --msg "PutVault aggregate conformance"
 */

methods {
    function settled()   external returns (bool)    envfree;
    function usdcPool()  external returns (uint256) envfree;   // collateral pool (put)
    function wethPool()  external returns (uint256) envfree;   // strike-asset pool (put)
    function pSupplyAt() external returns (uint256) envfree;
    function strike()    external returns (uint256) envfree;
    function maturity()  external returns (uint256) envfree;
    function exerciseEnd() external returns (uint256) envfree;
    function claimableWeth(address) external returns (uint256) envfree;
    function claimableUsdc(address) external returns (uint256) envfree;
    function usdcRequired(uint256) external returns (uint256) envfree;
    function usdcOut(uint256) external returns (uint256) envfree;

    // External WETH/USDC tokens summarized NONDET (no concrete token linked;
    // assumption: standard non-malicious ERC20, see ASSUMPTIONS_AND_BOUNDARY.md).
    function _.transfer(address, uint256)        external => NONDET;
    function _.transferFrom(address, address, uint256) external => NONDET;
    function _.balanceOf(address) external => NONDET;
}

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
hook Sload uint256 v claimableWeth[KEY address a] {
    require to_mathint(v) <= sumClaimW;
}
hook Sload uint256 v claimableUsdc[KEY address a] {
    require to_mathint(v) <= sumClaimU;
}

invariant credit_sums_nonneg()
    sumClaimW >= 0 && sumClaimU >= 0;

/* residual_le_pool (put): credits never exceed the frozen pools. Collateral
 * pool is usdcPool, strike-asset pool is wethPool. */
invariant residual_le_pool_usdc()
    settled() => sumClaimU <= to_mathint(usdcPool())
    { preserved { requireInvariant credit_sums_nonneg(); } }

invariant residual_le_pool_weth()
    settled() => sumClaimW <= to_mathint(wethPool())
    { preserved { requireInvariant credit_sums_nonneg(); } }

/* credits_le_holdings (put). */
invariant credits_le_holdings_usdc()
    settled() => sumClaimU <= to_mathint(usdcPool());
invariant credits_le_holdings_weth()
    settled() => sumClaimW <= to_mathint(wethPool());

/* T_ClaimNoDouble (put). */
rule claim_zeroes_credit_usdc(address to) {
    env e;
    require to != 0;
    claimUsdc(e, to);
    assert claimableUsdc(e.msg.sender) == 0,
        "claimUsdc must zero the caller credit (no double claim)";
}
rule claim_zeroes_credit_weth(address to) {
    env e;
    require to != 0;
    claimWeth(e, to);
    assert claimableWeth(e.msg.sender) == 0,
        "claimWeth must zero the caller credit (no double claim)";
}
rule no_double_claim_usdc(address to) {
    env e;
    claimUsdc(e, to);
    env e2;
    require e2.msg.sender == e.msg.sender;
    claimUsdc@withrevert(e2, to);
    assert lastReverted, "second consecutive claimUsdc must revert (credit zeroed)";
}

/* no_stranded (put) — SPEC §6 form, EXPECTED TO FAIL until §6 fix (see GAP). */
rule no_stranded_residualLiveness_SPEC_v6() {
    require settled();
    require pSupplyAt() == 0;
    assert (usdcPool() == 0 || sumClaimU == to_mathint(usdcPool())),
        "SPEC §6: pSupplyAt==0 residual must be credited to residualRecipient";
    assert (wethPool() == 0 || sumClaimW == to_mathint(wethPool())),
        "SPEC §6: pSupplyAt==0 residual must be credited to residualRecipient";
}

/* current impl safety-only property (passing). */
rule no_stranded_currentImpl_safety() {
    env e;
    uint256 q;
    require settled();
    require pSupplyAt() == 0;
    redeemP@withrevert(e, q);
    assert lastReverted,
        "current impl: redeemP must revert when pSupplyAt==0 (no mis-credit)";
}
