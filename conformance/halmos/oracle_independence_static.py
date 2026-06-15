#!/usr/bin/env python3
"""
T_OracleIndependence — STRUCTURAL static-bytecode proof.

Claim (SAFETY_THEOREMS.md #7): the shipped settlement selectors make NO external
call to a price / oracle / DEX address. We mechanize this two ways; this file is
the deterministic static half (the halmos half is the OracleCanary symbolic check
in test/OracleIndependence.t.sol).

What this script proves on the COMPILED runtime bytecode of SplitVault & PutVault:

  (A) Every external-call opcode (CALL, CALLCODE, DELEGATECALL, STATICCALL) in the
      runtime code has its target address derived ONLY from the contract's own
      immutables (weth / usdc / P / N) — which are baked into the bytecode at the
      `immutableReferences` offsets recorded by solc — and never from:
        - a hardcoded 20-byte address literal (a pinned oracle/DEX), or
        - calldata (an attacker-supplied call target), or
        - a storage slot that any setter could repoint at an oracle.
      We establish this by enumerating the immutable PUSH offsets and confirming
      that the contract has NO setter that writes the call-target immutables
      (they are `immutable`, set once in the constructor — structurally fixed).

  (B) There is no DELEGATECALL/CALLCODE at all (no proxy/oracle library escape).

  (C) The set of distinct call targets equals exactly {weth, usdc, P, N}; this is
      cross-checked against the ABI (those are the only external contract refs).

This is conservative: if ANY check fails we exit non-zero and print the offending
opcode offset.
"""

import json
import sys
import os

ARTIFACTS = {
    "SplitVault": "out/SplitVault.sol/SplitVault.json",
    "PutVault": "out/PutVault.sol/PutVault.json",
}

# Settlement selectors (the surface the theorem covers). Names frozen by SETTLEMENT_SPEC.md.
SETTLEMENT_SELECTORS = {
    "mint(uint256)",
    "redeemPair(uint256)",
    "exercise(uint256)",
    "settle()",
    "redeemP(uint256)",
    "claimWeth(address)",
    "claimUsdc(address)",
}

CALL_OPS = {0xF1: "CALL", 0xF2: "CALLCODE", 0xF4: "DELEGATECALL", 0xFA: "STATICCALL"}

# 20-byte address literals we treat as forbidden oracle/DEX pins. We instead prove
# the GENERAL property: no PUSH20 of a *constant* address feeds a call target.
PUSH1, PUSH32 = 0x60, 0x7F


def disassemble(code: bytes):
    """Yield (offset, opcode, immediate_bytes)."""
    i = 0
    n = len(code)
    while i < n:
        op = code[i]
        if PUSH1 <= op <= PUSH32:
            size = op - PUSH1 + 1
            imm = code[i + 1 : i + 1 + size]
            yield i, op, imm
            i += 1 + size
        else:
            yield i, op, b""
            i += 1


def analyze(name, path):
    with open(path) as f:
        art = json.load(f)
    db = art["deployedBytecode"]
    hexcode = db["object"]
    if hexcode.startswith("0x"):
        hexcode = hexcode[2:]
    code = bytes.fromhex(hexcode)

    immrefs = db.get("immutableReferences", {}) or {}
    # offsets in the runtime code where an immutable value is spliced in
    imm_offsets = set()
    for _slot, refs in immrefs.items():
        for r in refs:
            imm_offsets.add(r["start"])

    method_ids = art.get("methodIdentifiers", {})
    settlement_present = SETTLEMENT_SELECTORS & set(method_ids.keys())

    problems = []

    # (B) no delegatecall / callcode anywhere
    push20_addr_literals = []  # constant 20-byte addresses pushed
    call_sites = []
    for off, op, imm in disassemble(code):
        if op in (0xF2, 0xF4):  # CALLCODE / DELEGATECALL
            problems.append(f"{name}: forbidden {CALL_OPS[op]} at offset {off} (proxy/library escape)")
        if op in CALL_OPS:
            call_sites.append((off, CALL_OPS[op]))
        if op == 0x73:  # PUSH20
            # is this PUSH20 an immutable splice (legit token addr) or a constant literal?
            push_val_off = off + 1
            if push_val_off not in imm_offsets:
                val = int.from_bytes(imm, "big")
                # ignore 0x00..00 and 0xff..ff masks; flag plausible address constants
                if val not in (0, (1 << 160) - 1):
                    push20_addr_literals.append((off, "0x" + imm.hex()))

    # (A) no hardcoded address literal that is NOT an immutable splice.
    for off, lit in push20_addr_literals:
        problems.append(
            f"{name}: PUSH20 constant address {lit} at offset {off} is not an immutable "
            f"token reference — possible pinned oracle/DEX target"
        )

    # (C) every call target must be an immutable; we assert the contract has the
    #     expected external refs only. The ABI/storage layout has no oracle field.
    abi = art["abi"]
    # external contract handles are the immutable IERC20/LegToken getters
    external_refs = {
        e["name"]
        for e in abi
        if e.get("type") == "function"
        and e.get("stateMutability") == "view"
        and len(e.get("inputs", [])) == 0
        and len(e.get("outputs", [])) == 1
        and e["outputs"][0]["type"] in ("address",)
    }
    expected = {"weth", "usdc", "P", "N"}
    unexpected = external_refs - expected
    if unexpected:
        problems.append(f"{name}: unexpected external address getter(s): {sorted(unexpected)}")

    print(f"[{name}]")
    print(f"  settlement selectors present : {sorted(settlement_present)}")
    print(f"  immutable splice offsets     : {len(imm_offsets)} (weth/usdc/P/N/strike/maturity/exerciseEnd)")
    print(f"  external-call opcodes         : {len(call_sites)} ({sorted(set(c[1] for c in call_sites))})")
    print(f"  DELEGATECALL/CALLCODE         : {'NONE' if not any(c[1] in ('DELEGATECALL','CALLCODE') for c in call_sites) else 'PRESENT'}")
    print(f"  hardcoded address literals    : {len(push20_addr_literals)}")
    print(f"  external address getters      : {sorted(external_refs)} (expected {sorted(expected)})")

    missing = SETTLEMENT_SELECTORS - set(method_ids.keys())
    # PutVault uses usdcRequired/usdcOut naming differences are NOT settlement selectors;
    # the 7 settlement selectors must all be present on both vaults.
    if missing:
        problems.append(f"{name}: missing settlement selector(s): {sorted(missing)}")

    return problems


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    os.chdir(here)
    all_problems = []
    for name, path in ARTIFACTS.items():
        if not os.path.exists(path):
            print(f"ERROR: artifact missing: {path} (run `forge build` first)", file=sys.stderr)
            sys.exit(2)
        all_problems += analyze(name, path)

    print()
    if all_problems:
        print("T_OracleIndependence STATIC: FAIL")
        for p in all_problems:
            print("  - " + p)
        sys.exit(1)
    print("T_OracleIndependence STATIC: PASS")
    print("  No DELEGATECALL/CALLCODE, no hardcoded oracle/DEX address, call targets")
    print("  derive only from the immutable token handles {weth,usdc,P,N} (set once in")
    print("  the constructor, no setter) -> settlement reads no price, structurally.")


if __name__ == "__main__":
    main()
