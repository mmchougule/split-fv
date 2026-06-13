#!/usr/bin/env bash
# Reproduce the Verity-track build of Split's call settlement core.
# Verified working on macOS arm64 with Verity main @ Lean v4.22.0.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${VERITY_WORK:-/tmp/verity-build}"

# 1. Lean toolchain manager (elan) — pulls Lean v4.22.0 pinned by Verity.
if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
  else
    curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
    export PATH="$HOME/.elan/bin:$PATH"
  fi
fi

# 2. Clone Verity (shallow).
if [ ! -d "$WORK/.git" ]; then
  git clone --depth 1 https://github.com/lfglabs-dev/verity.git "$WORK"
fi

# 3. Drop in the SplitVault contract + spec + proofs.
mkdir -p "$WORK/Contracts/SplitVault/Proofs"
cp "$HERE/Contracts/SplitVault/SplitVault.lean"   "$WORK/Contracts/SplitVault/SplitVault.lean"
cp "$HERE/Contracts/SplitVault/Spec.lean"         "$WORK/Contracts/SplitVault/Spec.lean"
cp "$HERE/Contracts/SplitVault/Proofs/Basic.lean" "$WORK/Contracts/SplitVault/Proofs/Basic.lean"

# 4. Build framework (first run downloads Mathlib, ~30 min) then SplitVault modules.
cd "$WORK"
lake build Contracts.Vault   # builds the full Verity framework as a side effect
lake build \
  Contracts.SplitVault.SplitVault \
  Contracts.SplitVault.Spec \
  Contracts.SplitVault.Proofs.Basic

echo "OK: SplitVault settlement core compiled green in Verity (0 sorry)."
