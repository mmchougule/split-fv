"""
Shared test harness for the Split settlement-core Vyper reference (call AND put).

Each test module mirrors a theorem name from docs/SAFETY_THEOREMS.md and exercises BOTH
vaults through the real transition surface (compiled Vyper, run on titanoboa's EVM).
No mocks of the vault itself — only the trusted ERC20 (MockERC20.vy) is a test double,
matching ASSUMPTIONS_AND_BOUNDARY (non-malicious, no hooks, no rebasing).

Framework: titanoboa (`boa`) — the framework the Vyper docs recommend. Contracts are
loaded with `boa.load(<file>.vy, *ctor_args)`; senders are simulated with
`boa.env.prank(addr)`; time advances with `boa.env.time_travel(...)`; reverts are
asserted with `boa.reverts()`.
"""
import os
import pytest
import boa

HERE = os.path.dirname(__file__)
VYPER_DIR = os.path.dirname(HERE)

CALL_SRC = os.path.join(VYPER_DIR, "SplitVaultReference.vy")
PUT_SRC = os.path.join(VYPER_DIR, "PutVaultReference.vy")
MOCK_SRC = os.path.join(HERE, "MockERC20.vy")

UNIT_W = 10 ** 18
UNIT_U = 10 ** 6


def expect_revert(fn, *args, **kwargs):
    """Assert that a transition reverts (None in the Lean model = revert here).

    Mirrors the boa `with boa.reverts(): ...` idiom but in callable form, so the
    theorem-named test modules can stay terse.
    """
    try:
        with boa.reverts():
            fn(*args, **kwargs)
    except Exception:
        # boa.reverts() re-raises if NO revert happened; surface that as the
        # explicit assertion error the suite expects.
        raise AssertionError("expected revert, but call succeeded")
    return True


class VaultEnv:
    """A deployed vault + its two ERC20s + convenience funders/senders.

    `kind` is "call" or "put". Field names below stay in the vault's frame:
      collat asset  = WETH (call) / USDC (put)
      strike asset  = USDC (call) / WETH (put)
    """

    def __init__(self, kind, strike, maturity, window, residual):
        self.kind = kind
        # decimals: weth 18, usdc 6
        self.weth = boa.load(MOCK_SRC, 18)
        self.usdc = boa.load(MOCK_SRC, 6)
        if kind == "call":
            # ctor(weth, usdc, strike, maturity, window, residual)
            self.vault = boa.load(
                CALL_SRC,
                self.weth.address, self.usdc.address, strike, maturity, window, residual,
            )
            self.collat_tok = self.weth   # WETH
            self.strike_tok = self.usdc   # USDC
        else:
            # ctor(usdc, weth, strike, maturity, window, residual)
            self.vault = boa.load(
                PUT_SRC,
                self.usdc.address, self.weth.address, strike, maturity, window, residual,
            )
            self.collat_tok = self.usdc   # USDC
            self.strike_tok = self.weth   # WETH

    # --- token plumbing ------------------------------------------------------
    def fund_collat(self, who, amt):
        self.collat_tok.mint(who, amt)
        with boa.env.prank(who):
            self.collat_tok.approve(self.vault.address, 2 ** 256 - 1)

    def fund_strike(self, who, amt):
        self.strike_tok.mint(who, amt)
        with boa.env.prank(who):
            self.strike_tok.approve(self.vault.address, 2 ** 256 - 1)

    def collat_bal_of(self, who):
        return self.collat_tok.balanceOf(who)

    def strike_bal_of(self, who):
        return self.strike_tok.balanceOf(who)

    def vault_collat_token_bal(self):
        return self.collat_tok.balanceOf(self.vault.address)

    def vault_strike_token_bal(self):
        return self.strike_tok.balanceOf(self.vault.address)

    # --- transitions ---------------------------------------------------------
    def mint(self, who, q):
        with boa.env.prank(who):
            return self.vault.mint(q)

    def redeemPair(self, who, q):
        with boa.env.prank(who):
            return self.vault.redeemPair(q)

    def exercise(self, who, q):
        with boa.env.prank(who):
            return self.vault.exercise(q)

    def settle(self, who=None):
        # settle() is only valid AFTER the exercise window closes (now >= exerciseEnd) so it can
        # never preempt an in-window exercise; advance there first.
        self.past_exercise_end()
        if who is None:
            return self.vault.settle()
        with boa.env.prank(who):
            return self.vault.settle()

    def redeemP(self, who, q):
        with boa.env.prank(who):
            return self.vault.redeemP(q)

    def claimW(self, who, to=None):
        with boa.env.prank(who):
            return self.vault.claimW(to or who)

    def claimU(self, who, to=None):
        with boa.env.prank(who):
            return self.vault.claimU(to or who)

    # --- views ---------------------------------------------------------------
    def v(self, name, *args):
        return getattr(self.vault, name)(*args)

    # --- time ----------------------------------------------------------------
    def warp(self, ts):
        """Advance chain time to >= ts so the next tx sees timestamp >= ts."""
        cur = boa.env.evm.patch.timestamp
        target = max(ts, cur + 1)
        boa.env.time_travel(seconds=target - cur)

    def into_exercise(self):
        self.warp(self.v("maturity"))

    def past_exercise_end(self):
        self.warp(self.v("exerciseEnd"))

    def required_in(self, q):
        """CEIL strike-asset a unit-q exercise must pay in."""
        if self.kind == "call":
            return self.v("usdcRequired", q)
        return self.v("wethRequired", q)


@pytest.fixture
def accounts():
    """Ten deterministic test addresses, mirroring the old eth-tester account list."""
    return [boa.env.generate_address(f"acct{i}") for i in range(10)]


@pytest.fixture
def make_vault(accounts):
    """Factory: make_vault(kind, strike=..., ...) -> VaultEnv. maturity in the future."""
    def _make(kind, strike=None, window=10_000, residual=None, maturity=None):
        now = boa.env.evm.patch.timestamp
        if maturity is None:
            maturity = now + 10_000
        if residual is None:
            residual = accounts[9]
        if strike is None:
            # call: USDC per WETH (6dp) -> 3000 USDC; put: WETH per USDC (18dp basis)
            strike = 3000 * UNIT_U if kind == "call" else (UNIT_W // 3000)
        return VaultEnv(kind, strike, maturity, window, residual)
    return _make


@pytest.fixture(params=["call", "put"])
def kind(request):
    return request.param
