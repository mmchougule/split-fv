"""
Shared test harness for the Split settlement-core Vyper reference (call AND put).

Each test module mirrors a theorem name from docs/SAFETY_THEOREMS.md and exercises BOTH
vaults through the real transition surface (compiled Vyper, run on py-evm via eth-tester).
No mocks of the vault itself — only the trusted ERC20 (MockERC20.vy) is a test double,
matching ASSUMPTIONS_AND_BOUNDARY (non-malicious, no hooks, no rebasing).
"""
import os
import pytest
import vyper
from web3 import Web3
from eth_tester import EthereumTester, PyEVMBackend
from web3.providers.eth_tester import EthereumTesterProvider

HERE = os.path.dirname(__file__)
VYPER_DIR = os.path.dirname(HERE)

UNIT_W = 10 ** 18
UNIT_U = 10 ** 6


from web3.exceptions import ContractLogicError
from eth_tester.exceptions import TransactionFailed


def expect_revert(fn, *args, **kwargs):
    """Assert that a transition reverts (None in the Lean model = revert here)."""
    try:
        fn(*args, **kwargs)
    except (ContractLogicError, TransactionFailed):
        return True
    raise AssertionError("expected revert, but call succeeded")


def _compile(path):
    src = open(path).read()
    return vyper.compile_code(src, output_formats=["abi", "bytecode"])


@pytest.fixture(scope="session")
def artifacts():
    return {
        "mock": _compile(os.path.join(HERE, "MockERC20.vy")),
        "call": _compile(os.path.join(VYPER_DIR, "SplitVaultReference.vy")),
        "put": _compile(os.path.join(VYPER_DIR, "PutVaultReference.vy")),
    }


@pytest.fixture
def chain():
    return EthereumTester(PyEVMBackend())


@pytest.fixture
def w3(chain):
    return Web3(EthereumTesterProvider(chain))


@pytest.fixture
def accounts(w3):
    return list(w3.eth.accounts)


def _deploy(w3, art, *ctor):
    C = w3.eth.contract(abi=art["abi"], bytecode=art["bytecode"])
    tx = C.constructor(*ctor).transact({"from": w3.eth.accounts[0]})
    rc = w3.eth.wait_for_transaction_receipt(tx)
    return w3.eth.contract(address=rc.contractAddress, abi=art["abi"])


def _now(w3):
    return w3.eth.get_block("latest")["timestamp"]


def warp_to(chain, w3, ts):
    """Advance chain time to >= ts and mine, so the next tx sees timestamp >= ts."""
    cur = _now(w3)
    target = max(ts, cur + 1)
    chain.time_travel(target)
    chain.mine_block()


class VaultEnv:
    """A deployed vault + its two ERC20s + convenience funders/senders.

    `kind` is "call" or "put". Field names below stay in the vault's frame:
      collat asset  = WETH (call) / USDC (put)
      strike asset  = USDC (call) / WETH (put)
    """

    def __init__(self, chain, w3, artifacts, kind, strike, maturity, window, residual):
        self.chain = chain
        self.w3 = w3
        self.kind = kind
        self.acct0 = w3.eth.accounts[0]
        # decimals: weth 18, usdc 6
        self.weth = _deploy(w3, artifacts["mock"], 18)
        self.usdc = _deploy(w3, artifacts["mock"], 6)
        if kind == "call":
            # ctor(weth, usdc, strike, maturity, window, residual)
            self.vault = _deploy(
                w3, artifacts["call"],
                self.weth.address, self.usdc.address, strike, maturity, window, residual,
            )
            self.collat_tok = self.weth   # WETH
            self.strike_tok = self.usdc   # USDC
        else:
            # ctor(usdc, weth, strike, maturity, window, residual)
            self.vault = _deploy(
                w3, artifacts["put"],
                self.usdc.address, self.weth.address, strike, maturity, window, residual,
            )
            self.collat_tok = self.usdc   # USDC
            self.strike_tok = self.weth   # WETH

    # --- token plumbing ------------------------------------------------------
    def fund_collat(self, who, amt):
        self.collat_tok.functions.mint(who, amt).transact({"from": self.acct0})
        self.collat_tok.functions.approve(self.vault.address, 2 ** 256 - 1).transact({"from": who})

    def fund_strike(self, who, amt):
        self.strike_tok.functions.mint(who, amt).transact({"from": self.acct0})
        self.strike_tok.functions.approve(self.vault.address, 2 ** 256 - 1).transact({"from": who})

    def collat_bal_of(self, who):
        return self.collat_tok.functions.balanceOf(who).call()

    def strike_bal_of(self, who):
        return self.strike_tok.functions.balanceOf(who).call()

    def vault_collat_token_bal(self):
        return self.collat_tok.functions.balanceOf(self.vault.address).call()

    def vault_strike_token_bal(self):
        return self.strike_tok.functions.balanceOf(self.vault.address).call()

    # --- transitions ---------------------------------------------------------
    def mint(self, who, q):
        return self.vault.functions.mint(q).transact({"from": who})

    def redeemPair(self, who, q):
        return self.vault.functions.redeemPair(q).transact({"from": who})

    def exercise(self, who, q):
        return self.vault.functions.exercise(q).transact({"from": who})

    def settle(self, who=None):
        return self.vault.functions.settle().transact({"from": who or self.acct0})

    def redeemP(self, who, q):
        return self.vault.functions.redeemP(q).transact({"from": who})

    def claimW(self, who, to=None):
        return self.vault.functions.claimW(to or who).transact({"from": who})

    def claimU(self, who, to=None):
        return self.vault.functions.claimU(to or who).transact({"from": who})

    # --- views ---------------------------------------------------------------
    def v(self, name, *args):
        return getattr(self.vault.functions, name)(*args).call()

    # --- time ----------------------------------------------------------------
    def warp(self, ts):
        warp_to(self.chain, self.w3, ts)

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
def make_vault(chain, w3, artifacts, accounts):
    """Factory: make_vault(kind, strike=..., ...) -> VaultEnv. maturity in the future."""
    def _make(kind, strike=None, window=10_000, residual=None, maturity=None):
        now = _now(w3)
        if maturity is None:
            maturity = now + 10_000
        if residual is None:
            residual = accounts[9]
        if strike is None:
            # call: USDC per WETH (6dp) -> 3000 USDC; put: WETH per USDC (18dp basis)
            strike = 3000 * UNIT_U if kind == "call" else (UNIT_W // 3000)
        return VaultEnv(chain, w3, artifacts, kind, strike, maturity, window, residual)
    return _make


@pytest.fixture(params=["call", "put"])
def kind(request):
    return request.param
