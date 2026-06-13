# pragma version ^0.4.0
# @license MIT
# Minimal, non-malicious ERC20 for reference tests. No transfer hooks, no rebasing,
# no blacklist — matches the trusted-token assumption in ASSUMPTIONS_AND_BOUNDARY.

balanceOf: public(HashMap[address, uint256])
allowance: public(HashMap[address, HashMap[address, uint256]])
totalSupply: public(uint256)
decimals: public(uint8)

@deploy
def __init__(_decimals: uint8):
    self.decimals = _decimals

@external
def mint(to: address, amt: uint256):
    self.balanceOf[to] += amt
    self.totalSupply += amt

@external
def approve(spender: address, amt: uint256) -> bool:
    self.allowance[msg.sender][spender] = amt
    return True

@external
def transfer(to: address, amt: uint256) -> bool:
    assert self.balanceOf[msg.sender] >= amt, "insufficient"
    self.balanceOf[msg.sender] -= amt
    self.balanceOf[to] += amt
    return True

@external
def transferFrom(src: address, dst: address, amt: uint256) -> bool:
    assert self.balanceOf[src] >= amt, "insufficient"
    al: uint256 = self.allowance[src][msg.sender]
    assert al >= amt, "allowance"
    if al != max_value(uint256):
        self.allowance[src][msg.sender] = al - amt
    self.balanceOf[src] -= amt
    self.balanceOf[dst] += amt
    return True
