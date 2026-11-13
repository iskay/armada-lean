-- ABOUTME: The yield adapter's, the yield vault's and the vault's Aave position's state in the CCTP model.
-- ABOUTME: Vault shares are balances of the vault's own token in the ledger; conversion reuses the pool model's vault math.
/-
  ArmadaLean.Cctp.Yield — the yield adapter, the vault and its Aave position.

  Design record: model sheet v2.1 §4.6 and §5.4 (decision DQ-10 (a): the full vault in
  scope). The vault's share token (ayUSDC) is the vault's own ERC-20, so shares are
  balances of token `vault.self` in the chain's `Ledger` (`ArmadaLean.Cctp.Tokens`). The
  share / asset conversion and the `LOCKED_SHARES` lock are the pool model's
  (`ArmadaLean.Yield.Vault`: `c2s`, `c2a`, `LOCKED_SHARES`), pinned to the same vault blob
  (8859da5c at armada-poc 64436c14). Aave is an environment: the vault's position has a
  value that environment steps may raise (gains) or lower (losses), and a pause and a
  liquidity flag. The yield steps come in a later commit.
-/
import ArmadaLean.Cctp.Types
import ArmadaLean.Yield.Vault

namespace ArmadaLean.Cctp

/-- The yield adapter (ArmadaYieldAdapter.sol:46-63): its own address, the pool it serves
    (owner-set, unchecked, ArmadaYieldAdapter.sol:120-123), its owner, and the immutable
    USDC, vault and registry addresses. Its token balances are in the ledger. -/
structure AdapterState where
  self : Term
  owner : Term
  privacyPool : Term
  usdc : Term
  vault : Term
  registry : Term

/-- The yield vault (ArmadaYieldVault.sol:81-131): its own address (also its share token),
    its owner and fee module, the immutable treasury and underlying token, the yield-fee
    rate and harvest time, and its fee accounting (cumulative and accrued protocol fee,
    total deposited and paid out, the yield high-water mark). -/
structure VaultState where
  self : Term
  owner : Term
  feeModule : Option Term
  treasury : Term
  underlying : Term
  yieldFeeBps : Nat
  lastHarvestTime : Nat
  cumulativeProtocolFee : Nat
  totalDeposited : Nat
  totalPaidOut : Nat
  yieldHighWaterMark : Nat
  accruedProtocolFee : Nat

/-- The vault's Aave position (the spoke behind `IAaveSpoke`, ArmadaYieldVault.sol:93):
    the assets it is worth, and whether Aave is paused or short of liquidity. -/
structure AaveState where
  vaultAssets : Nat
  paused : Bool
  illiquid : Bool

/-- The yield contracts on the hub chain. -/
structure YieldState where
  adapter : AdapterState
  vault : VaultState
  aave : AaveState

end ArmadaLean.Cctp
