-- ABOUTME: The hub privacy pool's state in the CCTP model: the pool model's state plus CCTP wiring, keys and settings.
-- ABOUTME: Every field holds any value the contract's setters and initializer accept, including mistakes.
/-
  ArmadaLean.Cctp.Hub — the hub pool's state.

  Design record: model sheet v2.1 §4.2. The pool's notes, nullifiers, trees and ghost
  custody ledger are the pool model's `PoolState` (`ArmadaLean.Pool`, after the port of
  commit 55ee591). The flat shield fee is `PoolState.feeRatio`; the owner's
  `setShieldFee` writes it (one field, so the flat fee cannot disagree with itself).
  Everything CCTP and the owner add is here. Under decision D1 (a) the owner is
  adversarial, so each field may hold any value its setter or the initializer accepts:
  wrong Circle addresses (finding N-1), dirty words (N-4), a reverting registry (N-2), any
  key in any slot (S1). The hub's steps come in a later commit.
-/
import ArmadaLean.Pool
import ArmadaLean.Cctp.Crypto

namespace ArmadaLean.Cctp

/-- The hub pool's state (PrivacyPool.sol, PrivacyPoolStorage.sol at armada-poc 64436c14).
    * `pool`: the pool model's state (notes, nullifiers, trees, ghost custody, flat fee).
    * `self`: the pool's own address; `owner` and `pendingOwner`: the two-step ownership
      transfer (PrivacyPool.sol:304-319).
    * `tokenMessenger`, `messageTransmitter`, `usdc`, `localDomain`, `treasury`: set once by
      `initialize` (PrivacyPool.sol:81-127), which checks only that they are non-zero.
    * `remotePools`, `remoteHookRouters`: per domain, any word (PrivacyPool.sol:326-343).
    * `hookRouter`: set once, non-zero (PrivacyPool.sol:439-445).
    * `adapterRegistry`: set once, non-zero (PrivacyPool.sol:421-427).
    * `verificationKeys`: per shape, any key (VerifierModule.sol:31-41).
    * `feeModule`, `pauseController`: addresses into `Components`, mutable by the owner
      (PrivacyPool.sol:468-482).
    * `defaultFinality`: FAST or STANDARD when set (PrivacyPool.sol:454-462).
    * `blocklist`: tokens refused by shields; USDC can never be on it (PrivacyPool.sol:353-376).
    * `guardOn`: the `nonReentrant` flag (PrivacyPool.sol:57-62), read by callback steps. -/
structure HubState where
  pool : PoolState
  self : Term
  owner : Term
  pendingOwner : Option Term
  tokenMessenger : Term
  messageTransmitter : Term
  usdc : Term
  localDomain : Domain
  treasury : Term
  remotePools : Domain → Bytes32
  remoteHookRouters : Domain → Bytes32
  hookRouter : Option Term
  adapterRegistry : Option Term
  verificationKeys : Shape → Option VKey
  feeModule : Option Term
  pauseController : Option Term
  defaultFinality : Option RequestedFinality
  blocklist : Term → Bool
  guardOn : Bool

end ArmadaLean.Cctp
