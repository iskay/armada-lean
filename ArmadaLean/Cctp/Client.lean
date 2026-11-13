-- ABOUTME: A client-chain pool's state in the CCTP model, with its gasless wrapper's signed intents and permits.
-- ABOUTME: The client's initializer checks nothing, so every field may hold a mistaken value.
/-
  ArmadaLean.Cctp.Client — the state of one client-chain pool and its gasless wrapper.

  Design record: model sheet v2.1 §4.3. `PrivacyPoolClient.initialize` checks only the
  caller and that it runs once (PrivacyPoolClient.sol:96-117): no zero or identity checks,
  so the owner, the Circle addresses and `usdc` may all be wrong (finding CB-7). Signed
  gasless intents and permits are symbolic: an intent or permit enters the state only by a
  step of its signer (`signIntent`, `signPermit`), which stands for an unforgeable
  signature scheme whose digest covers the listed fields (assumption T-20). The client's
  steps come in a later commit. The hub's own gasless wrapper (GaslessShieldWrapper.sol)
  uses the same `Intent` and `Permit` records.
-/
import ArmadaLean.Cctp.Types

namespace ArmadaLean.Cctp

/-- A signed gasless shield intent (GaslessShieldWrapperClient.sol:151-174): the user, both
    notes, the CCTP `maxFee`, the requested finality (`none` resolves to the client
    owner's default at submission), a deadline and the user's nonce. -/
structure Intent where
  user : Term
  userNote : ShieldData
  feeNote : ShieldData
  maxFee : Nat
  finality : Option RequestedFinality
  deadline : Nat
  nonce : Nat
  deriving DecidableEq

/-- A signed ERC-2612 permit: anyone may submit it, once (GaslessShieldWrapperClient.sol:187-194
    calls it under `try`). -/
structure Permit where
  owner : Term
  spender : Term
  value : Nat
  deadline : Nat
  nonce : Nat
  deriving DecidableEq

/-- A gasless wrapper's state: each user's next intent nonce, the intents and permits their
    owners have signed, and the permits already used. -/
structure GaslessState where
  self : Term
  nonces : Term → Nat
  signedIntents : List Intent
  signedPermits : List Permit
  usedPermits : List Permit

/-- A client pool's state (PrivacyPoolClient.sol at armada-poc 64436c14).
    * `self`: the client's own address.
    * `tokenMessenger`, `messageTransmitter`, `usdc`, `localDomain`, `owner`: from
      `initialize`, unchecked (PrivacyPoolClient.sol:96-117).
    * `hubDomain`, `hubPool`: mutable by the owner, any word (PrivacyPoolClient.sol:427-432).
    * `hookRouter`: set once, non-zero (PrivacyPoolClient.sol:444-450).
    * `hubHookRouter`: mutable, any word (PrivacyPoolClient.sol:458-462).
    * `defaultFinality`: FAST or STANDARD when set (PrivacyPoolClient.sol:471-479).
    * `wrapper`: the client chain's gasless wrapper. -/
structure ClientState where
  self : Term
  owner : Term
  tokenMessenger : Term
  messageTransmitter : Term
  usdc : Term
  localDomain : Domain
  hubDomain : Domain
  hubPool : Bytes32
  hookRouter : Option Term
  hubHookRouter : Bytes32
  defaultFinality : Option RequestedFinality
  wrapper : GaslessState

end ArmadaLean.Cctp
