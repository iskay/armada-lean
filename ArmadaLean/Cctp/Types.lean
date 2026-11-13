-- ABOUTME: Core data types of the CCTP model: domains, finality, 32-byte words, payloads, burns, messages, attestations.
-- ABOUTME: Addresses are symbolic terms as in the pool model; a 32-byte word records whether an address in it is clean.
/-
  ArmadaLean.Cctp.Types — the data the CCTP model's state and steps are built from.

  Design record: model sheet v2.1 §3 (`.context/phase2/model-sheet.md` in the working
  notes; to be moved to `docs/` with the PR), with Butters' 2026-11-13 decision on
  address representation: addresses stay symbolic `Term`s, as everywhere else in this
  project (`ArmadaLean.Token`, `ArmadaLean.Pool.Payout`; armada-laconic `docs/process.md`
  1.2, "A contract address is a hash output. Model it as a symbolic Keccak term, never
  as a number"). CCTP stores remote addresses as 32-byte words, and Circle and the
  Armada router truncate a word to an address by dropping its upper 12 bytes, while the
  Armada pools compare whole words. `Bytes32` keeps exactly that distinction:
  `clean a` is address `a` zero-extended, `dirty hi a` is the same address with non-zero
  upper bytes `hi`, and `other n` is any other word. Truncation (`Bytes32.toAddress`)
  sends `clean a` and `dirty hi a` to `a`; word equality tells them apart.

  Circle source: circlefin/evm-cctp-contracts at a92a2b4e7e6ef99bf0b05dca71780f5ec190e729.
  Armada source: ship-armada/armada-poc at 64436c14.
-/
import ArmadaLean.Transact
import Mathlib.Data.PNat.Basic

namespace ArmadaLean.Cctp

/-- A CCTP domain: Circle's identifier for one chain (`MessageV2` envelope fields
    `sourceDomain` and `destinationDomain`, MessageV2.sol:31-41). -/
structure Domain where
  id : Nat
  deriving DecidableEq

/-- A 32-byte word as CCTP stores and transports remote addresses: the pool's
    `remotePools` / `remoteHookRouters` (PrivacyPool.sol:326-343), the client's `hubPool`
    / `hubHookRouter` (PrivacyPoolClient.sol:427-462), and the burn-message fields
    `mintRecipient`, `messageSender`, `destinationCaller` (BurnMessageV2.sol:27-36). -/
inductive Bytes32 where
  /-- Address `a`, zero-extended: the form `addressToBytes32` produces
      (ICCTPV2.sol:289-291; AddressUtils.sol:29-30). -/
  | clean (a : Term)
  /-- Address `a` with the non-zero value `hi` in the upper 12 bytes. The pools'
      whole-word comparisons (PrivacyPool.sol:271-276, PrivacyPoolClient.sol:312-315)
      reject it where the clean form would pass; truncation still yields `a`. -/
  | dirty (hi : ℕ+) (a : Term)
  /-- Any other word, by its numeric value. -/
  | other (n : Nat)
  deriving DecidableEq

/-- The zero word (`bytes32(0)`): "unset" for the pool's mappings, and "anyone may
    deliver" as a `destinationCaller` (MessageTransmitterV2.sol:300-306). -/
def Bytes32.zero : Bytes32 := .other 0

/-- Truncation of a word to an address, dropping the upper 12 bytes: Circle's
    `AddressUtils.toAddress` (AddressUtils.sol:39-40, used for the mint recipient at
    TokenMessengerV2.sol:473) and the router's `bytes32ToAddress` (ICCTPV2.sol:297-299,
    used for hook dispatch at CCTPHookRouter.sol:77-79). For a word that holds no
    address term, the result is the numeric value of its low 160 bits. -/
def Bytes32.toAddress : Bytes32 → Term
  | .clean a => a
  | .dirty _ a => a
  | .other n => Term.val (n % 2 ^ 160)

@[simp] theorem Bytes32.toAddress_clean (a : Term) : (Bytes32.clean a).toAddress = a := rfl

@[simp] theorem Bytes32.toAddress_dirty (hi : ℕ+) (a : Term) :
    (Bytes32.dirty hi a).toAddress = a := rfl

/-- A clean word and a dirty word holding the same address are different words, although
    they truncate to the same address. -/
theorem Bytes32.clean_ne_dirty (hi : ℕ+) (a : Term) : Bytes32.clean a ≠ Bytes32.dirty hi a :=
  fun h => Bytes32.noConfusion h

/-- The finality a burn requests (`minFinalityThreshold`). Armada's own senders request
    only `fast` (1000) or `standard` (2000) (PrivacyPoolClient.sol:381-393,
    PrivacyPool.sol:456-459); any other sender may request any value Circle's
    TokenMessenger accepts, which is at least 500 (FinalityThresholds.sol:27,
    TokenMessengerV2.sol:342-354). -/
inductive RequestedFinality where
  | fast
  | standard
  | raw (n : {n : Nat // 500 ≤ n})
  deriving DecidableEq

/-- The numeric threshold a requested finality stands for (FinalityThresholds.sol:21,24). -/
def RequestedFinality.value : RequestedFinality → Nat
  | .fast => 1000
  | .standard => 2000
  | .raw n => n.val

/-- One shield note carried in a CCTP payload (`ShieldData`, CCTPTypes.sol). `value`
    is a `uint120`, so the bound is part of the type; `ciphertext` stands for the
    encrypted bundle and shield key, which no contract check reads. -/
structure ShieldData where
  npk : Term
  value : {v : Nat // v < 2 ^ 120}
  ciphertext : Term
  integrator : Option Term
  deriving DecidableEq

/-- The unshield payload (`UnshieldData`, CCTPTypes.sol): the final recipient and the
    relayer-chosen `uniqueNonce`, which no proof binds (TransactModule.sol:251-253). -/
structure UnshieldData where
  recipient : Term
  uniqueNonce : Term
  deriving DecidableEq

/-- The hook data of a burn, as the pools decode it (`CCTPPayloadLib.decode`,
    CCTPTypes.sol:100-109). `malformed` is any byte string the decoder rejects, so the
    decode guard can fail in the model (PrivacyPool.sol:261). -/
inductive Payload where
  | shield (notes : List ShieldData)
  | unshield (u : UnshieldData)
  | malformed
  deriving DecidableEq

/-- A stable identity for one burn transaction. It survives the reordering of pending
    transactions by a reorg; a burn that a reorg drops has its identity retired (model
    sheet v2.1 §4.1). -/
structure BurnId where
  id : Nat
  deriving DecidableEq

/-- The fields of a `BurnMessageV2` body that the pools and the router read
    (BurnMessageV2.sol:27-36). A burn's body carries them, and a generic message's body may
    be shaped like one (the #613 forgery). `feeExecuted` and the expiry are not here:
    Circle's attestation service chooses them (`Attestation`). -/
structure BurnBody where
  burnToken : Term
  mintRecipient : Bytes32
  amount : Nat
  messageSender : Bytes32
  maxFee : Nat
  hookData : Payload
  deriving DecidableEq

/-- A burn as the source chain records it (`depositForBurn` / `depositForBurnWithHook`,
    TokenMessengerV2.sol:166-232). The burn checks `maxFee < amount`
    (TokenMessengerV2.sol:342-354), so the bound is part of the type. `messageSender` in
    the body is the address that called `depositForBurn` (TokenMessengerV2.sol:369). -/
structure BurnRecord where
  id : BurnId
  source : Domain
  dest : Domain
  destinationCaller : Bytes32
  requested : RequestedFinality
  body : BurnBody
  maxFee_lt : body.maxFee < body.amount

/-- A generic message (`MessageTransmitterV2.sendMessage`, MessageTransmitterV2.sol:143-174):
    anyone may send one, with any recipient and any body; the envelope sender is the
    caller. `burnShaped` is the body read as a burn body, when it parses as one. -/
structure GenericMessage where
  source : Domain
  dest : Domain
  sender : Bytes32
  recipient : Bytes32
  destinationCaller : Bytes32
  burnShaped : Option BurnBody
  deriving DecidableEq

/-- A CCTP message: a burn, or a generic message. The router dispatches a pool hook only
    for burns (its envelope-recipient check, CCTPHookRouter.sol:62-65), so the two must be
    distinguishable. -/
inductive Message where
  | burn (b : BurnRecord)
  | generic (g : GenericMessage)

/-- The destination domain of a message's envelope. -/
def Message.dest : Message → Domain
  | .burn b => b.dest
  | .generic g => g.dest

/-- The `destinationCaller` of a message's envelope (MessageTransmitterV2.sol:300-306). -/
def Message.destinationCaller : Message → Bytes32
  | .burn b => b.destinationCaller
  | .generic g => g.destinationCaller

/-- Circle's destination-side fee bounds for a burn (TokenMessengerV2.sol:470-471):
    `fee == 0 || fee < amount`, and `fee <= maxFee`. -/
def FeeWithinBounds (b : BurnBody) (fee : Nat) : Prop :=
  (fee = 0 ∨ fee < b.amount) ∧ fee ≤ b.maxFee

/-- What Circle's attestation service adds to a message when it attests it: a nonce
    (assigned off-chain), the executed fee, the executed finality, and for burns an
    expiry block (TokenMessengerV2.sol:460-465; BurnMessageV2.sol:54,85 leave fee and
    expiry empty at the source). The attester epoch records which attester set signed,
    so a rotation can invalidate an attestation. For burns, the fee bounds are part of
    the type. -/
structure Attestation where
  msg : Message
  nonce : Nat
  feeExecuted : Nat
  executed : Nat
  expiry : Option Nat
  epoch : Nat
  feeOK : ∀ b, msg = .burn b → FeeWithinBounds b.body feeExecuted

/-- A circuit shape: the number of nullifiers (inputs) and commitments (outputs). The pool
    keeps one verification key per shape (`verificationKeys[N][M]`, PrivacyPool.sol:514). -/
structure Shape where
  nullifiers : Nat
  commitments : Nat
  deriving DecidableEq

/-- The public inputs of a proof as the pool lays them out for the verifier: one flat
    list `[merkleRoot, boundParamsHash, nullifiers…, commitments…]` (PrivacyPool.sol:524-541).
    The layout is flat, so two shapes with the same `N + M` read the same list
    differently: the basis of the mis-slotted-key case. -/
abbrev PublicInputs := List Term

/-- The flat public-input list of a Transact public record (PrivacyPool.sol:524-541). -/
def PublicInputs.ofTransact {N M : Nat} (pub : TransactPublic N M) : PublicInputs :=
  pub.merkleRoot :: pub.boundParamsHash :: (List.ofFn pub.nullifiers ++ List.ofFn pub.commitmentsOut)

end ArmadaLean.Cctp
