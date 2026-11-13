-- ABOUTME: Circle's CCTP v2 contracts on one chain, and its off-chain attestation service, as state and relations.
-- ABOUTME: Burns, generic sends and message receipt each hold exactly when Circle's on-chain checks pass.
/-
  ArmadaLean.Cctp.Circle — Circle's CCTP v2 on one chain, and the attestation service.

  Design record: model sheet v2.1 §4.7, §5.1 (burn guards CB*), §5.2 (receive guards
  RM*), §5.6, and the assumption registry §9 (T-1′, T-2, T-2b, T-3, T-4, T-5, T-6, T-9,
  T-11). Source: circlefin/evm-cctp-contracts at a92a2b4e7e6ef99bf0b05dca71780f5ec190e729,
  `src/v2/` (MessageTransmitterV2.sol, TokenMessengerV2.sol, BaseTokenMessenger.sol,
  TokenMinterV2.sol), and the stablecoin's FiatTokenV1.sol for the USDC checks
  (`ArmadaLean.Cctp.Tokens`).

  Circle's operations are relations between states (`Burn`, `SendGeneric`, `Receive`),
  as the pool model's `Step` is. The attestation service (Iris) is off-chain: its state
  `Iris` is global, not part of any chain.
-/
import ArmadaLean.Cctp.Tokens

namespace ArmadaLean.Cctp

/-- Circle's CCTP contracts on one chain (MessageTransmitterV2, TokenMessengerV2,
    TokenMinterV2 and their roles).
    * `usedNonces`: the destination's used-nonce set, one global set keyed by nonce
      (BaseMessageTransmitter.sol:57-58).
    * `paused`: the pauser's flag on send, receive, mint and burn
      (MessageTransmitterV2.sol:149,209; TokenMinter.sol:93,114).
    * `denylist`: addresses that may not burn, checked against the caller and the
      transaction origin (Denylistable.sol:87-93).
    * `remoteMessenger d`: a TokenMessenger is registered for domain `d`
      (BaseTokenMessenger.sol:183-193,259-265,284-291).
    * `linkedToken d t`: the local token minted for burn token `t` of domain `d`
      (TokenMinterV2.sol:68-69).
    * `minter`: the local TokenMinter, the USDC minter; `minterAllowance t`: its remaining
      mint allowance for token `t` (FiatToken `minterAllowed`).
    * `maxShieldNotes`: the message body size limit, measured in shield notes
      (BaseMessageTransmitter.sol:77-81).
    * `burnLimit t`, `minFeeRate t`, `fastFee t`: the per-message burn limit
      (TokenController.sol:98-105), the minimum fee rate on the 10^7 scale
      (TokenMessengerV2.sol:314-319), and the attestation service's fast-transfer fee for
      token `t`.
    * `feeRecipient`: where the executed fee is minted (BaseTokenMessenger.sol:330-358). -/
structure CircleChain where
  domain : Domain
  tokenMessenger : Term
  messageTransmitter : Term
  minter : Term
  usedNonces : List Nat
  paused : Bool
  denylist : Term → Bool
  remoteMessenger : Domain → Bool
  linkedToken : Domain → Term → Option Term
  minterAllowance : Term → Nat
  maxShieldNotes : Nat
  burnLimit : Term → Nat
  minFeeRate : Term → Nat
  fastFee : Term → Nat
  feeRecipient : Term

/-- The off-chain attestation service: the current attester epoch and every attestation
    issued so far (MessageTransmitterV2.sol:286-313 checks one against the attester set). -/
structure Iris where
  epoch : Nat
  issued : List Attestation

/-- A payload fits the message body size limit. -/
def CircleChain.BodyFits (cc : CircleChain) : Payload → Prop
  | .shield notes => notes.length ≤ cc.maxShieldNotes
  | _ => True

/-- Circle's minimum-fee rule for a burn (TokenMessengerV2.sol:314-319,347-354): with a
    non-zero rate, `maxFee ≥ max(1, amount · rate / 10^7)`. -/
def CircleChain.MinFeeOK (cc : CircleChain) (b : BurnBody) : Prop :=
  cc.minFeeRate b.burnToken = 0 ∨ max 1 (b.amount * cc.minFeeRate b.burnToken / 10 ^ 7) ≤ b.maxFee

/-- A burn on this chain (`depositForBurn` / `depositForBurnWithHook`,
    TokenMessengerV2.sol:166-232,342-381; Circle burn guards CB1-CB9 of model sheet v2.1
    §5.1). `burner` is the caller and `txOrigin` the transaction origin; the TokenMessenger
    pulls `amount` from the burner with `transferFrom` and the minter burns it. -/
def CircleChain.Burn (cc : CircleChain) (L : Ledger) (burner txOrigin : Term) (rec : BurnRecord)
    (L' : Ledger) : Prop :=
  cc.paused = false ∧                                            -- CB1
  cc.denylist burner = false ∧ cc.denylist txOrigin = false ∧    -- CB2
  rec.source = cc.domain ∧ rec.dest ≠ cc.domain ∧
  cc.remoteMessenger rec.dest = true ∧                           -- CB3
  0 < rec.body.amount ∧ rec.body.amount ≤ cc.burnLimit rec.body.burnToken ∧   -- CB4
  cc.MinFeeOK rec.body ∧                                         -- CB5
  rec.body.mintRecipient ≠ Bytes32.zero ∧
  rec.body.messageSender = .clean burner ∧
  cc.BodyFits rec.body.hookData ∧                                -- CB9
  ∃ L₁, L.transferFrom rec.body.burnToken cc.tokenMessenger burner cc.minter rec.body.amount = some L₁ ∧
    L₁.burn rec.body.burnToken cc.minter rec.body.amount = some L'   -- CB6-CB8 (USDC checks)

/-- A generic message sent on this chain (`sendMessage`, MessageTransmitterV2.sol:143-174):
    not paused, another domain, a non-zero recipient, a body within the size limit, and the
    envelope sender is the caller. -/
def CircleChain.SendGeneric (cc : CircleChain) (sender : Term) (g : GenericMessage) : Prop :=
  cc.paused = false ∧ g.source = cc.domain ∧ g.dest ≠ cc.domain ∧
  g.recipient ≠ Bytes32.zero ∧ g.sender = .clean sender ∧
  (∀ body, g.burnShaped = some body → cc.BodyFits body.hookData)

/-- The receive checks common to every message (MessageTransmitterV2.sol:286-313; receive
    guards RM1, RM2, RM3, RM4, RM6 of model sheet v2.1 §5.2). -/
def CircleChain.ReceiveCommon (cc : CircleChain) (iris : Iris) (caller : Term) (att : Attestation) :
    Prop :=
  att ∈ iris.issued ∧ att.epoch = iris.epoch ∧                    -- RM1
  att.msg.dest = cc.domain ∧                                       -- RM2
  (att.msg.destinationCaller = Bytes32.zero ∨
    att.msg.destinationCaller = .clean caller) ∧                   -- RM3
  att.nonce ∉ cc.usedNonces ∧                                      -- RM4
  cc.paused = false                                                -- RM6

/-- Mark a nonce used. -/
def CircleChain.useNonce (cc : CircleChain) (n : Nat) : CircleChain :=
  { cc with usedNonces := n :: cc.usedNonces }

/-- Receipt of an attested message by `caller` (`receiveMessage`). For a generic message the
    nonce is used and nothing is minted; the recipient's handler runs in the step that
    calls this (`ArmadaLean.Cctp.Router`). For a burn (TokenMessengerV2.sol:405-473): not
    expired (RM5); the source messenger registered and the token linked; then the linked
    token is minted, `amount − feeExecuted` to the truncated mint recipient and the fee to
    the fee recipient, under USDC's mint checks, and the minter allowance falls by
    `amount` (RM7). -/
def CircleChain.Receive (cc : CircleChain) (L : Ledger) (iris : Iris) (now : Nat) (caller : Term)
    (att : Attestation) (cc' : CircleChain) (L' : Ledger) : Prop :=
  cc.ReceiveCommon iris caller att ∧
  match att.msg with
  | .generic _ => cc' = cc.useNonce att.nonce ∧ L' = L
  | .burn b =>
      (att.expiry = none ∨ ∃ e, att.expiry = some e ∧ now < e) ∧          -- RM5
      cc.remoteMessenger b.source = true ∧
      ∃ tok, cc.linkedToken b.source b.body.burnToken = some tok ∧
        b.body.amount ≤ cc.minterAllowance tok ∧
        ∃ L₁, L.mint tok cc.minter b.body.mintRecipient.toAddress (b.body.amount - att.feeExecuted)
            = some L₁ ∧
          (att.feeExecuted = 0 ∧ L' = L₁ ∨
            0 < att.feeExecuted ∧ L₁.mint tok cc.minter cc.feeRecipient att.feeExecuted = some L') ∧
          cc' = { cc.useNonce att.nonce with
            minterAllowance := fun t => if t = tok then cc.minterAllowance t - b.body.amount
              else cc.minterAllowance t }

/-- The nonce of a received message is used afterwards. -/
theorem CircleChain.useNonce_mem (cc : CircleChain) (n : Nat) : n ∈ (cc.useNonce n).usedNonces :=
  List.mem_cons_self

end ArmadaLean.Cctp
