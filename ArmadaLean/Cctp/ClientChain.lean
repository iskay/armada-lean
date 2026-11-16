-- ABOUTME: A client chain's state and steps: the client's shield burns, the gasless wrapper, and the unshield handler.
-- ABOUTME: Each step holds exactly when the client's and Circle's checks pass; guard IDs follow model sheet v2.1 §5.
/-
  ArmadaLean.Cctp.ClientChain — the client-chain side of the CCTP model.

  Design record: model sheet v2.1 §4.3 and §5.1-§5.2 (client steps CS*, CW*, GS*; client
  unshield handler DU1-DU7). A client step relates two `ClientChain` states. The two shield
  entry points share `BurnShield`: pull the burned total from a payer, approve the
  TokenMessenger, and burn through Circle (`CircleChain.Burn`). The client's
  `crossChainShieldWithFee` has no caller restriction, so anyone may call it directly, not
  only the gasless wrapper (re-check finding R1-05). The burn through the client's stored
  `tokenMessenger` is modelled for a genuine TokenMessenger; a miswired one falls under the
  wiring hypothesis (model sheet v2.1 §9, A-wiring), as on the hub.
-/
import ArmadaLean.Cctp.HubChain
import ArmadaLean.Cctp.Client

namespace ArmadaLean.Cctp

/-- A client chain's state: the client pool, Circle's contracts there, the token ledger, and
    the hook routers deployed there. -/
structure ClientChain where
  client : ClientState
  circle : CircleChain
  ledger : Ledger
  routers : Term → Option RouterState

/-- The finality a client burn requests (PrivacyPoolClient.sol:381-393): the caller's FAST or
    STANDARD request, else the client's default, else STANDARD. -/
def ClientState.resolveFinality (c : ClientState) (requested : Option RequestedFinality) :
    RequestedFinality :=
  match requested with
  | some f => f
  | none => c.defaultFinality.getD .standard

/-- A requested finality a caller may pass to the client: FAST or STANDARD only
    (PrivacyPoolClient.sol:383-386). -/
def ClientFinalityOK : Option RequestedFinality → Prop
  | none => True
  | some .fast => True
  | some .standard => True
  | some (.raw _) => False

/-- A note the client accepts before burning (`_validateNote`, PrivacyPoolClient.sol:340-343):
    positive value and a canonical note key. -/
def ClientNoteOK (n : ShieldData) : Prop := 0 < n.value.val ∧ Canonical n.npk

/-- Pull `total` USDC from `payer` (the client is the spender), approve the TokenMessenger for
    it, and burn it through Circle toward the hub (`_pullAndBurn`,
    PrivacyPoolClient.sol:352-374): the burn record names the hub domain, mints to `hubPool`,
    pins `destinationCaller` to `hubHookRouter`, burns the client's `usdc`, carries the
    notes as hook data, and requests the resolved finality. -/
def ClientChain.BurnShield (s : ClientChain) (payer txOrigin : Term) (notes : List ShieldData)
    (total maxFee : Nat) (finality : Option RequestedFinality) (rec : BurnRecord)
    (L' : Ledger) : Prop :=
  s.client.tokenMessenger = s.circle.tokenMessenger ∧
  ∃ L₁, s.ledger.transferFrom s.client.usdc s.client.self payer s.client.self total = some L₁ ∧
  ∃ L₂, L₁.approve s.client.usdc s.client.self s.client.tokenMessenger total = some L₂ ∧
  rec.source = s.circle.domain ∧ rec.dest = s.client.hubDomain ∧
  rec.destinationCaller = s.client.hubHookRouter ∧
  rec.requested = s.client.resolveFinality finality ∧
  rec.body = { burnToken := s.client.usdc, mintRecipient := s.client.hubPool, amount := total,
               messageSender := .clean s.client.self, maxFee := maxFee, hookData := .shield notes } ∧
  s.circle.Burn L₂ s.client.self txOrigin rec L'

/-- A direct cross-chain shield by `caller` (`crossChainShield`, PrivacyPoolClient.sol:150-179):
    one note of value `amount`. -/
def ClientChain.Shield (s : ClientChain) (caller txOrigin : Term) (note : ShieldData)
    (maxFee : Nat) (finality : Option RequestedFinality) (rec : BurnRecord) (s' : ClientChain) :
    Prop :=
  0 < note.value.val ∧                                                        -- CS1
  maxFee < note.value.val ∧                                                   -- CS2
  s.client.hubPool ≠ Bytes32.zero ∧                                           -- CS3
  s.client.hubHookRouter ≠ Bytes32.zero ∧                                     -- CS4
  ClientNoteOK note ∧                                                         -- CS6 (CS5: the uint120 type)
  ClientFinalityOK finality ∧
  ∃ L', s.BurnShield caller txOrigin [note] note.value.val maxFee finality rec L' ∧  -- CS7, CB*
  s' = { s with ledger := L' }

/-- A cross-chain shield with a relayer fee note, by any `caller` (`crossChainShieldWithFee`,
    PrivacyPoolClient.sol:194-222): the user note first (it absorbs the CCTP fee on the hub),
    then the fee note. -/
def ClientChain.ShieldWithFee (s : ClientChain) (caller txOrigin : Term) (userNote feeNote : ShieldData)
    (maxFee : Nat) (finality : Option RequestedFinality) (rec : BurnRecord) (s' : ClientChain) :
    Prop :=
  s.client.hubPool ≠ Bytes32.zero ∧ s.client.hubHookRouter ≠ Bytes32.zero ∧    -- CW1
  0 < userNote.value.val + feeNote.value.val ∧                                -- CW2
  maxFee < userNote.value.val ∧                                               -- CW3
  ClientNoteOK userNote ∧ ClientNoteOK feeNote ∧                              -- CW4
  ClientFinalityOK finality ∧
  ∃ L', s.BurnShield caller txOrigin [userNote, feeNote]
      (userNote.value.val + feeNote.value.val) maxFee finality rec L' ∧         -- CW5, CB*
  s' = { s with ledger := L' }

/-- A user signs a gasless intent: it joins the signed set (the symbolic stand-in for an
    unforgeable signature, assumption T-20). -/
def ClientChain.SignIntent (s : ClientChain) (signer : Term) (i : Intent) (s' : ClientChain) : Prop :=
  i.user = signer ∧
  s' = { s with client := { s.client with wrapper := { s.client.wrapper with
          signedIntents := i :: s.client.wrapper.signedIntents } } }

/-- A token holder signs an ERC-2612 permit. -/
def ClientChain.SignPermit (s : ClientChain) (signer : Term) (pm : Permit) (s' : ClientChain) : Prop :=
  pm.owner = signer ∧
  s' = { s with client := { s.client with wrapper := { s.client.wrapper with
          signedPermits := pm :: s.client.wrapper.signedPermits } } }

/-- Anyone submits a signed, unused, unexpired permit (GaslessShieldWrapperClient.sol:187-194):
    the allowance is set, under USDC's approve checks, and the permit is used. -/
def ClientChain.SubmitPermit (s : ClientChain) (now : Nat) (pm : Permit) (s' : ClientChain) : Prop :=
  pm ∈ s.client.wrapper.signedPermits ∧ pm ∉ s.client.wrapper.usedPermits ∧ now ≤ pm.deadline ∧
  ∃ L', s.ledger.approve s.client.usdc pm.owner pm.spender pm.value = some L' ∧
  s' = { s with ledger := L', client := { s.client with wrapper := { s.client.wrapper with
          usedPermits := pm :: s.client.wrapper.usedPermits } } }

/-- A relayer submits a user's signed intent (`gaslessCrossChainShield`,
    GaslessShieldWrapperClient.sol:112-201): the intent is signed and unexpired with the
    user's current nonce, which is consumed; the wrapper pulls both notes' total from the user
    and passes it to the client's `crossChainShieldWithFee` as the caller. The relayer is the
    transaction origin, which Circle's denylist checks (re-check RT-relayer-10). A requested finality
    of `none` resolves to the client's default at submission (re-check RT-owner-05). -/
def ClientChain.GaslessShield (s : ClientChain) (now : Nat) (relayer : Term) (i : Intent)
    (rec : BurnRecord) (s' : ClientChain) : Prop :=
  i ∈ s.client.wrapper.signedIntents ∧                                        -- GS1
  i.nonce = s.client.wrapper.nonces i.user ∧                                  -- GS2
  now ≤ i.deadline ∧                                                          -- GS3
  let total := i.userNote.value.val + i.feeNote.value.val
  let w := s.client.wrapper.self
  ∃ L₁, s.ledger.transferFrom s.client.usdc w i.user w total = some L₁ ∧       -- GS4, GS5
  ∃ L₂, L₁.approve s.client.usdc w s.client.self total = some L₂ ∧
  let s₁ := { s with
    ledger := L₂,
    client := { s.client with wrapper := { s.client.wrapper with
      nonces := fun u => if u = i.user then s.client.wrapper.nonces u + 1 else s.client.wrapper.nonces u } } }
  s₁.ShieldWithFee w relayer i.userNote i.feeNote i.maxFee i.finality rec s'

/-- The client's CCTP unshield handler (`handleReceiveFinalizedMessage` /
    `handleReceiveUnfinalizedMessage` → `_handleCCTPMessage`, PrivacyPoolClient.sol:245-331),
    run by `caller` on a burn from domain `src` with body `body` and executed fee `feeExecuted`,
    after Circle minted the USDC to the client: it forwards exactly the amount received to the
    unshield's recipient. -/
def ClientChain.HandleUnshield (s : ClientChain) (caller : Term) (finalized : Bool) (executed : Nat)
    (src : Domain) (body : BurnBody) (feeExecuted : Nat) (s' : ClientChain) : Prop :=
  (caller = s.client.tokenMessenger ∨ s.client.hookRouter = some caller) ∧    -- DU1
  (if finalized = true then 2000 ≤ executed else 1000 ≤ executed) ∧           -- DU2
  src = s.client.hubDomain ∧                                                   -- DU3
  ∃ u : UnshieldData, body.hookData = .unshield u ∧                            -- DU4, DU5
  body.messageSender = s.client.hubPool ∧                                      -- DU6 (whole word)
  ∃ L', s.ledger.transfer s.client.usdc s.client.self u.recipient (body.amount - feeExecuted)
      = some L' ∧                                                              -- DU7
  s' = { s with ledger := L' }

end ArmadaLean.Cctp
