-- ABOUTME: How CCTP messages reach the pools: router relays, direct receiveMessage calls, and direct handler calls.
-- ABOUTME: A relay is atomic: Circle's receipt and the pool hook succeed together or the whole delivery reverts.
/-
  ArmadaLean.Cctp.Delivery — the delivery layer, on the hub chain and on a client chain.

  Design record: model sheet v2.1 §5.2 (`relay` RL1-RL2 with Circle's RM*, `directReceive`,
  `handlerCall`). Three ways reach a pool's CCTP handler:
  - `relay` (`CCTPHookRouter.relayWithHook`, CCTPHookRouter.sol:56-100), permissionless: the
    envelope recipient must be the router's TokenMessenger (RL1), the router calls
    `receiveMessage` (Circle's checks and the mint, with the router as caller), then
    dispatches the hook to the truncated mint recipient (RL2), all in one transaction;
  - `directReceive` (`MessageTransmitterV2.receiveMessage`, anyone): a burn whose
    `destinationCaller` is zero mints with no hook (the hookless delivery #64 fixed); a
    generic message runs its recipient's handler with the MessageTransmitter as caller;
  - `handlerCall`: any address that is not a Circle contract or a router calls a handler
    directly with a body of its choosing. The handler's caller check (DS1, DU1) refuses it
    unless an owner or deployer wired that address in (finding N-1, issue #641).

  Generic messages: Circle's TokenMessenger rejects one whose envelope sender is not a
  registered remote TokenMessenger (BaseTokenMessenger.sol:284-291), and a user's generic
  message never has one, so with RL1 in place no generic message gets through a genuine
  router. The guard is kept separate so that deleting it (the #613 bug replay) lets a
  burn-shaped generic message reach the hook with nothing minted.

  The hub's steps take the callback frame of `ArmadaLean.Cctp.HubChain` (`Frame`), which the
  shield handler opens at its fee-module calls. A client chain's steps need none: the client
  moves only its stored `usdc` and calls only Circle. When that `usdc` is Circle's USDC it
  makes no callbacks; when it is not, the burn every client shield ends in reverts (Circle
  burns only linked tokens), and the unshield handler makes one transfer and nothing after
  it, so a callback there sees nothing a separate step could not.
-/
import ArmadaLean.Cctp.HubShield
import ArmadaLean.Cctp.ClientChain

namespace ArmadaLean.Cctp

/-- The source domain of a message's envelope. -/
def Message.source : Message → Domain
  | .burn b => b.source
  | .generic g => g.source

/-- The body a hook receives: a burn's body, or a generic message's body read as a burn
    body when it parses as one. -/
def Message.hookBody : Message → Option BurnBody
  | .burn b => some b.body
  | .generic g => g.burnShaped

/-- The router's envelope check (RL1, CCTPHookRouter.sol:62-65): the message is addressed to
    the router's TokenMessenger. A burn is addressed to the destination chain's TokenMessenger
    (TokenMessengerV2.sol:356-381); a generic message to the recipient its sender chose. -/
def RouterRL1 (r : RouterState) (cc : CircleChain) : Message → Prop
  | .burn _ => r.tokenMessenger = cc.tokenMessenger
  | .generic g => g.recipient = .clean r.tokenMessenger

/-- A generic message's recipient accepts it inside `receiveMessage`: Circle's TokenMessenger
    never does (its sender check, BaseTokenMessenger.sol:284-291); another contract may. -/
def GenericRecipientAccepts (cc : CircleChain) (g : GenericMessage) : Prop :=
  g.recipient.toAddress ≠ cc.tokenMessenger

/-- An address an external actor may use as a caller: not a router, not Circle's TokenMessenger
    or MessageTransmitter (those only call handlers inside `relay` and `directReceive`). -/
def HubChain.ExternalCaller (s : HubChain) (c : Term) : Prop :=
  s.routers c = none ∧ c ≠ s.circle.tokenMessenger ∧ c ≠ s.circle.messageTransmitter

/-- The same, on a client chain. -/
def ClientChain.ExternalCaller (s : ClientChain) (c : Term) : Prop :=
  s.routers c = none ∧ c ≠ s.circle.tokenMessenger ∧ c ≠ s.circle.messageTransmitter

/-- A relay on the hub chain through the router at `rt`: RL1, the router's MessageTransmitter
    is Circle's, Circle's receipt with the router as caller, then the hook to the truncated mint
    recipient (RL2): the hub's shield handler when that is the hub, nothing in the pools
    otherwise. -/
def HubChain.Relay (s : HubChain) (F : Frame) (iris : Iris) (now : Nat) (rt : Term) (att : Attestation)
    (legs : List FeeLeg) (s' : HubChain) : Prop :=
  ∃ r, s.routers rt = some r ∧
  RouterRL1 r s.circle att.msg ∧                                              -- RL1
  r.messageTransmitter = s.circle.messageTransmitter ∧
  (∀ g, att.msg = .generic g → GenericRecipientAccepts s.circle g) ∧
  ∃ cc' L₁, s.circle.Receive s.ledger iris now rt att cc' L₁ ∧                -- RM*
  ∃ body, att.msg.hookBody = some body ∧
  let s₁ := { s with circle := cc', ledger := L₁ }
  if body.mintRecipient.toAddress = s.hub.self then                          -- RL2
    s₁.HandleShield F rt (decide (2000 ≤ att.executed)) att.executed att.msg.source body
      att.feeExecuted legs s'
  else s' = s₁

/-- A direct `receiveMessage` on the hub chain by `caller`: a burn mints with no hook; a generic
    message runs its recipient's handler, which for the hub is its shield handler with the
    MessageTransmitter as caller. -/
def HubChain.DirectReceive (s : HubChain) (F : Frame) (iris : Iris) (now : Nat) (caller : Term)
    (att : Attestation) (legs : List FeeLeg) (s' : HubChain) : Prop :=
  ∃ cc' L₁, s.circle.Receive s.ledger iris now caller att cc' L₁ ∧
  let s₁ := { s with circle := cc', ledger := L₁ }
  match att.msg with
  | .burn _ => s' = s₁
  | .generic g =>
      GenericRecipientAccepts s.circle g ∧
      if g.recipient.toAddress = s.hub.self then
        ∃ body, g.burnShaped = some body ∧
          s₁.HandleShield F s.circle.messageTransmitter (decide (2000 ≤ att.executed)) att.executed
            g.source body att.feeExecuted legs s'
      else s' = s₁

/-- A direct call of the hub's shield handler by an external caller, with a body of its choosing
    and nothing minted. -/
def HubChain.HandlerCall (s : HubChain) (F : Frame) (caller : Term) (finalized : Bool) (executed : Nat)
    (src : Domain) (body : BurnBody) (feeExecuted : Nat) (legs : List FeeLeg) (s' : HubChain) :
    Prop :=
  s.ExternalCaller caller ∧ s.HandleShield F caller finalized executed src body feeExecuted legs s'

/-- A relay on a client chain through the router at `rt`, dispatching to the client's unshield
    handler when the truncated mint recipient is the client. -/
def ClientChain.Relay (s : ClientChain) (iris : Iris) (now : Nat) (rt : Term) (att : Attestation)
    (s' : ClientChain) : Prop :=
  ∃ r, s.routers rt = some r ∧
  RouterRL1 r s.circle att.msg ∧                                              -- RL1
  r.messageTransmitter = s.circle.messageTransmitter ∧
  (∀ g, att.msg = .generic g → GenericRecipientAccepts s.circle g) ∧
  ∃ cc' L₁, s.circle.Receive s.ledger iris now rt att cc' L₁ ∧                -- RM*
  ∃ body, att.msg.hookBody = some body ∧
  let s₁ := { s with circle := cc', ledger := L₁ }
  if body.mintRecipient.toAddress = s.client.self then                       -- RL2
    s₁.HandleUnshield rt (decide (2000 ≤ att.executed)) att.executed att.msg.source body
      att.feeExecuted s'
  else s' = s₁

/-- A direct `receiveMessage` on a client chain by `caller`. -/
def ClientChain.DirectReceive (s : ClientChain) (iris : Iris) (now : Nat) (caller : Term)
    (att : Attestation) (s' : ClientChain) : Prop :=
  ∃ cc' L₁, s.circle.Receive s.ledger iris now caller att cc' L₁ ∧
  let s₁ := { s with circle := cc', ledger := L₁ }
  match att.msg with
  | .burn _ => s' = s₁
  | .generic g =>
      GenericRecipientAccepts s.circle g ∧
      if g.recipient.toAddress = s.client.self then
        ∃ body, g.burnShaped = some body ∧
          s₁.HandleUnshield s.circle.messageTransmitter (decide (2000 ≤ att.executed)) att.executed
            g.source body att.feeExecuted s'
      else s' = s₁

/-- A direct call of the client's unshield handler by an external caller, with a body of its
    choosing and nothing minted. -/
def ClientChain.HandlerCall (s : ClientChain) (caller : Term) (finalized : Bool) (executed : Nat)
    (src : Domain) (body : BurnBody) (feeExecuted : Nat) (s' : ClientChain) : Prop :=
  s.ExternalCaller caller ∧ s.HandleUnshield caller finalized executed src body feeExecuted s'

end ArmadaLean.Cctp
