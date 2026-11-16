-- ABOUTME: The hub's two shield steps: the CCTP inbound shield handler and the batched local shield.
-- ABOUTME: Each holds exactly when the contract's checks pass; guard IDs follow model sheet v2.1 §5.
/-
  ArmadaLean.Cctp.HubShield — the hub steps that create notes from tokens received.

  Design record: model sheet v2.1 §5.2 (hub shield handler, guards DS1-DS16) and §5.3
  (`localShieldBatch`, guards LS0-LS10). Both are relations between hub-chain states.

  `HandleShield` is the hub handler's part of an inbound delivery: by the time it runs,
  Circle's `receiveMessage` has minted the USDC to the pool (the router composes the two
  atomically in a later commit). Its fee legs are paid from the pool's own balance.
  `LocalShieldBatch` pulls each note's value and fee legs from the shielder.

  The fee module's split and the order of fee-leg payments follow the code; a callback
  from the fee module's `recordShieldFee` (re-check RD-3) is added when callbacks are
  modelled.
-/
import ArmadaLean.Cctp.HubChain

namespace ArmadaLean.Cctp

/-- The pre-fee note values of an inbound SHIELD payload (ShieldModule.sol:107-124): the
    recipient note (first) gets the amount received minus the fee notes' declared values;
    every later note gets its declared value. -/
def inboundValues (received : Nat) (notes : List ShieldData) : List Nat :=
  match notes with
  | [] => []
  | _ :: rest =>
      let feeSum := (rest.map (fun n => n.value.val)).sum
      (received - feeSum) :: rest.map (fun n => n.value.val)

/-- The preimages credited for a list of notes with their pre-fee values and fee legs, in
    token `t`: each note keeps its value minus its fee. -/
def creditedPreimages (t : Term) (notes : List ShieldData) (vals : List Nat) (legs : List FeeLeg) :
    List CommitmentPreimage :=
  (notes.zip (vals.zip legs)).map fun x => ⟨x.1.npk, ⟨t⟩, x.2.1 - x.2.2.fee⟩

/-- The hub's CCTP shield handler (`handleReceiveFinalizedMessage` /
    `handleReceiveUnfinalizedMessage` → `_handleCCTPMessage` → `processIncomingShield`,
    PrivacyPool.sol:199-292; ShieldModule.sol:101-140), run by `caller` on a burn from domain
    `src` with body `body`, executed fee `feeExecuted` and executed finality `executed`.
    `finalized` says which of the two handlers is called. `legs` is the fee module's split
    per note (the adversary's choice within `FeeOK`). -/
def HubChain.HandleShield (s : HubChain) (caller : Term) (finalized : Bool) (executed : Nat)
    (src : Domain) (body : BurnBody) (feeExecuted : Nat) (legs : List FeeLeg) (s' : HubChain) :
    Prop :=
  (caller = s.hub.tokenMessenger ∨ s.hub.hookRouter = some caller) ∧                -- DS1
  (if finalized = true then 2000 ≤ executed else 1000 ≤ executed) ∧                 -- DS2
  ∃ notes : List ShieldData, body.hookData = .shield notes ∧                         -- DS3, DS4
  s.hub.remotePools src ≠ Bytes32.zero ∧                                             -- DS5
  body.messageSender = s.hub.remotePools src ∧                                       -- DS6 (whole word)
  (∃ pc, s.pauseView = some pc ∧ pc.shieldsPaused = false) ∧                         -- DS8
  notes ≠ [] ∧                                                                       -- DS9
  let received := body.amount - feeExecuted
  let vals := inboundValues received notes
  ((notes.drop 1).map (fun n => n.value.val)).sum < received ∧                        -- DS10
  received ≤ (notes.map (fun n => n.value.val)).sum ∧                                -- DS11
  (∀ n ∈ notes, Canonical n.npk) ∧ (∀ v ∈ vals, 0 < v) ∧                              -- DS12
  s.hub.blocklist s.hub.usdc = false ∧                                               -- DS12b
  ∃ priv, s.privileged caller = some priv ∧                                          -- DS13
  legs.length = notes.length ∧
  (∀ x ∈ notes.zip (vals.zip legs), s.FeeOK priv x.2.1 x.1.integrator x.2.2) ∧        -- DS14, DS16
  ∃ L', payLegs s.ledger s.hub.usdc s.hub.self s.hub.treasury legs = some L' ∧       -- DS15
  let pres := creditedPreimages s.hub.usdc notes vals legs
  s' = { s with
          ledger := L',
          comps := s.comps.addPending (s.recordedRevenue priv legs),
          hub := { s.hub with pool := creditBatch s.hub.pool pres },
          events := s.events ++ [batchEvent s.hub.pool pres] }

/-- One request of a local shield (`ShieldRequest`, ShieldModule.sol:45-90): the note key,
    the token, and the gross value, a `uint120`. -/
structure ShieldRequest where
  npk : Term
  token : Term
  value : {v : Nat // v < 2 ^ 120}
  deriving DecidableEq

/-- Pull one request's tokens from the shielder (ShieldModule.sol:303-385): the note's value
    minus its fee into the pool, and the fee legs to the treasury and the integrator. The
    pool's exact balance-change check (ShieldModule.sol:321-324,341-343) always holds for a
    ledger transfer; a token that lies about balances is an environment step. -/
def pullRequest (L : Ledger) (pool caller treasury : Term) (r : ShieldRequest) (leg : FeeLeg) :
    Option Ledger :=
  (L.transferFrom r.token pool caller pool (r.value.val - leg.fee)).bind fun L₁ =>
    payLeg L₁ r.token caller treasury leg

/-- Pull every request of a batch in order; any failure reverts the batch. -/
def pullRequests (L : Ledger) (pool caller treasury : Term) :
    List (ShieldRequest × FeeLeg) → Option Ledger
  | [] => some L
  | x :: xs => (pullRequest L pool caller treasury x.1 x.2).bind fun L₁ =>
      pullRequests L₁ pool caller treasury xs

/-- A batched local shield by `caller` with integrator `integrator` (`PrivacyPool.shield` →
    `ShieldModule.shield`, PrivacyPool.sol:138-140; ShieldModule.sol:45-90). `legs` is the
    fee split per request. -/
def HubChain.LocalShieldBatch (s : HubChain) (caller : Term) (integrator : Option Term)
    (reqs : List ShieldRequest) (legs : List FeeLeg) (s' : HubChain) : Prop :=
  reqs ≠ [] ∧                                                                        -- LS0
  s.hub.guardOn = false ∧                                                            -- LS1
  (∃ pc, s.pauseView = some pc ∧ pc.shieldsPaused = false) ∧                         -- LS2
  (∀ r ∈ reqs, 0 < r.value.val ∧ s.hub.blocklist r.token = false ∧ Canonical r.npk) ∧  -- LS4-LS6
  ∃ priv, s.privileged caller = some priv ∧                                          -- LS7
  legs.length = reqs.length ∧
  (∀ x ∈ reqs.zip legs, s.FeeOK priv x.1.value.val integrator x.2) ∧                  -- LS8
  ∃ L', pullRequests s.ledger s.hub.self caller s.hub.treasury (reqs.zip legs) = some L' ∧  -- LS9, LS10
  let pres := (reqs.zip legs).map fun x => (⟨x.1.npk, ⟨x.1.token⟩, x.1.value.val - x.2.fee⟩ : CommitmentPreimage)
  s' = { s with
          ledger := L',
          comps := s.comps.addPending (s.recordedRevenue priv legs),
          hub := { s.hub with pool := creditBatch s.hub.pool pres },
          events := s.events ++ [batchEvent s.hub.pool pres] }

end ArmadaLean.Cctp
