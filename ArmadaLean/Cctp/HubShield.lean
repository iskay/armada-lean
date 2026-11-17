-- ABOUTME: The hub's two shield steps: the CCTP inbound shield handler and the batched local shield.
-- ABOUTME: Each holds exactly when the contract's checks pass; guard IDs follow model sheet v2.1 §5.
/-
  ArmadaLean.Cctp.HubShield — the hub steps that create notes from tokens received.

  Design record: model sheet v2.1 §5.2 (hub shield handler, guards DS1-DS16) and §5.3
  (`localShieldBatch`, guards LS0-LS10). Both are relations between hub-chain states.

  `HandleShield` is the hub handler's part of an inbound delivery: by the time it runs,
  Circle's `receiveMessage` has minted the USDC to the pool (the router composes the two
  atomically, `ArmadaLean.Cctp.Delivery`). Its fee legs are paid from the pool's own balance.
  `LocalShieldBatch` pulls each note's value and fee legs from the shielder.

  The fee module's split and the order of fee-leg payments follow the code. Both steps run
  note by note and open a callback frame at each call into untrusted code: the fee module's
  `recordShieldFee`, and on the local path every pull of a token other than USDC and the
  vault's shares (model sheet v2.1 §5.0). The insertion position is read after the loop
  (ShieldModule.sol:77-78,135-136), so a frame that lands an inbound shield moves it.
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

/-- One note's fee on the inbound path (`_applyShieldFee`, ShieldModule.sol:176-225), on pre-fee
    value `value`: the fee legs paid in USDC from the pool, then the fee-module record. -/
def HubChain.InboundFee (s : HubChain) (F : Frame) (caller : Term) (integrator : Option Term)
    (value : Nat) (leg : FeeLeg) (s' : HubChain) : Prop :=
  ∃ priv, s.privileged caller = some priv ∧                                          -- DS13
  s.FeeOK priv value integrator leg ∧                                                -- DS14
  ∃ L', payLeg s.ledger s.hub.usdc s.hub.self s.hub.treasury leg = some L' ∧          -- DS15
  ({ s with ledger := L' } : HubChain).RecordFee F priv [(s.hub.usdc, leg)] s'       -- DS16

/-- The inbound path's fees note by note, each on the state the previous note's left. Each
    entry is a note's integrator, pre-fee value and fee legs. -/
inductive InboundRun (F : Frame) (caller : Term) :
    HubChain → List (Option Term × Nat × FeeLeg) → HubChain → Prop where
  | nil (s : HubChain) : InboundRun F caller s [] s
  | cons {s s₁ s' : HubChain} {x : Option Term × Nat × FeeLeg} {xs : List (Option Term × Nat × FeeLeg)}
      (hFee : s.InboundFee F caller x.1 x.2.1 x.2.2 s₁) (hRest : InboundRun F caller s₁ xs s') :
      InboundRun F caller s (x :: xs) s'

/-- The hub's CCTP shield handler (`handleReceiveFinalizedMessage` /
    `handleReceiveUnfinalizedMessage` → `_handleCCTPMessage` → `processIncomingShield`,
    PrivacyPool.sol:199-292; ShieldModule.sol:101-140), run by `caller` on a burn from domain
    `src` with body `body`, executed fee `feeExecuted` and executed finality `executed`.
    `finalized` says which of the two handlers is called. `legs` is the fee module's split
    per note (the adversary's choice within `FeeOK`). The handler has no re-entrancy guard
    (finding CB-10). -/
def HubChain.HandleShield (s : HubChain) (F : Frame) (caller : Term) (finalized : Bool)
    (executed : Nat) (src : Domain) (body : BurnBody) (feeExecuted : Nat) (legs : List FeeLeg)
    (s' : HubChain) : Prop :=
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
  legs.length = notes.length ∧
  ∃ s₁, InboundRun F caller s ((notes.map (·.integrator)).zip (vals.zip legs)) s₁ ∧  -- DS13-DS16
  let pres := creditedPreimages s.hub.usdc notes vals legs
  s' = { s₁ with
          hub := { s₁.hub with pool := creditBatch s₁.hub.pool pres },
          events := s₁.events ++ [batchEvent s₁.hub.pool pres] }

/-- One request of a local shield (`ShieldRequest`, ShieldModule.sol:45-90): the note key,
    the token, and the gross value, a `uint120`. -/
structure ShieldRequest where
  npk : Term
  token : Term
  value : {v : Nat // v < 2 ^ 120}
  deriving DecidableEq

/-- One request of a local shield by `caller` (`_validateCommitmentPreimage` then
    `_transferTokenIn`, ShieldModule.sol:62-74,269-385): the value net of fee pulled into the
    pool under the pool's exact balance-change check, then the fee legs pulled from the caller
    to the treasury and the integrator, then the fee-module record. Each pull is a call into
    the token. -/
def HubChain.ShieldIn (s : HubChain) (F : Frame) (caller : Term) (integrator : Option Term)
    (r : ShieldRequest) (leg : FeeLeg) (s' : HubChain) : Prop :=
  0 < r.value.val ∧ s.hub.blocklist r.token = false ∧ Canonical r.npk ∧              -- LS4-LS6
  ∃ priv, s.privileged caller = some priv ∧                                          -- LS7
  s.FeeOK priv r.value.val integrator leg ∧                                          -- LS8
  let pool := s.hub.self
  let base := r.value.val - leg.fee
  ∃ s₁, s.TokenCall F r.token (fun L => L.transferFrom r.token pool caller pool base) s₁ ∧  -- LS9
  s.ledger.balance r.token pool + base = s₁.ledger.balance r.token pool ∧
  ∃ s₂, (leg.armadaTake = 0 ∧ s₂ = s₁ ∨ 0 < leg.armadaTake ∧                         -- LS10
    s₁.TokenCall F r.token
      (fun L => L.transferFrom r.token pool caller s.hub.treasury leg.armadaTake) s₂) ∧
  ∃ s₃, (leg.integratorFee = 0 ∧ s₃ = s₂ ∨ ∃ i, 0 < leg.integratorFee ∧ leg.integrator = some i ∧
    s₂.TokenCall F r.token (fun L => L.transferFrom r.token pool caller i leg.integratorFee) s₃) ∧
  s₃.RecordFee F priv [(r.token, leg)] s'                                            -- LS8

/-- A local shield's requests in order, each on the state the previous one left. -/
inductive ShieldRun (F : Frame) (caller : Term) (integrator : Option Term) :
    HubChain → List (ShieldRequest × FeeLeg) → HubChain → Prop where
  | nil (s : HubChain) : ShieldRun F caller integrator s [] s
  | cons {s s₁ s' : HubChain} {x : ShieldRequest × FeeLeg} {xs : List (ShieldRequest × FeeLeg)}
      (hIn : s.ShieldIn F caller integrator x.1 x.2 s₁) (hRest : ShieldRun F caller integrator s₁ xs s') :
      ShieldRun F caller integrator s (x :: xs) s'

/-- A batched local shield by `caller` with integrator `integrator` (`PrivacyPool.shield` →
    `ShieldModule.shield`, PrivacyPool.sol:138-140; ShieldModule.sol:45-90). `legs` is the
    fee split per request. The re-entrancy guard is held for the whole batch. -/
def HubChain.LocalShieldBatch (s : HubChain) (F : Frame) (caller : Term) (integrator : Option Term)
    (reqs : List ShieldRequest) (legs : List FeeLeg) (s' : HubChain) : Prop :=
  reqs ≠ [] ∧                                                                        -- LS0
  s.hub.guardOn = false ∧                                                            -- LS1
  (∃ pc, s.pauseView = some pc ∧ pc.shieldsPaused = false) ∧                         -- LS2
  legs.length = reqs.length ∧
  ∃ s₁, ShieldRun F caller integrator { s with hub := { s.hub with guardOn := true } }  -- LS4-LS10
    (reqs.zip legs) s₁ ∧
  let pres := (reqs.zip legs).map fun x => (⟨x.1.npk, ⟨x.1.token⟩, x.1.value.val - x.2.fee⟩ : CommitmentPreimage)
  s' = { s₁ with
          hub := { s₁.hub with guardOn := false, pool := creditBatch s₁.hub.pool pres },
          events := s₁.events ++ [batchEvent s₁.hub.pool pres] }

end ArmadaLean.Cctp
