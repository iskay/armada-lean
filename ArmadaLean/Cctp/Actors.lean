-- ABOUTME: Owner, governance, any-actor and plain token steps of the CCTP model, on the hub chain and a client chain.
-- ABOUTME: Each setter holds exactly when the contract lets that caller make that change; the owner is adversarial.
/-
  ArmadaLean.Cctp.Actors — the steps that change configuration, and plain token actions.

  Design record: model sheet v2.1 §5.5 (owner, governance and any-actor steps) under
  decision D1 (a): the owner and governance are adversarial, so every setter may write any
  value its contract accepts, at any time. Plain token actions (transfer, approve) let any
  holder move tokens, including donating to a pool, which raises the pool's balance without
  a note (catalogue item 87).

  The pause controller: an owner installs a controller by pointing the hub at it
  (`setShieldPauseContract`, PrivacyPool.sol:468-472); the components map holds a controller
  state for every address, so pointing at an address picks any flags. Governance wind-down,
  and the any-actor trigger, set the shipped controller's wind-down flags at the address the
  wind-down contract names (ShieldPauseController.sol:80-90,158-166).
-/
import ArmadaLean.Cctp.ClientChain

namespace ArmadaLean.Cctp

/-! ### Hub owner -/

/-- An owner step on the hub (PrivacyPool.sol:300-482), as a configuration change. -/
inductive HubOwnerOp where
  | setRemotePool (d : Domain) (w : Bytes32)
  | setRemoteHookRouter (d : Domain) (w : Bytes32)
  | setHookRouter (a : Term)
  | setAdapterRegistry (a : Term)
  | setVerificationKey (sh : Shape) (k : VKey)
  | setShieldFee (r : FeeRatio)
  | setFeeModule (a : Option Term)
  | setShieldPauseContract (a : Option Term)
  | setDefaultFinality (f : RequestedFinality)
  | addToBlocklist (t : Term)
  | removeFromBlocklist (t : Term)
  | transferOwnership (n : Option Term)

/-- The checks each hub owner step makes beyond the caller being the owner: set-once and
    non-zero for the hook router (PrivacyPool.sol:439-445) and the registry (:421-427); the flat
    fee only while no fee module is wired, in basis points, within the cap (:404-410); default
    finality FAST or STANDARD (:454-462); USDC never blocklisted (:356). -/
def HubOwnerOp.Allowed (h : HubState) : HubOwnerOp → Prop
  | .setHookRouter a => h.hookRouter = none ∧ a ≠ Term.val 0
  | .setAdapterRegistry a => h.adapterRegistry = none ∧ a ≠ Term.val 0
  | .setShieldFee r => h.feeModule = none ∧ r.den = 10000
  | .setDefaultFinality f => f = .fast ∨ f = .standard
  | .addToBlocklist t => t ≠ h.usdc
  | _ => True

/-- The effect of a hub owner step. -/
def HubOwnerOp.apply (h : HubState) : HubOwnerOp → HubState
  | .setRemotePool d w => { h with remotePools := fun d' => if d' = d then w else h.remotePools d' }
  | .setRemoteHookRouter d w =>
      { h with remoteHookRouters := fun d' => if d' = d then w else h.remoteHookRouters d' }
  | .setHookRouter a => { h with hookRouter := some a }
  | .setAdapterRegistry a => { h with adapterRegistry := some a }
  | .setVerificationKey sh k =>
      { h with verificationKeys := fun sh' => if sh' = sh then some k else h.verificationKeys sh' }
  | .setShieldFee r => { h with pool := { h.pool with feeRatio := r } }
  | .setFeeModule a => { h with feeModule := a }
  | .setShieldPauseContract a => { h with pauseController := a }
  | .setDefaultFinality f => { h with defaultFinality := some f }
  | .addToBlocklist t => { h with blocklist := fun t' => if t' = t then true else h.blocklist t' }
  | .removeFromBlocklist t => { h with blocklist := fun t' => if t' = t then false else h.blocklist t' }
  | .transferOwnership n => { h with pendingOwner := n }

/-- A hub owner step by `caller`. -/
def HubChain.OwnerStep (s : HubChain) (caller : Term) (op : HubOwnerOp) (s' : HubChain) : Prop :=
  caller = s.hub.owner ∧ op.Allowed s.hub ∧ s' = { s with hub := op.apply s.hub }

/-- Accepting a pending hub ownership transfer (PrivacyPool.sol:313-319). -/
def HubChain.AcceptOwnership (s : HubChain) (caller : Term) (s' : HubChain) : Prop :=
  s.hub.pendingOwner = some caller ∧
  s' = { s with hub := { s.hub with owner := caller, pendingOwner := none } }

/-! ### Client owner -/

/-- An owner step on a client (PrivacyPoolClient.sol:405-479). -/
inductive ClientOwnerOp where
  | setHubPool (d : Domain) (w : Bytes32)
  | setHookRouter (a : Term)
  | setHubHookRouter (w : Bytes32)
  | setDefaultFinality (f : RequestedFinality)
  | transferOwnership (n : Option Term)

/-- The checks each client owner step makes beyond the caller being the owner: set-once and
    non-zero for the hook router (PrivacyPoolClient.sol:444-450); default finality FAST or
    STANDARD (:471-479). -/
def ClientOwnerOp.Allowed (c : ClientState) : ClientOwnerOp → Prop
  | .setHookRouter a => c.hookRouter = none ∧ a ≠ Term.val 0
  | .setDefaultFinality f => f = .fast ∨ f = .standard
  | _ => True

/-- The effect of a client owner step. -/
def ClientOwnerOp.apply (c : ClientState) : ClientOwnerOp → ClientState
  | .setHubPool d w => { c with hubDomain := d, hubPool := w }
  | .setHookRouter a => { c with hookRouter := some a }
  | .setHubHookRouter w => { c with hubHookRouter := w }
  | .setDefaultFinality f => { c with defaultFinality := some f }
  | .transferOwnership n => { c with pendingOwner := n }

/-- A client owner step by `caller`. -/
def ClientChain.OwnerStep (s : ClientChain) (caller : Term) (op : ClientOwnerOp) (s' : ClientChain) :
    Prop :=
  caller = s.client.owner ∧ op.Allowed s.client ∧ s' = { s with client := op.apply s.client }

/-- Accepting a pending client ownership transfer (PrivacyPoolClient.sol:414-420). -/
def ClientChain.AcceptOwnership (s : ClientChain) (caller : Term) (s' : ClientChain) : Prop :=
  s.client.pendingOwner = some caller ∧
  s' = { s with client := { s.client with owner := caller, pendingOwner := none } }

/-! ### Governance and any actor -/

/-- A governance step on the hub chain's shared components: any adapter-registry contents, any
    fee-module parameters (including the single pool it serves and whether it reverts), any
    pause-controller state at an address governance controls. -/
inductive GovOp where
  | setRegistry (a : Term) (r : AdapterRegistry)
  | setFeeModule (a : Term) (f : FeeModule)
  | setController (a : Term) (pc : PauseController)

/-- The effect of a governance step. -/
def GovOp.apply (c : Components) : GovOp → Components
  | .setRegistry a r => { c with registry := fun a' => if a' = a then r else c.registry a' }
  | .setFeeModule a f => { c with feeModule := fun a' => if a' = a then f else c.feeModule a' }
  | .setController a pc => { c with pause := fun a' => if a' = a then pc else c.pause a' }

/-- A governance step. Governance is adversarial (D1 (a)); a step it takes needs no other check. -/
def HubChain.GovStep (s : HubChain) (op : GovOp) (s' : HubChain) : Prop :=
  s' = { s with comps := op.apply s.comps }

/-- Wind-down's effect: the trigger is set, and the controller the wind-down contract names
    pauses shields and enters withdraw-only mode, permanently (ShieldPauseController.sol:80-90). -/
def Components.windDownNow (c : Components) : Components :=
  let a := c.windDown.pauseController
  { c with
      windDown := { c.windDown with triggered := true },
      pause := fun a' => if a' = a then
        { c.pause a with windDownActive := true, shieldsPaused := true, withdrawOnly := true }
        else c.pause a' }

/-- Governance winds down at any time (ArmadaWindDown.sol:176+). -/
def HubChain.GovWindDown (s : HubChain) (s' : HubChain) : Prop :=
  s.comps.windDown.triggered = false ∧ s' = { s with comps := s.comps.windDownNow }

/-- Anyone syncs fee revenue into the wind-down counter (`syncStablecoinRevenue`). -/
def HubChain.SyncRevenue (s : HubChain) (s' : HubChain) : Prop :=
  s' = { s with comps := { s.comps with windDown := { s.comps.windDown with
          revenue := s.comps.windDown.revenue + s.comps.windDown.pending, pending := 0 } } }

/-- Anyone triggers wind-down once the deadline has passed and recognized revenue is below the
    threshold (`triggerWindDown`, ArmadaWindDown.sol:153-174). The best-effort sync before the
    check (:167) may succeed (`synced`) or fail, leaving the recognized revenue stale. -/
def HubChain.TriggerWindDown (s : HubChain) (now : Nat) (synced : Bool) (s' : HubChain) : Prop :=
  let w := s.comps.windDown
  let recognized := if synced = true then w.revenue + w.pending else w.revenue
  w.triggered = false ∧ w.deadline < now ∧ recognized < w.threshold ∧
  s' = { s with comps := { s.comps.windDownNow with windDown := { s.comps.windDownNow.windDown with
          revenue := recognized, pending := if synced = true then 0 else w.pending } } }

/-! ### Plain token actions -/

/-- A holder transfers tokens to anyone (a donation when the recipient is a pool). -/
def HubChain.TokenTransfer (s : HubChain) (caller t dst : Term) (amt : Nat) (s' : HubChain) : Prop :=
  ∃ L', s.ledger.transfer t caller dst amt = some L' ∧ s' = { s with ledger := L' }

/-- A holder approves a spender. -/
def HubChain.TokenApprove (s : HubChain) (caller t sp : Term) (amt : Nat) (s' : HubChain) : Prop :=
  ∃ L', s.ledger.approve t caller sp amt = some L' ∧ s' = { s with ledger := L' }

/-- A holder transfers tokens on a client chain. -/
def ClientChain.TokenTransfer (s : ClientChain) (caller t dst : Term) (amt : Nat) (s' : ClientChain) :
    Prop :=
  ∃ L', s.ledger.transfer t caller dst amt = some L' ∧ s' = { s with ledger := L' }

/-- A holder approves a spender on a client chain. -/
def ClientChain.TokenApprove (s : ClientChain) (caller t sp : Term) (amt : Nat) (s' : ClientChain) :
    Prop :=
  ∃ L', s.ledger.approve t caller sp amt = some L' ∧ s' = { s with ledger := L' }

end ArmadaLean.Cctp
