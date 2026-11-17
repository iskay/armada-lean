-- ABOUTME: The hub chain's state in the CCTP model: the hub pool with Circle, the ledger, components, routers and yield.
-- ABOUTME: Shared helpers for hub steps: pause and registry views, canonical field elements, batch crediting, fee legs.
/-
  ArmadaLean.Cctp.HubChain — the state one hub-chain transaction acts on, and helpers its
  steps share.

  Design record: model sheet v2.1 §4 and §5. One hub transaction may touch the pool, Circle's
  contracts, the token ledger, the shared components and the yield contracts, so a hub
  step relates two `HubChain` states. The hub steps (`ArmadaLean.Cctp.HubShield`,
  `ArmadaLean.Cctp.HubTransact`) use exactly the contract's checks; the pool model's ghost
  bookkeeping (`PoolState.live`, `PoolState.held`) is updated from what the step reveals,
  not from a private witness. A transaction accepted under a degenerate or trapdoor key
  has no witness, and the model must still let it happen (model sheet v2.1 §3.2).

  A step that calls into untrusted code (a token with hooks, the fee module, Aave) takes a
  callback frame `F` and opens it at each such call, between the effects the code has
  applied and those it has not (model sheet v2.1 §5.0, decision RD-3 (a)).
-/
import ArmadaLean.Cctp.Circle
import ArmadaLean.Cctp.Shared
import ArmadaLean.Cctp.Hub
import ArmadaLean.Cctp.Router
import ArmadaLean.Cctp.Yield
import ArmadaLean.Cctp.Client

namespace ArmadaLean.Cctp

/-- A ghost record of one `Shield` or `Transact` event: the tree and start index it reports,
    and the leaves it announces (ShieldModule.sol:135-138; TransactModule.sol:86-90). Wallets
    find notes by these events. -/
structure LeafEvent where
  tree : Nat
  start : Nat
  leaves : List Term
  deriving DecidableEq

/-- A signed hub gasless shield intent (GaslessShieldWrapper.sol:60-62,149-169): the user, the
    shield requests (bound by their hash), the integrator, a deadline and the user's nonce. -/
structure HubIntent where
  user : Term
  reqs : List ShieldRequest
  integrator : Option Term
  deadline : Nat
  nonce : Nat
  deriving DecidableEq

/-- The hub's gasless wrapper (GaslessShieldWrapper.sol:42-105): its own address, its immutable
    USDC and pool (non-zero, otherwise unchecked), each user's next nonce, and the intents and
    permits their owners have signed. -/
structure HubGasless where
  self : Term
  usdc : Term
  privacyPool : Term
  nonces : Term → Nat
  signedIntents : List HubIntent
  signedPermits : List Permit
  usedPermits : List Permit

/-- The hub chain's state. `burns` and `generics` are ghost records of the burns and generic
    messages this chain's transactions created; the attestation service reads them, and a reorg
    that drops a transaction drops its record. -/
structure HubChain where
  hub : HubState
  circle : CircleChain
  ledger : Ledger
  comps : Components
  routers : Term → Option RouterState
  yield : YieldState
  events : List LeafEvent
  burns : List BurnRecord
  generics : List GenericMessage
  gasless : HubGasless

/-- A term is a canonical field element: a number below the BN254 scalar field prime, or a
    hash output (which is one by construction). The pools require note keys to be canonical
    (`npk < SNARK_SCALAR_FIELD`, ShieldModule.sol:283-292; PrivacyPoolClient.sol:340-343). -/
def Canonical (t : Term) : Prop := ∀ n, t = Term.val n → n < p

/-- The pause controller's views as the pool reads them (ShieldModule.sol:442-449;
    TransactModule.sol:476-497): with no controller set, nothing is paused; a reverting
    controller makes the calling transaction revert (`none`). -/
def HubChain.pauseView (s : HubChain) : Option PauseController :=
  match s.hub.pauseController with
  | none => some { shieldsPaused := false, withdrawOnly := false, emergencyPaused := false,
                   windDownActive := false, reverts := false }
  | some a => if (s.comps.pause a).reverts = true then none else some (s.comps.pause a)

/-- Whether `caller` is a fee-exempt (privileged) shielder (ShieldModule.sol:258-263):
    authorized or withdraw-only in the adapter registry. With no registry set, nobody is;
    a reverting registry makes the calling transaction revert (`none`), which is how a bad
    registry setting stops every shield (finding N-2). -/
def HubChain.privileged (s : HubChain) (caller : Term) : Option Bool :=
  match s.hub.adapterRegistry with
  | none => some false
  | some a =>
      let r := s.comps.registry a
      if r.reverts = true then none else some (r.authorized caller || r.withdrawOnly caller)

/-- One note's shield-fee legs: the total fee deducted from the note, the protocol's take
    paid to the treasury, and the integrator's share paid to the integrator. -/
structure FeeLeg where
  fee : Nat
  armadaTake : Nat
  integratorFee : Nat
  integrator : Option Term
  deriving DecidableEq

/-- The shield-fee rule for one note of pre-fee value `value` (ShieldModule.sol:176-250,
    303-415). A privileged caller pays nothing. With a fee module set, the module (which
    must not revert and must name this pool, ArmadaFeeModule.sol:166) returns a split the
    pool accepts only if its parts sum to the total, an integrator fee has an integrator,
    and the total is at most 15% (`_requireValidFeeSplit`, ShieldModule.sol:237-250); the
    split is otherwise the adversary's choice. With no module, the flat fee
    `shieldFee feeRatio value` all goes to the treasury. -/
def HubChain.FeeOK (s : HubChain) (priv : Bool) (value : Nat) (integrator : Option Term)
    (leg : FeeLeg) : Prop :=
  if priv = true then leg.fee = 0 ∧ leg.armadaTake = 0 ∧ leg.integratorFee = 0
  else match s.hub.feeModule with
    | some m =>
        (s.comps.feeModule m).reverts = false ∧ (s.comps.feeModule m).privacyPool = s.hub.self ∧
        leg.armadaTake + leg.integratorFee = leg.fee ∧
        (leg.integratorFee = 0 ∨ (leg.integrator = integrator ∧ integrator.isSome)) ∧
        leg.fee * 10000 ≤ value * 1500
    | none =>
        leg.fee = shieldFee s.hub.pool.feeRatio value ∧ leg.armadaTake = leg.fee ∧
        leg.integratorFee = 0

/-- The wind-down revenue a shield records (`recordShieldFee`, ArmadaFeeModule.sol:159-198):
    the protocol takes of its notes in the module's USDC, on the fee-module path, when that
    module is the fee collector the revenue counter reads; nothing for a privileged caller or
    the flat path. `fees` pairs each note's token with its fee legs. -/
def HubChain.recordedRevenue (s : HubChain) (priv : Bool) (fees : List (Term × FeeLeg)) : Nat :=
  match s.hub.feeModule with
  | some m =>
      if priv = false ∧ m = s.comps.windDown.feeCollector then
        ((fees.filter (fun x => x.1 = (s.comps.feeModule m).usdc)).map (·.2.armadaTake)).sum
      else 0
  | none => 0

/-- Add recorded fee revenue to the wind-down contract's pending (unsynced) revenue. -/
def Components.addPending (c : Components) (n : Nat) : Components :=
  { c with windDown := { c.windDown with pending := c.windDown.pending + n } }

/-- Pay one note's fee legs in token `t` from `payer` (the pool itself on the inbound path,
    the shielder on the local path): the protocol take to the treasury, the integrator fee
    to the integrator, each only when positive (ShieldModule.sol:196-222, 325-363). -/
def payLeg (L : Ledger) (t payer treasury : Term) (leg : FeeLeg) : Option Ledger :=
  let afterTake := if leg.armadaTake = 0 then some L else L.transfer t payer treasury leg.armadaTake
  afterTake.bind fun L₁ =>
    match leg.integrator with
    | some i => if leg.integratorFee = 0 then some L₁ else L₁.transfer t payer i leg.integratorFee
    | none => if leg.integratorFee = 0 then some L₁ else none

/-- Pay a list of fee legs in order; any failed transfer reverts the whole list. -/
def payLegs (L : Ledger) (t payer treasury : Term) : List FeeLeg → Option Ledger
  | [] => some L
  | leg :: legs => (payLeg L t payer treasury leg).bind fun L₁ => payLegs L₁ t payer treasury legs

/-- A callback frame (model sheet v2.1 §5.0): what the environment may do while an outer step
    has called into untrusted code. The effects the outer step applied so far are visible; the
    outer step then continues on the state the frame leaves and re-reads what the code
    re-reads. The steps take the frame as a parameter; the machine
    (`ArmadaLean.Cctp.System`) supplies it. -/
abbrev Frame := HubChain → HubChain → Prop

/-- Tokens whose code makes no external calls: the hub's USDC (Circle's FiatToken, under the
    wiring hypothesis, model sheet departure X-25) and the vault's share token (an OpenZeppelin
    ERC-20). Every other token is untrusted code. -/
def HubChain.TrustedToken (s : HubChain) (t : Term) : Prop :=
  t = s.hub.usdc ∨ t = s.yield.vault.self

/-- A call into token `t` that applies `op` to the ledger. A trusted token makes no callbacks;
    any other token may open a frame before and after its balance change. -/
def HubChain.TokenCall (s : HubChain) (F : Frame) (t : Term) (op : Ledger → Option Ledger)
    (s' : HubChain) : Prop :=
  s.TrustedToken t ∧ (∃ L', op s.ledger = some L' ∧ s' = { s with ledger := L' }) ∨
  ¬ s.TrustedToken t ∧ ∃ s₁ L₂, F s s₁ ∧ op s₁.ledger = some L₂ ∧ F { s₁ with ledger := L₂ } s'

/-- The pool's `recordShieldFee` call on the fee-module path (ShieldModule.sol:206-212,357-363):
    the recorded revenue, then a frame, since the fee module is untrusted code. Nothing on the
    flat path or for a privileged caller. `fees` pairs each note's token with its fee legs. -/
def HubChain.RecordFee (s : HubChain) (F : Frame) (priv : Bool) (fees : List (Term × FeeLeg))
    (s' : HubChain) : Prop :=
  (∃ m, s.hub.feeModule = some m ∧ priv = false ∧
    F { s with comps := s.comps.addPending (s.recordedRevenue priv fees) } s') ∨
  ((s.hub.feeModule = none ∨ priv = true) ∧ s' = s)

/-- Credit a batch of new notes to the pool model's state: their commitments go into one
    Merkle batch (the whole batch moves to a new tree if it would overflow the current one,
    `insertLeaves`, MerkleModule.sol:62-70), each note becomes live at its position, and
    each token's ghost custody grows by its notes' values. -/
def creditBatch (ps : PoolState) (pres : List CommitmentPreimage) : PoolState :=
  let leaves := pres.map hashCommitment
  let tn := insertTree ps.trees leaves.length
  let pos := insertStart ps.trees leaves.length
  { ps with
      live := fun t => (withTreePositionsFrom tn pos pres).filter (fun e => e.2.token = t) ++ ps.live t,
      held := fun t => ps.held t + ((pres.filter (fun pre => pre.token = t)).map (·.value)).sum,
      trees := insertLeaves ps.trees leaves }

/-- The event record of a credited batch: the tree and start index the batch lands at. -/
def batchEvent (ps : PoolState) (pres : List CommitmentPreimage) : LeafEvent :=
  let leaves := pres.map hashCommitment
  { tree := insertTree ps.trees leaves.length, start := insertStart ps.trees leaves.length,
    leaves := leaves }

end ArmadaLean.Cctp
