-- ABOUTME: The CCTP model's machine: the hub chain and the client chains as canonical logs, Iris, and the clock.
-- ABOUTME: Every transaction kind on each chain, its execution with callback frames by nesting depth, and the steps.
/-
  ArmadaLean.Cctp.System — the composed machine `Cctp.system` (model sheet v2.1 §4, §5).

  The system holds the hub chain and every client chain as canonical logs
  (`ArmadaLean.Cctp.Chain`), the attestation service and the clock. A transaction is one
  public entry point with its arguments and the choices the code leaves open (fee splits,
  ghost decodings, burn records). A transaction reads its own chain's state and the context:
  the attestations issued so far and the time, both read at execution time, so a reorg
  re-executes against the context of the reorg.

  Callback frames (model sheet v2.1 §5.0, decision RD-3 (a)). The hub's steps take a frame
  (`Frame`). `hubFrame ctx n` is a frame of nesting depth at most `n`: depth zero changes
  nothing, depth `n + 1` is any sequence of hub transactions whose own frames have depth at
  most `n`. A step succeeds at some depth (`HubChain.Step`), so every finite nesting is
  covered, and the definition is plain recursion on `n`. A frame may run any hub
  transaction, not only those an untrusted callee could submit: a superset of the real
  behaviours, which keeps every safety statement sound. Client chains need no frames
  (`ArmadaLean.Cctp.Delivery`).

  Environment limits read here: a ledger change never touches the vault's share token and
  never rewrites the chain's stored USDC (model sheet departure X-25); Iris attests only
  burns and generic messages its source chain holds (canonical) or has finalized.
-/
import ArmadaLean.Machine
import ArmadaLean.Cctp.Chain
import ArmadaLean.Cctp.HubGasless
import ArmadaLean.Cctp.HubYield
import ArmadaLean.Cctp.Delivery
import ArmadaLean.Cctp.Actors
import ArmadaLean.Cctp.Env

namespace ArmadaLean.Cctp

/-- What a transaction reads beyond its chain's state: the attestation service and the time. -/
structure Ctx where
  iris : Iris
  now : Nat

/-! ### Hub chain transactions -/

/-- A transaction on the hub chain (model sheet v2.1 §5). -/
inductive HubTxn (C : Crypto) where
  | localShield (caller : Term) (integrator : Option Term) (reqs : List ShieldRequest)
      (legs : List FeeLeg)
  | localTransact (caller : Term) (txs : List (HubTx C)) (decoded : List (Option CommitmentPreimage))
  | atomicUnshield (caller txOrigin : Term) (tx : HubTx C) (d : Domain) (finalRecipient : Term)
      (maxFee : Nat) (uniqueNonce : Term) (rec : BurnRecord)
      (decoded : List (Option CommitmentPreimage))
  | relay (rt : Term) (att : Attestation) (legs : List FeeLeg)
  | directReceive (caller : Term) (att : Attestation) (legs : List FeeLeg)
  | handlerCall (caller : Term) (finalized : Bool) (executed : Nat) (src : Domain) (body : BurnBody)
      (feeExecuted : Nat) (legs : List FeeLeg)
  | lendAndShield (tx : HubTx C) (npk ct : Term) (decoded : List (Option CommitmentPreimage))
      (legs : List FeeLeg)
  | redeemAndShield (tx : HubTx C) (npk ct feeNpk feeCt : Term) (feeAmount : Nat)
      (decoded : List (Option CommitmentPreimage)) (legs : List FeeLeg)
  | vaultDeposit (caller receiver : Term) (assets shares : Nat)
  | vaultRedeem (caller receiver owner : Term) (shares assets : Nat)
  | harvest
  | vaultOwner (caller : Term) (op : VaultOwnerOp)
  | adapterOwner (caller : Term) (op : AdapterOwnerOp)
  | owner (caller : Term) (op : HubOwnerOp)
  | acceptOwnership (caller : Term)
  | gov (op : GovOp)
  | govWindDown
  | syncRevenue
  | triggerWindDown (synced : Bool)
  | signIntent (signer : Term) (i : HubIntent)
  | signPermit (signer : Term) (pm : Permit)
  | submitPermit (pm : Permit)
  | gaslessShield (i : HubIntent) (legs : List FeeLeg)
  | transfer (caller t dst : Term) (amt : Nat)
  | transferFrom (caller t src dst : Term) (amt : Nat)
  | approve (caller t sp : Term) (amt : Nat)
  | foreignBurn (burner txOrigin : Term) (rec : BurnRecord)
  | sendGeneric (sender : Term) (g : GenericMessage)
  | circle (op : CircleOp)
  | ledger (op : LedgerOp)
  | aave (op : AaveOp)

/-- A ledger change the environment may make on the hub chain: never the vault's share token,
    never a rewrite of the hub's USDC. -/
def HubChain.LedgerOpAllowed (s : HubChain) (op : LedgerOp) : Prop :=
  op.Allowed s.hub.usdc ∧ op.token ≠ s.yield.vault.self

/-- One hub transaction's execution with callback frame `F` in context `ctx`. -/
def HubChain.Exec {C : Crypto} (s : HubChain) (F : Frame) (ctx : Ctx) : HubTxn C → HubChain → Prop
  | .localShield caller integrator reqs legs => s.LocalShieldBatch F caller integrator reqs legs
  | .localTransact caller txs decoded => s.LocalTransactBatch F caller txs decoded
  | .atomicUnshield caller txOrigin tx d finalRecipient maxFee uniqueNonce rec decoded =>
      s.AtomicUnshield caller txOrigin tx d finalRecipient maxFee uniqueNonce rec decoded
  | .relay rt att legs => s.Relay F ctx.iris ctx.now rt att legs
  | .directReceive caller att legs => s.DirectReceive F ctx.iris ctx.now caller att legs
  | .handlerCall caller finalized executed src body feeExecuted legs =>
      s.HandlerCall F caller finalized executed src body feeExecuted legs
  | .lendAndShield tx npk ct decoded legs => s.LendAndShield F tx npk ct decoded legs
  | .redeemAndShield tx npk ct feeNpk feeCt feeAmount decoded legs =>
      s.RedeemAndShield F ctx.now tx npk ct feeNpk feeCt feeAmount decoded legs
  | .vaultDeposit caller receiver assets shares => s.VaultDeposit F caller receiver assets shares
  | .vaultRedeem caller receiver owner shares assets =>
      s.VaultRedeem F ctx.now caller receiver owner shares assets
  | .harvest => s.Harvest F ctx.now
  | .vaultOwner caller op => s.VaultOwnerStep caller op
  | .adapterOwner caller op => s.AdapterOwnerStep caller op
  | .owner caller op => s.OwnerStep caller op
  | .acceptOwnership caller => s.AcceptOwnership caller
  | .gov op => s.GovStep op
  | .govWindDown => s.GovWindDown
  | .syncRevenue => s.SyncRevenue
  | .triggerWindDown synced => s.TriggerWindDown ctx.now synced
  | .signIntent signer i => s.SignIntent signer i
  | .signPermit signer pm => s.SignPermit signer pm
  | .submitPermit pm => s.SubmitPermit ctx.now pm
  | .gaslessShield i legs => s.GaslessShield F ctx.now i legs
  | .transfer caller t dst amt => s.TokenTransfer caller t dst amt
  | .transferFrom caller t src dst amt => fun s' =>
      ∃ L', s.ledger.transferFrom t caller src dst amt = some L' ∧ s' = { s with ledger := L' }
  | .approve caller t sp amt => s.TokenApprove caller t sp amt
  | .foreignBurn burner txOrigin rec => fun s' =>
      ∃ L', s.circle.Burn s.ledger burner txOrigin rec L' ∧
        s' = { s with ledger := L', burns := s.burns ++ [rec] }
  | .sendGeneric sender g => fun s' =>
      s.circle.SendGeneric sender g ∧ s' = { s with generics := s.generics ++ [g] }
  | .circle op => fun s' => s' = { s with circle := op.apply s.circle }
  | .ledger op => fun s' => s.LedgerOpAllowed op ∧ s' = { s with ledger := op.apply s.ledger }
  | .aave op => fun s' => s' = { s with yield := { s.yield with aave := op.apply s.yield.aave } }

/-- The callback frame of nesting depth at most `n` in context `ctx`. -/
def hubFrame {C : Crypto} (ctx : Ctx) : Nat → Frame
  | 0 => fun s s' => s' = s
  | n + 1 => Relation.ReflTransGen fun s s' => ∃ tx : HubTxn C, s.Exec (hubFrame (C := C) ctx n) ctx tx s'

/-- A hub transaction succeeds: it executes with callback frames of some finite depth. -/
def HubChain.Step {C : Crypto} (ctx : Ctx) (s : HubChain) (tx : HubTxn C) (s' : HubChain) : Prop :=
  ∃ n, s.Exec (hubFrame (C := C) ctx n) ctx tx s'

/-! ### Client chain transactions -/

/-- A transaction on a client chain (model sheet v2.1 §5). -/
inductive ClientTxn where
  | shield (caller txOrigin : Term) (note : ShieldData) (maxFee : Nat)
      (finality : Option RequestedFinality) (rec : BurnRecord)
  | shieldWithFee (caller txOrigin : Term) (userNote feeNote : ShieldData) (maxFee : Nat)
      (finality : Option RequestedFinality) (rec : BurnRecord)
  | signIntent (signer : Term) (i : Intent)
  | signPermit (signer : Term) (pm : Permit)
  | submitPermit (pm : Permit)
  | gaslessShield (relayer : Term) (i : Intent) (rec : BurnRecord)
  | relay (rt : Term) (att : Attestation)
  | directReceive (caller : Term) (att : Attestation)
  | handlerCall (caller : Term) (finalized : Bool) (executed : Nat) (src : Domain) (body : BurnBody)
      (feeExecuted : Nat)
  | owner (caller : Term) (op : ClientOwnerOp)
  | acceptOwnership (caller : Term)
  | transfer (caller t dst : Term) (amt : Nat)
  | transferFrom (caller t src dst : Term) (amt : Nat)
  | approve (caller t sp : Term) (amt : Nat)
  | foreignBurn (burner txOrigin : Term) (rec : BurnRecord)
  | sendGeneric (sender : Term) (g : GenericMessage)
  | circle (op : CircleOp)
  | ledger (op : LedgerOp)

/-- One client transaction's execution in context `ctx`. -/
def ClientChain.Step (ctx : Ctx) (s : ClientChain) : ClientTxn → ClientChain → Prop
  | .shield caller txOrigin note maxFee finality rec => s.Shield caller txOrigin note maxFee finality rec
  | .shieldWithFee caller txOrigin userNote feeNote maxFee finality rec =>
      s.ShieldWithFee caller txOrigin userNote feeNote maxFee finality rec
  | .signIntent signer i => s.SignIntent signer i
  | .signPermit signer pm => s.SignPermit signer pm
  | .submitPermit pm => s.SubmitPermit ctx.now pm
  | .gaslessShield relayer i rec => s.GaslessShield ctx.now relayer i rec
  | .relay rt att => s.Relay ctx.iris ctx.now rt att
  | .directReceive caller att => s.DirectReceive ctx.iris ctx.now caller att
  | .handlerCall caller finalized executed src body feeExecuted =>
      s.HandlerCall caller finalized executed src body feeExecuted
  | .owner caller op => s.OwnerStep caller op
  | .acceptOwnership caller => s.AcceptOwnership caller
  | .transfer caller t dst amt => s.TokenTransfer caller t dst amt
  | .transferFrom caller t src dst amt => fun s' =>
      ∃ L', s.ledger.transferFrom t caller src dst amt = some L' ∧ s' = { s with ledger := L' }
  | .approve caller t sp amt => s.TokenApprove caller t sp amt
  | .foreignBurn burner txOrigin rec => fun s' =>
      ∃ L', s.circle.Burn s.ledger burner txOrigin rec L' ∧
        s' = { s with ledger := L', burns := s.burns ++ [rec] }
  | .sendGeneric sender g => fun s' =>
      s.circle.SendGeneric sender g ∧ s' = { s with generics := s.generics ++ [g] }
  | .circle op => fun s' => s' = { s with circle := op.apply s.circle }
  | .ledger op => fun s' => op.Allowed s.client.usdc ∧ s' = { s with ledger := op.apply s.ledger }

/-! ### The system -/

/-- The whole system: the hub chain's log, each client domain's log (`none` for a domain with
    no client chain), the attestation service and the time. -/
structure System (C : Crypto) where
  hub : Chain HubChain (HubTxn C)
  clients : Domain → Option (Chain ClientChain ClientTxn)
  iris : Iris
  now : Nat

namespace System

variable {C : Crypto}

/-- The context transactions read. -/
def ctx (σ : System C) : Ctx := ⟨σ.iris, σ.now⟩

/-- Replace one client domain's log. -/
def setClient (σ : System C) (d : Domain) (c : Chain ClientChain ClientTxn) : System C :=
  { σ with clients := fun d' => if d' = d then some c else σ.clients d' }

/-- A burn is in its source chain's current state. -/
def BurnCanonical (σ : System C) (b : BurnRecord) : Prop :=
  σ.hub.current.circle.domain = b.source ∧ b ∈ σ.hub.current.burns ∨
  ∃ c, σ.clients b.source = some c ∧ b ∈ c.current.burns

/-- A burn is in its source chain's finalized snapshot. -/
def BurnFinalized (σ : System C) (b : BurnRecord) : Prop :=
  σ.hub.snapshot.circle.domain = b.source ∧ b ∈ σ.hub.snapshot.burns ∨
  ∃ c, σ.clients b.source = some c ∧ b ∈ c.snapshot.burns

/-- A generic message is in its source chain's current state. -/
def GenericCanonical (σ : System C) (g : GenericMessage) : Prop :=
  σ.hub.current.circle.domain = g.source ∧ g ∈ σ.hub.current.generics ∨
  ∃ c, σ.clients g.source = some c ∧ g ∈ c.current.generics

/-- A message is in its source chain's current state. -/
def MsgCanonical (σ : System C) : Message → Prop
  | .burn b => σ.BurnCanonical b
  | .generic g => σ.GenericCanonical g

/-- Circle's fast-transfer fee for a burn's token on its source chain. -/
def fastFee (σ : System C) (b : BurnRecord) : Nat :=
  if σ.hub.current.circle.domain = b.source then σ.hub.current.circle.fastFee b.body.burnToken
  else match σ.clients b.source with
    | some c => c.current.circle.fastFee b.body.burnToken
    | none => 0

/-- One step of the system (model sheet v2.1 §5): a transaction attempted on a chain, a
    finalization or a reorg of a chain, an attestation service step, or the clock. -/
inductive Step : System C → System C → Prop where
  | hubTx (σ : System C) (tx : HubTxn C) (s' : HubChain)
      (hAttempt : Attempt (HubChain.Step σ.ctx) σ.hub.current tx s') :
      Step σ { σ with hub := σ.hub.submit tx s' }
  | clientTx (σ : System C) (d : Domain) (c : Chain ClientChain ClientTxn) (tx : ClientTxn)
      (s' : ClientChain) (hClient : σ.clients d = some c)
      (hAttempt : Attempt (ClientChain.Step σ.ctx) c.current tx s') :
      Step σ (σ.setClient d (c.submit tx s'))
  | hubFinalize (σ : System C) (k : Nat) : Step σ { σ with hub := σ.hub.finalize k }
  | clientFinalize (σ : System C) (d : Domain) (c : Chain ClientChain ClientTxn) (k : Nat)
      (hClient : σ.clients d = some c) : Step σ (σ.setClient d (c.finalize k))
  | hubReorg (σ : System C) (h' : Chain HubChain (HubTxn C))
      (hReorg : σ.hub.Reorg (HubChain.Step σ.ctx) h') : Step σ { σ with hub := h' }
  | clientReorg (σ : System C) (d : Domain) (c c' : Chain ClientChain ClientTxn)
      (hClient : σ.clients d = some c) (hReorg : c.Reorg (ClientChain.Step σ.ctx) c') :
      Step σ (σ.setClient d c')
  | attestBurn (σ : System C) (b : BurnRecord) (fast : Bool) (att : Attestation) (iris' : Iris)
      (hAttest : σ.iris.AttestBurn b (σ.BurnCanonical b) (σ.BurnFinalized b) (σ.fastFee b) fast att iris') :
      Step σ { σ with iris := iris' }
  | attestGeneric (σ : System C) (g : GenericMessage) (att : Attestation) (iris' : Iris)
      (hAttest : σ.iris.AttestGeneric g (σ.GenericCanonical g) att iris') :
      Step σ { σ with iris := iris' }
  | reattest (σ : System C) (old new : Attestation) (iris' : Iris)
      (hAttest : σ.iris.Reattest old new (σ.MsgCanonical new.msg) iris') :
      Step σ { σ with iris := iris' }
  | rotate (σ : System C) : Step σ { σ with iris := σ.iris.rotate }
  | tick (σ : System C) : Step σ { σ with now := σ.now + 1 }

end System

/-- A hub chain right after deployment: a genesis pool, no events, burns or generic messages,
    no used Circle nonces, re-entrancy guards clear, a fresh vault whose share token has no
    holders, flags or Aave position, the adapter's unlimited USDC approval of the vault
    (ArmadaYieldAdapter.sol:111), wind-down not triggered, and an empty gasless wrapper. Every
    configuration field is free: the deployer's arguments are any the code accepts. -/
def HubChain.Fresh (s : HubChain) : Prop :=
  s.hub.pool = genesis s.hub.pool.feeRatio ∧ s.hub.guardOn = false ∧
  s.events = [] ∧ s.burns = [] ∧ s.generics = [] ∧ s.circle.usedNonces = [] ∧
  s.yield.vault.totalSupply = 0 ∧ s.yield.vault.totalDeposited = 0 ∧ s.yield.vault.totalPaidOut = 0 ∧
  s.yield.vault.cumulativeProtocolFee = 0 ∧ s.yield.vault.accruedProtocolFee = 0 ∧
  s.yield.vault.yieldHighWaterMark = 0 ∧ s.yield.vault.guardOn = false ∧
  s.yield.aave.vaultAssets = 0 ∧
  (∀ h, s.ledger.balance s.yield.vault.self h = 0) ∧ s.ledger.paused s.yield.vault.self = false ∧
  (∀ a, s.ledger.blacklisted s.yield.vault.self a = false) ∧
  s.yield.adapter.guardOn = false ∧
  s.ledger.allowance s.yield.adapter.usdc s.yield.adapter.self s.yield.adapter.vault = 2 ^ 256 - 1 ∧
  s.comps.windDown.triggered = false ∧
  s.gasless.signedIntents = [] ∧ s.gasless.signedPermits = [] ∧ s.gasless.usedPermits = [] ∧
  (∀ u, s.gasless.nonces u = 0)

/-- A client chain right after deployment: no burns or generic messages, no used Circle nonces,
    an empty gasless wrapper. -/
def ClientChain.Fresh (s : ClientChain) : Prop :=
  s.burns = [] ∧ s.generics = [] ∧ s.circle.usedNonces = [] ∧
  s.client.wrapper.signedIntents = [] ∧ s.client.wrapper.signedPermits = [] ∧
  s.client.wrapper.usedPermits = [] ∧ (∀ u, s.client.wrapper.nonces u = 0)

/-- An initial system: every chain freshly deployed with nothing pending, each client chain at
    its own domain, none at the hub's, and no attestation issued. -/
def System.Init {C : Crypto} (σ : System C) : Prop :=
  σ.hub.pending = [] ∧ σ.hub.snapshot.Fresh ∧ σ.iris.issued = [] ∧
  ∀ d c, σ.clients d = some c →
    c.pending = [] ∧ c.snapshot.Fresh ∧ c.snapshot.circle.domain = d ∧
    d ≠ σ.hub.snapshot.circle.domain

/-- The CCTP model's machine (`Machine`, `ArmadaLean/Machine.lean`). -/
def system (C : Crypto) : Machine (System C) where
  init := System.Init
  step := System.Step

end ArmadaLean.Cctp
