-- ABOUTME: Non-vacuity of the CCTP machine: a concrete initial system, and a run that delivers an inbound shield.
-- ABOUTME: From a fresh system a client shield is burned, finalized, attested and relayed, and the hub credits it.
/-
  ArmadaLean.Cctp.NonVacuity — the CCTP machine is not vacuous.

  Design record: model sheet v2.1 §7 (witness rules) and §15 (statement order, step 10a). A
  statement over the reachable states of `system C` would hold trivially if no initial state
  existed, or if no delivery could ever happen. This file builds one concrete initial system
  (`init0`) and one concrete run from it (`reach4`): a user's shield on the client chain, the
  client chain finalizing it, Iris attesting it STANDARD, and a relay through the hub router,
  after which the hub pool holds a live 100 USDC note backed by 100 USDC (`delivered4`). Every
  step is the machine's own step, checked by the kernel.
-/
import ArmadaLean.Cctp.System

namespace ArmadaLean.Cctp.NonVacuity

open ArmadaLean.Cctp

/-- The ideal cryptography with a signature check that accepts everything and no forgeries. The
    inbound shield verifies no proof, so the run does not depend on the choice. -/
def C : Crypto := Crypto.ideal (fun _ _ _ => True) (fun _ => False)

def usdc : Term := .val 1
def hubPool : Term := .val 10
def hubTM : Term := .val 11
def hubMT : Term := .val 12
def hubMinter : Term := .val 13
def router : Term := .val 14
def treasury : Term := .val 15
def owner : Term := .val 16
def client : Term := .val 20
def clientTM : Term := .val 21
def clientMT : Term := .val 22
def clientMinter : Term := .val 23
def user : Term := .val 30
def vault : Term := .val 40
def adapter : Term := .val 41
def spoke : Term := .val 42
def registry : Term := .val 43
def hubWrapper : Term := .val 44
def clientWrapper : Term := .val 45
def hubDom : Domain := ⟨0⟩
def clientDom : Domain := ⟨1⟩

/-- The starting ledger of both chains: the user holds 100 USDC and has approved the client for
    it; the adapter's unlimited approval of the vault is in place. -/
def L0 : Ledger where
  balance := fun t h => if t = usdc ∧ h = user then 100 else 0
  blacklisted := fun _ _ => false
  paused := fun _ => false
  allowance := fun t o sp =>
    if t = usdc ∧ o = user ∧ sp = client then 100
    else if t = usdc ∧ o = adapter ∧ sp = vault then 2 ^ 256 - 1 else 0

/-- Circle's contracts on a chain at domain `d`: unpaused, every messenger registered, every token
    linked to itself, generous limits, no minimum or fast fee. -/
def circleAt (d : Domain) (tm mt minter : Term) : CircleChain where
  domain := d
  tokenMessenger := tm
  messageTransmitter := mt
  minter := minter
  usedNonces := []
  paused := false
  denylist := fun _ => false
  remoteMessenger := fun _ => true
  linkedToken := fun _ t => some t
  minterAllowance := fun _ => 10 ^ 12
  maxShieldNotes := 10
  burnLimit := fun _ => 10 ^ 12
  minFeeRate := fun _ => 0
  fastFee := fun _ => 0
  feeRecipient := .val 99

/-- A zero shield fee. -/
def zeroFee : FeeRatio := ⟨0, 1, by decide, by decide, by decide⟩

def hub0 : HubState where
  pool := genesis zeroFee
  self := hubPool
  owner := owner
  pendingOwner := none
  tokenMessenger := hubTM
  messageTransmitter := hubMT
  usdc := usdc
  localDomain := hubDom
  treasury := treasury
  remotePools := fun _ => .clean client
  remoteHookRouters := fun _ => .clean router
  hookRouter := some router
  adapterRegistry := none
  verificationKeys := fun _ => none
  feeModule := none
  pauseController := none
  defaultFinality := none
  blocklist := fun _ => false
  guardOn := false

def comps0 : Components where
  pause := fun _ => ⟨false, false, false, false, false⟩
  feeModule := fun _ => ⟨hubPool, vault, usdc, 1000, 604800, false⟩
  registry := fun _ => ⟨fun _ => false, fun _ => false, false⟩
  windDown := ⟨0, 0, 0, 0, .val 0, false, .val 0⟩

def yield0 : YieldState where
  adapter := ⟨adapter, owner, hubPool, usdc, vault, registry, false⟩
  vault := ⟨vault, owner, none, treasury, usdc, 1000, 0, 0, 0, 0, 0, 0, 0, false⟩
  aave := ⟨spoke, 0, false, false⟩

/-- The freshly deployed hub chain: a genesis pool at the hub's address, the router registered
    and wired to Circle, no fee module, registry or pause controller. -/
def h0 : HubChain where
  hub := hub0
  circle := circleAt hubDom hubTM hubMT hubMinter
  ledger := L0
  comps := comps0
  routers := fun a => if a = router then some ⟨router, hubMT, hubTM⟩ else none
  yield := yield0
  events := []
  burns := []
  generics := []
  gasless := ⟨hubWrapper, usdc, hubPool, fun _ => 0, [], [], []⟩

def client0 : ClientState where
  self := client
  owner := owner
  pendingOwner := none
  tokenMessenger := clientTM
  messageTransmitter := clientMT
  usdc := usdc
  localDomain := clientDom
  hubDomain := hubDom
  hubPool := .clean hubPool
  hookRouter := none
  hubHookRouter := .clean router
  defaultFinality := none
  wrapper := ⟨clientWrapper, fun _ => 0, [], [], []⟩

/-- The freshly deployed client chain at domain 1, pointing at the hub pool and the hub router. -/
def c0 : ClientChain where
  client := client0
  circle := circleAt clientDom clientTM clientMT clientMinter
  ledger := L0
  routers := fun _ => none
  burns := []
  generics := []

/-- The initial system: the hub at domain 0, one client at domain 1, no attestations, time 0. -/
def σ0 : System C where
  hub := ⟨h0, []⟩
  clients := fun d => if d = clientDom then some ⟨c0, []⟩ else none
  iris := ⟨0, []⟩
  now := 0

/-- The concrete system is an initial state of the machine. -/
theorem init0 : (system C).init σ0 := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_,
      rfl, rfl, rfl, rfl, ?_⟩
    · intro h; simp [σ0, h0, L0, yield0, usdc, vault]
    · intro a; rfl
    · simp [σ0, h0, L0, yield0, usdc, adapter, vault, user, client]
    · intro u; rfl
  · intro d c h
    simp only [σ0] at h
    split at h
    · cases h; subst_vars
      refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, rfl, by decide⟩
    · cases h


/-- The user's note: 100 USDC to a canonical note key. -/
def note : ShieldData := ⟨.val 5, ⟨100, by decide⟩, .val 0, none⟩

/-- The burn the client shield creates. -/
def rec1 : BurnRecord where
  id := ⟨0⟩
  source := clientDom
  dest := hubDom
  destinationCaller := .clean router
  requested := .standard
  body := { burnToken := usdc, mintRecipient := .clean hubPool, amount := 100,
            messageSender := .clean client, maxFee := 0, hookData := .shield [note] }
  maxFee_lt := by decide

def tx1 : ClientTxn := .shield user user note 0 none rec1

def cL1 : Ledger :=
  (((L0.transferFrom usdc client user client 100).bind fun L => L.approve usdc client clientTM 100).bind
    fun L => (L.transferFrom usdc clientTM client clientMinter 100).bind fun L => L.burn usdc clientMinter 100).getD L0

def c1 : ClientChain := { c0 with ledger := cL1, burns := [rec1] }

/-- The note key is a canonical field element. -/
theorem canonical5 : Canonical (Term.val 5) := by
  intro n h; cases h; unfold p; decide

/-- The user's client shield succeeds and leaves the burn on the client chain. -/
theorem step1 : ClientChain.Step σ0.ctx c0 tx1 c1 := by
  show c0.Shield user user note 0 none rec1 c1
  refine ⟨by decide, by decide, by decide, by decide, ⟨by decide, canonical5⟩, trivial, cL1, ?_, rfl⟩
  refine ⟨rfl, _, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, Or.inl rfl, by decide, rfl,
    (by show [note].length ≤ 10; decide), _, rfl, rfl⟩


def chain1 : Chain ClientChain ClientTxn := (⟨c0, []⟩ : Chain ClientChain ClientTxn).submit tx1 c1

def σ1 : System C := σ0.setClient clientDom chain1

def σ2 : System C := σ1.setClient clientDom (chain1.finalize 1)

/-- Iris's STANDARD attestation of the burn: nonce 0, no fee, executed finality 2000. -/
def att : Attestation where
  msg := .burn rec1
  nonce := 0
  feeExecuted := 0
  executed := 2000
  expiry := none
  epoch := 0
  feeOK := by intro b h; cases h; exact ⟨Or.inl rfl, Nat.zero_le _⟩

def σ3 : System C := { σ2 with iris := ⟨0, [att]⟩ }

def leg0 : FeeLeg := ⟨0, 0, 0, none⟩

def tx4 : HubTxn C := .relay router att [leg0]

def hubCC0 : CircleChain := circleAt hubDom hubTM hubMT hubMinter

def hubCC1 : CircleChain :=
  { hubCC0.useNonce 0 with
    minterAllowance := fun t => if t = usdc then hubCC0.minterAllowance t - 100 else hubCC0.minterAllowance t }

def hubL1 : Ledger := (L0.mint usdc hubMinter hubPool 100).getD L0

def hs1 : HubChain := { h0 with circle := hubCC1, ledger := hubL1 }

def pres1 : List CommitmentPreimage := creditedPreimages usdc [note] (inboundValues 100 [note]) [leg0]

/-- The hub chain after the relay: the USDC minted to the pool and the note credited. -/
def h1 : HubChain :=
  { hs1 with hub := { hs1.hub with pool := creditBatch hs1.hub.pool pres1 },
             events := hs1.events ++ [batchEvent hs1.hub.pool pres1] }

/-- The relay through the hub router succeeds: Circle mints to the pool and the shield handler
    credits the note. -/
theorem hubStep : HubChain.Step σ3.ctx h0 tx4 h1 := by
  refine ⟨0, ?_⟩
  show h0.Relay (hubFrame (C := C) σ3.ctx 0) σ3.ctx.iris σ3.ctx.now router att [leg0] h1
  refine ⟨⟨router, hubMT, hubTM⟩, rfl, rfl, rfl, ?_, hubCC1, hubL1, ?_, rec1.body, rfl, ?_⟩
  · intro g h; cases h
  · refine ⟨⟨List.mem_singleton.mpr rfl, rfl, rfl, Or.inr rfl, by simp [h0, circleAt], rfl⟩, ?_⟩
    exact ⟨Or.inl rfl, rfl, usdc, rfl, by decide, hubL1, rfl, Or.inl ⟨rfl, rfl⟩, rfl⟩
  · show hs1.HandleShield _ router _ _ _ _ _ _ h1
    have hFee : hs1.InboundFee (hubFrame (C := C) σ3.ctx 0) router none 100 leg0 hs1 :=
      ⟨false, rfl, ⟨rfl, rfl, rfl⟩, hubL1, rfl, Or.inr ⟨Or.inl rfl, rfl⟩⟩
    refine ⟨Or.inr rfl, by decide, [note], rfl, by decide, rfl, ⟨_, rfl, rfl⟩, by decide, by decide,
      by decide, ?_, by decide, rfl, rfl, hs1, InboundRun.cons hFee (InboundRun.nil hs1), rfl⟩
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact canonical5

/-- The system after the relay. -/
def σ4 : System C := { σ3 with hub := σ3.hub.submit tx4 h1 }

/-- The system after the relay is reachable: shield, finalize, attest, relay. -/
theorem reach4 : (system C).Reachable σ4 := by
  refine ⟨σ0, init0, ?_⟩
  have s01 : System.Step σ0 σ1 := System.Step.clientTx σ0 clientDom ⟨c0, []⟩ tx1 c1 rfl (Or.inl step1)
  have s12 : System.Step σ1 σ2 := System.Step.clientFinalize σ1 clientDom chain1 1 rfl
  have s23 : System.Step σ2 σ3 := by
    refine System.Step.attestBurn σ2 rec1 false att ⟨0, [att]⟩ ⟨rfl, rfl, ?_, by decide, by decide,
      ⟨Or.inr ⟨chain1.finalize 1, rfl, List.mem_singleton.mpr rfl⟩, by decide⟩, rfl⟩
    intro a ha
    simp [σ2, σ1, σ0, System.setClient] at ha
  have s34 : System.Step σ3 σ4 := System.Step.hubTx σ3 tx4 h1 (Or.inl hubStep)
  exact ((((Relation.ReflTransGen.refl).tail s01).tail s12).tail s23).tail s34

/-- After the relay the hub pool holds the note: custody 100, real USDC balance 100, a live
    note. -/
theorem delivered4 :
    σ4.hub.current.hub.pool.held ⟨usdc⟩ = 100 ∧ σ4.hub.current.ledger.balance usdc hubPool = 100 ∧
      σ4.hub.current.hub.pool.live ⟨usdc⟩ ≠ [] := by
  simp only [σ4, Chain.current_submit]
  decide

/-- The machine has an initial state. -/
theorem system_has_init : ∃ σ : System C, (system C).init σ := ⟨σ0, init0⟩

/-- An inbound shield can be delivered: some reachable state's hub pool holds a live note
    backed by real USDC. -/
theorem inbound_shield_can_be_delivered :
    ∃ σ : System C, (system C).Reachable σ ∧ σ.hub.current.hub.pool.held ⟨usdc⟩ = 100 ∧
      σ.hub.current.ledger.balance usdc hubPool = 100 ∧ σ.hub.current.hub.pool.live ⟨usdc⟩ ≠ [] :=
  ⟨σ4, reach4, delivered4⟩

end ArmadaLean.Cctp.NonVacuity
