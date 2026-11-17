-- ABOUTME: The hub's two transact steps: the batched local transact (transfers and unshields) and the atomic unshield.
-- ABOUTME: Each uses exactly the contract's checks; ghost note bookkeeping is decoded from what the transaction reveals.
/-
  ArmadaLean.Cctp.HubTransact — the hub steps that spend notes.

  Design record: model sheet v2.1 §5.1 (`atomicUnshield`, guards AU1-AU15) and §5.3
  (`localTransactBatch`, guards LT0-LT11). Both are relations between hub-chain states.

  The steps use exactly the contract's checks (TransactModule.sol:43-98,116-277,293-411):
  the proof is checked by `Crypto.verify` under whatever key the slot for the
  transaction's shape holds, so a transaction accepted under a degenerate or trapdoor key
  is a step, with no witness. The pool model's ghost bookkeeping is updated from what the
  transaction reveals:
  - a live note leaves `PoolState.live` when the transaction publishes its nullifier
    (`SpentBy`); the refinement lemma `cctp_inputs_live` (stage A) shows that under proof
    soundness and ceremony keys these are exactly the notes the proof spends;
  - each new commitment is decoded to the preimage it hashes (`decoded`, a ghost argument
    constrained by `Decodes`); a commitment that is no preimage's hash is a garbage leaf,
    with a position and no live note.
  Value conservation is therefore a theorem about the model under `Crypto.Sound` and
  ceremony keys (stage C), not an assumption of the step; with a degenerate key the model
  shows the insolvency.

  The local transact marks every nullifier first, then pays the unshields one by one, then
  reads the insertion position and inserts (TransactModule.sol:63-94). A payout in a token
  other than USDC and the vault's shares is a call into untrusted code and opens a callback
  frame (model sheet v2.1 §5.0); the atomic unshield moves only USDC and calls only Circle.

  Departure (model sheet v2.1 §10, X-22): the local payout goes to the unshield note key itself; the contract truncates it to 160 bits (TransactModule.sol:424).
  Both of the contract's pool guards stay consistent with that choice (the local guard
  compares the truncated address, the atomic guard the whole word), so no theorem depends on
  the truncation.
-/
import ArmadaLean.Cctp.HubChain

namespace ArmadaLean.Cctp

open Classical

/-- The unshield type bound into a transaction (`UnshieldType`, PoolTypes.sol). -/
inductive UnshieldKind where
  | none
  | normal
  | redirect
  deriving DecidableEq

/-- The unshield note a transaction carries in calldata (`unshieldPreimage`): its note key
    (the recipient, encoded), token and value. -/
structure UnshieldNote where
  npk : Term
  token : Term
  value : Nat
  deriving DecidableEq

/-- A transaction as the hub contract receives it (`Transaction`, PoolTypes.sol), at the level
    this model needs: the circuit shape and public record, the bound parameters, the unshield
    type and note, the result of the context checks the model does not detail (gas price, chain
    id, ciphertext length: TransactModule.sol:297-312,320-366), and the proof. -/
structure HubTx (C : Crypto) where
  shape : Shape
  pub : TransactPublic shape.nullifiers shape.commitments
  bp : BoundParams
  kind : UnshieldKind
  note : UnshieldNote
  contextOK : Bool
  proof : C.Proof

/-- The note key a transaction's unshield commitment hashes: the caller for REDIRECT
    (TransactModule.sol:346-352), the calldata note key otherwise. -/
def HubTx.hashedNpk {C : Crypto} (tx : HubTx C) (caller : Term) : Term :=
  if tx.kind = .redirect then caller else tx.note.npk

/-- The new commitments a transaction leaves in the pool: all of them, except the last one
    when the transaction unshields (TransactModule.sol:404-408). -/
def HubTx.newCommitments {C : Crypto} (tx : HubTx C) : List Term :=
  let cs := List.ofFn tx.pub.commitmentsOut
  if tx.kind = .none then cs else cs.dropLast

/-- The contract's per-transaction checks (`_validateTransaction`, TransactModule.sol:293-374),
    on pool state `ps`, by `caller`, against key registry `keys`. -/
def HubTx.Valid {C : Crypto} (tx : HubTx C) (ps : PoolState) (keys : Shape → Option VKey)
    (caller : Term) : Prop :=
  tx.contextOK = true ∧                                                         -- LT4
  AdaptAllows tx.bp caller ∧                                                    -- LT6
  tx.pub.merkleRoot ∈ ps.rootsAt' tx.bp.treeNumber ∧                            -- LT5
  tx.pub.boundParamsHash = hashBoundParams tx.bp ∧
  (if tx.kind = .none then tx.bp.unshield = none
   else 0 < tx.shape.commitments ∧ Canonical tx.note.npk ∧ 0 < tx.note.value ∧   -- LT7
     tx.bp.unshield = some ⟨tx.hashedNpk caller, tx.note.value⟩ ∧
     (List.ofFn tx.pub.commitmentsOut).getLast? =
       some (commitment (tx.hashedNpk caller) ⟨tx.note.token⟩ tx.note.value)) ∧
  ∃ k, keys tx.shape = some k ∧ C.verify k (PublicInputs.ofTransact tx.pub) tx.proof  -- LT8

/-- A user note's key: its note key derives from some master public key whose nullifying key
    is `nk` (Transact.circom:61-84). -/
def UserKey (pre : CommitmentPreimage) (nk : Nat) : Prop :=
  ∃ (pk : Nat × Nat) (r : Nat), pre.npk = npk (masterPublicKey pk nk) r

/-- A live entry is spent by a transaction on tree `tn` that publishes nullifiers `nulls`: it
    sits in that tree and its own nullifier is among them (Transact.circom:97-101). -/
def SpentBy (tn : Nat) (nulls : List Term) (e : (Nat × Nat) × CommitmentPreimage) : Prop :=
  e.1.1 = tn ∧ ∃ nk, UserKey e.2 nk ∧ nullifier (Term.val nk) e.1.2 ∈ nulls

/-- Mark one transaction's nullifiers spent on its tree, and drop from the ghost live set every
    entry it spends (`_accumulateAndNullify`, TransactModule.sol:385-411). `none` when a
    nullifier is already spent or repeats. -/
noncomputable def nullifyTx {C : Crypto} (ps : PoolState) (tx : HubTx C) : Option PoolState :=
  let nulls := List.ofFn tx.pub.nullifiers
  (markSpent (ps.spent tx.bp.treeNumber) nulls).map fun spent' =>
    { ps with
        spent := fun n => if n = tx.bp.treeNumber then spent' else ps.spent n,
        live := fun t => (ps.live t).filter fun e => ¬ SpentBy tx.bp.treeNumber nulls e }

/-- Validate and nullify a batch's transactions in order: each is validated on the state the
    previous ones left (TransactModule.sol:63-75). `ps'` is the pool after the last. -/
inductive ValidateRun {C : Crypto} (keys : Shape → Option VKey) (caller : Term) :
    PoolState → List (HubTx C) → PoolState → Prop where
  | nil (ps : PoolState) : ValidateRun keys caller ps [] ps
  | cons {ps ps₁ ps' : PoolState} {tx : HubTx C} {txs : List (HubTx C)}
      (hValid : tx.Valid ps keys caller) (hNull : nullifyTx ps tx = some ps₁)
      (hRest : ValidateRun keys caller ps₁ txs ps') :
      ValidateRun keys caller ps (tx :: txs) ps'

/-- A ghost decoding of new commitments: `some pre` exactly when the commitment is `pre`'s hash,
    `none` when it is no preimage's hash (a garbage leaf). -/
def Decodes (cs : List Term) (decoded : List (Option CommitmentPreimage)) : Prop :=
  decoded.length = cs.length ∧
  ∀ x ∈ cs.zip decoded, match x.2 with
    | some pre => hashCommitment pre = x.1
    | none => ∀ pre, hashCommitment pre ≠ x.1

/-- Insert a batch of leaves (the contract's one `insertLeaves` call, TransactModule.sol:84-94)
    and credit the decoded ones to the ghost live set and custody. No root is pushed for an
    empty batch (effect LTe1: the contract skips the call). -/
noncomputable def creditLeaves (ps : PoolState) (leaves : List Term)
    (decoded : List (Option CommitmentPreimage)) : PoolState :=
  if leaves = [] then ps
  else
    let tn := insertTree ps.trees leaves.length
    let pos := insertStart ps.trees leaves.length
    let placed := (withTreePositionsFrom tn pos decoded).filterMap fun e => e.2.map fun pre => (e.1, pre)
    let pres := decoded.filterMap id
    { ps with
        live := fun t => placed.filter (fun e => e.2.token = t) ++ ps.live t,
        held := fun t => ps.held t + ((pres.filter (fun pre => pre.token = t)).map (·.value)).sum,
        trees := insertLeaves ps.trees leaves }

/-- Pay one local unshield (`_transferTokenOut`, TransactModule.sol:418-436): never to the pool
    (LT10), an ERC-20 transfer from the pool to the unshield note key (LT10b, LT11); ghost
    custody falls by the payout. -/
def HubChain.PayOut {C : Crypto} (s : HubChain) (F : Frame) (tx : HubTx C) (s' : HubChain) : Prop :=
  tx.note.npk ≠ s.hub.self ∧                                                   -- LT10
  ∃ s₁, s.TokenCall F tx.note.token                                             -- LT10b, LT11
    (fun L => L.transfer tx.note.token s.hub.self tx.note.npk tx.note.value) s₁ ∧
  let ps := s₁.hub.pool
  s' = { s₁ with hub := { s₁.hub with pool := { ps with
          held := fun t => if t = ⟨tx.note.token⟩ then ps.held t - tx.note.value else ps.held t,
          payouts := ps.payouts ++ [⟨⟨tx.note.token⟩, tx.note.npk, tx.note.value⟩] } } }

/-- Pay a batch's local unshields in order (TransactModule.sol:77-82); a transaction without an
    unshield pays nothing. -/
inductive PayRun {C : Crypto} (F : Frame) : HubChain → List (HubTx C) → HubChain → Prop where
  | nil (s : HubChain) : PayRun F s [] s
  | skip {s s' : HubChain} {tx : HubTx C} {txs : List (HubTx C)}
      (hNone : tx.kind = .none) (hRest : PayRun F s txs s') : PayRun F s (tx :: txs) s'
  | pay {s s₁ s' : HubChain} {tx : HubTx C} {txs : List (HubTx C)}
      (hKind : tx.kind ≠ .none) (hPay : s.PayOut F tx s₁) (hRest : PayRun F s₁ txs s') :
      PayRun F s (tx :: txs) s'

/-- A batched local transact by `caller` (`PrivacyPool.transact` → `TransactModule.transact`,
    PrivacyPool.sol:146-148; TransactModule.sol:43-98). `decoded` is the ghost decoding of the
    batch's new commitments. The re-entrancy guard is held from the nullifiers to the
    insertion. -/
def HubChain.LocalTransactBatch {C : Crypto} (s : HubChain) (F : Frame) (caller : Term)
    (txs : List (HubTx C)) (decoded : List (Option CommitmentPreimage)) (s' : HubChain) : Prop :=
  txs ≠ [] ∧                                                                   -- LT0
  s.hub.guardOn = false ∧                                                      -- LT1
  (∃ pc, s.pauseView = some pc ∧ pc.emergencyPaused = false ∧                   -- LT2
    (pc.withdrawOnly = true → ∀ tx ∈ txs, tx.kind ≠ .none)) ∧                    -- LT3
  ∃ ps₁, ValidateRun s.hub.verificationKeys caller s.hub.pool txs ps₁ ∧          -- LT4-LT9
  ∃ s₂, PayRun F { s with hub := { s.hub with guardOn := true, pool := ps₁ } } txs s₂ ∧  -- LT10, LT11
  let leaves := (txs.map HubTx.newCommitments).flatten
  let ps₂ := s₂.hub.pool
  Decodes leaves decoded ∧
  s' = { s₂ with
          hub := { s₂.hub with guardOn := false, pool := creditLeaves ps₂ leaves decoded },
          events := if leaves = [] then s₂.events
            else s₂.events ++ [⟨insertTree ps₂.trees leaves.length, insertStart ps₂.trees leaves.length, leaves⟩] }

/-- The tag Armada's binding hashes first (`keccak256("ArmadaCCTPUnshield.v1")`,
    CCTPBindingLib.sol:24), as a fixed term. -/
def cctpBindingTag : Term := Term.val 0x41726d616461434354505631

/-- The cross-chain unshield binding (`CCTPBindingLib.encode`, CCTPBindingLib.sol:33-39):
    the symbolic Keccak hash of the tag, the recipient, the destination domain and `maxFee`. -/
def cctpBinding (recipient : Term) (d : Domain) (maxFee : Nat) : Term :=
  Term.keccak [cctpBindingTag, recipient, Term.val d.id, Term.val maxFee]

/-- The atomic cross-chain unshield by `caller` with transaction origin `txOrigin`
    (`PrivacyPool.atomicCrossChainUnshield` → `TransactModule.atomicCrossChainUnshield`,
    PrivacyPool.sol:163-178; TransactModule.sol:116-277). `rec` is the burn it creates;
    `decoded` the ghost decoding of its change notes. Withdraw-only mode is not checked,
    as in the code (finding CB-8). The outbound burn is modelled for a genuine TokenMessenger
    (the hub's stored address is Circle's); a miswired one is covered by the wiring hypothesis
    of the solvency statement (model sheet v2.1 §9, A-wiring). -/
def HubChain.AtomicUnshield {C : Crypto} (s : HubChain) (caller txOrigin : Term) (tx : HubTx C)
    (d : Domain) (finalRecipient : Term) (maxFee : Nat) (uniqueNonce : Term) (rec : BurnRecord)
    (decoded : List (Option CommitmentPreimage)) (s' : HubChain) : Prop :=
  s.hub.guardOn = false ∧                                                      -- AU1
  (∃ pc, s.pauseView = some pc ∧ pc.emergencyPaused = false) ∧                  -- AU2
  d ≠ s.hub.localDomain ∧                                                      -- AU3
  finalRecipient ≠ Term.val 0 ∧                                                -- AU4
  tx.kind ≠ .none ∧                                                            -- AU5
  tx.note.token = s.hub.usdc ∧                                                 -- AU6
  s.hub.remotePools d ≠ Bytes32.zero ∧                                         -- AU7
  s.hub.remoteHookRouters d ≠ Bytes32.zero ∧                                   -- AU8
  tx.bp.adaptContract = none ∧                                                 -- AU9
  tx.bp.adaptParams = cctpBinding finalRecipient d maxFee ∧                    -- AU10
  tx.note.npk = s.hub.self ∧                                                   -- AU11 (whole word)
  tx.Valid s.hub.pool s.hub.verificationKeys caller ∧                          -- AU12
  maxFee < tx.note.value ∧                                                     -- AU13
  ∃ ps₁, nullifyTx s.hub.pool tx = some ps₁ ∧                                  -- AU14
  s.hub.tokenMessenger = s.circle.tokenMessenger ∧
  ∃ L₁, s.ledger.approve s.hub.usdc s.hub.self s.hub.tokenMessenger tx.note.value = some L₁ ∧  -- AU15
  rec.source = s.circle.domain ∧ rec.dest = d ∧
  rec.destinationCaller = s.hub.remoteHookRouters d ∧
  rec.requested = s.hub.defaultFinality.getD .standard ∧
  rec.body = { burnToken := s.hub.usdc, mintRecipient := s.hub.remotePools d,
               amount := tx.note.value, messageSender := .clean s.hub.self, maxFee := maxFee,
               hookData := .unshield ⟨finalRecipient, uniqueNonce⟩ } ∧
  ∃ L₂, s.circle.Burn L₁ s.hub.self txOrigin rec L₂ ∧
  let leaves := tx.newCommitments
  Decodes leaves decoded ∧
  let ps₂ := creditLeaves ps₁ leaves decoded
  s' = { s with
          ledger := L₂,
          burns := s.burns ++ [rec],
          hub := { s.hub with pool := { ps₂ with
            held := fun t => if t = ⟨s.hub.usdc⟩ then ps₂.held t - tx.note.value else ps₂.held t } },
          events := if leaves = [] then s.events
            else s.events ++ [⟨insertTree ps₁.trees leaves.length, insertStart ps₁.trees leaves.length, leaves⟩] }

end ArmadaLean.Cctp
