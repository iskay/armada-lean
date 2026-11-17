-- ABOUTME: A chain's canonical log: a finalized snapshot plus pending attempted transactions, each with its result.
-- ABOUTME: Finalization moves a prefix into the snapshot; a reorg re-executes a reordered subset of the pending ones.
/-
  ArmadaLean.Cctp.Chain — the canonical log of one chain, and reorgs.

  Design record: model sheet v2.1 §4.1 (decision T-10 a, Butters 2026-11-13; reorg design
  from the re-check, `.context/recheck/triage.md` T4). A chain keeps the state at the end
  of its finalized prefix (the snapshot) and the transactions submitted since (the pending
  suffix), each with the state right after it. Every submitted transaction is recorded,
  including one that reverted: a reorg may re-execute the pending transactions in a
  different order, and a transaction that reverted in one order may succeed in another.

  `Chain S Tx` is generic in the state type `S` and the transaction type `Tx`, so the hub and
  each client reuse it. Execution is a relation `R : S → Tx → S → Prop`, not a function: a
  transaction that calls into untrusted code has as many outcomes as the callee has
  behaviours (model sheet v2.1 §5.0). An attempt succeeds in any way `R` allows, or reverts
  and leaves the state unchanged; a callee may revert a transaction that could otherwise
  succeed. Recording each transaction's result keeps the finalized snapshot the state the
  chain was actually in. The CCTP model instantiates it in `ArmadaLean.Cctp.System`.
-/
import Mathlib.Data.List.Basic

namespace ArmadaLean.Cctp

/-- One attempted transaction: it succeeds as `R` allows, or it reverts and leaves the state
    unchanged. -/
def Attempt {S Tx : Type} (R : S → Tx → S → Prop) (s : S) (tx : Tx) (s' : S) : Prop :=
  R s tx s' ∨ s' = s

/-- A pending suffix follows from a starting state: each transaction's recorded state is an
    attempt of that transaction on the state before it. -/
inductive Trace {S Tx : Type} (R : S → Tx → S → Prop) : S → List (Tx × S) → Prop where
  | nil (s : S) : Trace R s []
  | cons {s s₁ : S} {tx : Tx} {rest : List (Tx × S)}
      (hTx : Attempt R s tx s₁) (hRest : Trace R s₁ rest) : Trace R s ((tx, s₁) :: rest)

/-- The canonical log of one chain: the state at the end of the finalized prefix, and the
    transactions submitted since, in order, each with the state right after it (model sheet
    v2.1 §4.1). -/
structure Chain (S Tx : Type) where
  snapshot : S
  pending : List (Tx × S)

namespace Chain

variable {S Tx : Type}

/-- The current state of a chain: the state after the last pending transaction, or the
    snapshot when none is pending. -/
def current (c : Chain S Tx) : S :=
  (c.pending.getLast?.map Prod.snd).getD c.snapshot

/-- The pending transactions, without their results. -/
def txs (c : Chain S Tx) : List Tx :=
  c.pending.map Prod.fst

/-- Submit one more transaction with the state it leaves: it joins the end of the pending
    suffix. The machine requires that state to be an attempt on the current state. -/
def submit (c : Chain S Tx) (tx : Tx) (s' : S) : Chain S Tx :=
  { c with pending := c.pending ++ [(tx, s')] }

/-- Finalize the first `k` pending transactions: the state after the last of them becomes
    the snapshot. -/
def finalize (c : Chain S Tx) (k : Nat) : Chain S Tx :=
  { snapshot := ((c.pending.take k).getLast?.map Prod.snd).getD c.snapshot,
    pending := c.pending.drop k }

/-- A reorg of a chain: the snapshot stays, and the new pending suffix is a reordering of a
    sub-list of the old transactions (no transaction is invented, none is inserted before a
    kept one; registered as assumption T-10b in model sheet v2.1 §9), re-executed from the
    snapshot. -/
def Reorg (R : S → Tx → S → Prop) (c c' : Chain S Tx) : Prop :=
  c'.snapshot = c.snapshot ∧ (∃ kept : List Tx, kept.Sublist c.txs ∧ c'.txs.Perm kept) ∧
    Trace R c'.snapshot c'.pending

/-- A submitted transaction's state is the current state. -/
@[simp] theorem current_submit (c : Chain S Tx) (tx : Tx) (s' : S) :
    (c.submit tx s').current = s' := by
  simp [current, submit]

/-- Finalization does not change the current state. -/
theorem current_finalize (c : Chain S Tx) (k : Nat) : (c.finalize k).current = c.current := by
  unfold current finalize
  conv_rhs => rw [← List.take_append_drop k c.pending]
  rw [List.getLast?_append]
  rcases h : (c.pending.drop k).getLast? with _ | x <;> simp

end Chain

end ArmadaLean.Cctp
