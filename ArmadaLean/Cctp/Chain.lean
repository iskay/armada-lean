-- ABOUTME: A chain's canonical log: a finalized snapshot plus pending attempted transactions, replayed in order.
-- ABOUTME: Finalization moves a prefix into the snapshot; a reorg re-executes a reordered subset of the pending ones.
/-
  ArmadaLean.Cctp.Chain — the canonical log of one chain, and reorgs.

  Design record: model sheet v2.1 §4.1 (decision T-10 a, Butters 2026-11-13; reorg design
  from the re-check, `.context/recheck/triage.md` T4). A chain keeps the state at the end
  of its finalized prefix (the snapshot) and the list of transactions submitted since
  (the pending suffix). Every submitted transaction is recorded, including one that
  reverted: a reorg may re-execute the pending transactions in a different order, and a
  transaction that reverted in one order may succeed in another. The current state is the
  replay of the pending transactions over the snapshot, where a reverting transaction
  leaves the state unchanged.

  `Chain S Tx` is generic in the state type `S`, the transaction type `Tx` and the
  execution function `exec : S → Tx → Option S` (`none` is a revert), so the hub and each
  client reuse it. The CCTP model instantiates it once its state and steps exist
  (`ArmadaLean.Cctp.System`).
-/
import Mathlib.Data.List.Basic

namespace ArmadaLean.Cctp

/-- Execute one attempted transaction: its new state if it succeeds, the old state if it
    reverts. -/
def attempt {S Tx : Type} (exec : S → Tx → Option S) (s : S) (tx : Tx) : S :=
  (exec s tx).getD s

/-- Replay attempted transactions in order over a starting state. -/
def replay {S Tx : Type} (exec : S → Tx → Option S) (s : S) (txs : List Tx) : S :=
  txs.foldl (attempt exec) s

@[simp] theorem replay_nil {S Tx : Type} (exec : S → Tx → Option S) (s : S) :
    replay exec s [] = s := rfl

theorem replay_append {S Tx : Type} (exec : S → Tx → Option S) (s : S) (a b : List Tx) :
    replay exec s (a ++ b) = replay exec (replay exec s a) b := by
  simp only [replay, List.foldl_append]

/-- The canonical log of one chain: the state at the end of the finalized prefix, and the
    transactions submitted since, in order (model sheet v2.1 §4.1). -/
structure Chain (S Tx : Type) where
  snapshot : S
  pending : List Tx

namespace Chain

variable {S Tx : Type}

/-- The current state of a chain: the pending transactions replayed over the snapshot. -/
def current (exec : S → Tx → Option S) (c : Chain S Tx) : S :=
  replay exec c.snapshot c.pending

/-- Submit one more transaction: it joins the end of the pending suffix. -/
def submit (c : Chain S Tx) (tx : Tx) : Chain S Tx :=
  { c with pending := c.pending ++ [tx] }

/-- Finalize the first `k` pending transactions: their replay becomes the snapshot. -/
def finalize (exec : S → Tx → Option S) (c : Chain S Tx) (k : Nat) : Chain S Tx :=
  { snapshot := replay exec c.snapshot (c.pending.take k), pending := c.pending.drop k }

/-- A reorg of a chain: the snapshot stays, and the new pending suffix is a reordering of a
    sub-list of the old one (no transaction is invented, none is inserted before a kept
    one; registered as assumption T-10b in model sheet v2.1 §9). -/
def Reorg (c c' : Chain S Tx) : Prop :=
  c'.snapshot = c.snapshot ∧ ∃ kept : List Tx, kept.Sublist c.pending ∧ c'.pending.Perm kept

/-- Submitting a transaction attempts it on the current state. -/
theorem current_submit (exec : S → Tx → Option S) (c : Chain S Tx) (tx : Tx) :
    (c.submit tx).current exec = attempt exec (c.current exec) tx := by
  simp only [current, submit]
  rw [replay_append]
  rfl

/-- Finalization does not change the current state. -/
theorem current_finalize (exec : S → Tx → Option S) (c : Chain S Tx) (k : Nat) :
    (c.finalize exec k).current exec = c.current exec := by
  simp only [current, finalize, ← replay_append, List.take_append_drop]

/-- Every chain is a reorg of itself. -/
theorem reorg_refl (c : Chain S Tx) : Reorg c c :=
  ⟨rfl, c.pending, List.Sublist.refl _, List.Perm.refl _⟩

end Chain

end ArmadaLean.Cctp
