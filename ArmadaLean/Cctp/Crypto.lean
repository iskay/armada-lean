-- ABOUTME: The CCTP model's cryptography as parameters: a signature check and a proof verifier, with four key cases.
-- ABOUTME: Soundness and completeness are named hypotheses; an ideal instance with no axioms serves the witnesses.
/-
  ArmadaLean.Cctp.Crypto — cryptographic primitives as parameters, not axioms.

  Design record: model sheet v2.1 §3.2 (decision RD-1, Butters 2026-11-13). The pool model
  of PR #1 declares the signature check `EdDSAVerify` and the proof verifier
  `VerifyAccepts` as axioms. A statement whose hypotheses need an accepted proof then has
  no buildable witness, and a verifier that accepts nothing satisfies a soundness
  hypothesis vacuously. Here both primitives are fields of a structure `Crypto`, every
  CCTP statement is stated for any `Crypto` that satisfies the named hypotheses it needs,
  and witnesses use the axiom-free instance `Crypto.ideal`.

  The pool stores one verification key per circuit shape (`verificationKeys[N][M]`,
  PrivacyPool.sol:514) and the owner may write any key into any slot
  (`setVerificationKey`, VerifierModule.sol:31-41, "No structural validation is performed
  on the key"). `VKey` has four cases. Model sheet v2.1 names five; two of them are one
  constructor here, distinguished by comparing the key's shape with the slot's:
  - `ceremony s` stored in the slot of shape `s`: the good key;
  - `ceremony s'` stored in the slot of a shape `s ≠ s'`: a genuine key in the wrong slot
    (code finding DEBIT-01 of the solvency red team);
  - `degenerate`: `gamma2 = delta2`, which accepts every input (finding TRUST-02);
  - `trapdoor s`: a well-formed key of shape `s` whose toxic waste someone knows;
  - `zero`: an all-zero key, which accepts nothing.
-/
import ArmadaLean.Cctp.Types

namespace ArmadaLean.Cctp

/-- The type of a signature check over a Transact message hash, the parameter of
    `TransactCore` (ArmadaLean.Transact): public key, signature, message. -/
abbrev SigCheck := (Nat × Nat) → (Nat × Nat × Nat) → Term → Prop

/-- A verification key held in one slot of the pool's registry (PrivacyPool.sol:514;
    VerifierModule.sol:31-41). -/
inductive VKey where
  /-- The finalized ceremony key of circuit shape `s`. -/
  | ceremony (s : Shape)
  /-- A key with `gamma2 = delta2`: the Groth16 equation then holds for any public inputs
      (SnarkTypes.sol:19-52). An uncontributed `0000.zkey` exports one. -/
  | degenerate
  /-- A well-formed key of shape `s` whose toxic waste is known to someone. -/
  | trapdoor (s : Shape)
  /-- An all-zero key: no proof verifies against it. -/
  | zero
  deriving DecidableEq

/-- The cryptographic primitives of the model.
    * `sigOK`: the signature check inside the circuit (Transact.circom:163-186).
    * `Proof`: the type of proof objects.
    * `verifyCeremony s inputs π`: the on-chain Groth16 check of proof `π` against the
      ceremony key of shape `s`, on the flat public-input list `inputs`
      (PrivacyPool.sol:513-545).
    * `forged inputs`: the public inputs for which the holder of a trapdoor can make a
      proof that the trapdoor key accepts. -/
structure Crypto where
  sigOK : SigCheck
  Proof : Type
  verifyCeremony : Shape → PublicInputs → Proof → Prop
  forged : PublicInputs → Prop

/-- What the pool's `verify` accepts when the slot holds key `k` (PrivacyPool.sol:513-545).
    The contract reads the same flat input list whatever key the slot holds, so a
    ceremony key of another shape checks that list against its own circuit. -/
def Crypto.verify (C : Crypto) : VKey → PublicInputs → C.Proof → Prop
  | .ceremony s, inputs, π => C.verifyCeremony s inputs π
  | .degenerate, _, _ => True
  | .trapdoor s, inputs, π => C.verifyCeremony s inputs π ∨ C.forged inputs
  | .zero, _, _ => False

/-- Proof soundness for ceremony keys: a proof accepted against the ceremony key of shape
    `s` comes from a witness that satisfies the circuit's core constraints
    (`TransactCore`, ArmadaLean.Transact) for some public record whose flat layout is the
    accepted input list. Only ceremony keys are covered; the other cases are definitions
    (`Crypto.verify`). -/
def Crypto.Sound (C : Crypto) : Prop :=
  ∀ (s : Shape) (inputs : PublicInputs) (π : C.Proof),
    C.verifyCeremony s inputs π →
      ∃ (pub : TransactPublic s.nullifiers s.commitments)
        (w : TransactWitness s.nullifiers s.commitments),
        PublicInputs.ofTransact pub = inputs ∧ TransactCore C.sigOK w pub

/-- Proof completeness for ceremony keys: an honest prover who holds a witness that
    satisfies the circuit's core constraints gets a proof that the ceremony key of the
    witness's shape accepts. -/
def Crypto.Complete (C : Crypto) : Prop :=
  ∀ (s : Shape) (pub : TransactPublic s.nullifiers s.commitments)
    (w : TransactWitness s.nullifiers s.commitments),
    TransactCore C.sigOK w pub → ∃ π : C.Proof, C.verifyCeremony s (PublicInputs.ofTransact pub) π

/-- The ideal cryptography that witnesses use, with no axiom. The signature check is the
    given `sig`; a ceremony key accepts exactly the input lists that some witness of its
    shape satisfies; proofs carry no data; the trapdoor holder can forge the inputs `forge`. -/
def Crypto.ideal (sig : SigCheck) (forge : PublicInputs → Prop) : Crypto where
  sigOK := sig
  Proof := Unit
  verifyCeremony := fun s inputs _ =>
    ∃ (pub : TransactPublic s.nullifiers s.commitments)
      (w : TransactWitness s.nullifiers s.commitments),
      PublicInputs.ofTransact pub = inputs ∧ TransactCore sig w pub
  forged := forge

/-- The ideal cryptography is sound. -/
theorem Crypto.ideal_sound (sig : SigCheck) (forge : PublicInputs → Prop) :
    (Crypto.ideal sig forge).Sound := by
  intro _ _ _ h
  exact h

/-- The ideal cryptography is complete. -/
theorem Crypto.ideal_complete (sig : SigCheck) (forge : PublicInputs → Prop) :
    (Crypto.ideal sig forge).Complete := by
  intro _ pub w hw
  exact ⟨(), pub, w, rfl, hw⟩

/-- A degenerate key accepts every input list with any proof. -/
@[simp] theorem Crypto.verify_degenerate (C : Crypto) (inputs : PublicInputs) (π : C.Proof) :
    C.verify .degenerate inputs π := by
  simp only [Crypto.verify]

/-- A zero key accepts nothing. -/
@[simp] theorem Crypto.verify_zero (C : Crypto) (inputs : PublicInputs) (π : C.Proof) :
    ¬ C.verify .zero inputs π := by
  simp only [Crypto.verify, not_false_eq_true]

end ArmadaLean.Cctp
