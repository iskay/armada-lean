-- ABOUTME: Environment steps of the CCTP model: Circle's powers, the USDC issuer, other tokens, attestation, Aave.
-- ABOUTME: Each is a change the environment may make; liveness theorems carry hypotheses that limit them.
/-
  ArmadaLean.Cctp.Env — what the environment may do.

  Design record: model sheet v2.1 §5.6 and decision D2 (a): Circle's and the USDC issuer's
  powers are environment steps, and liveness theorems carry named hypotheses limiting them
  (`CircleLive`, `UsdcLive`, model sheet v2.1 §7). The attestation service's steps are stated
  over a burn or generic message and a flag saying whether the source chain still holds it
  (canonical) or has finalized it; the machine (`ArmadaLean.Cctp.System`) supplies those flags
  from the chain logs.

  Removing the local minter (`TokenMessengerV2.removeLocalMinter`) makes every burn and every
  mint on that chain revert. The model has no minter-presence flag; it gets the same effect by
  setting every burn limit and every minter allowance to zero.
-/
import ArmadaLean.Cctp.Yield
import ArmadaLean.Cctp.Circle

namespace ArmadaLean.Cctp

/-! ### Circle's powers on one chain (model sheet v2.1 §5.6; assumption T-11) -/

/-- A change Circle may make to its contracts on one chain. -/
inductive CircleOp where
  | setPaused (b : Bool)
  | setDenylisted (a : Term) (b : Bool)
  | setRemoteMessenger (d : Domain) (b : Bool)
  | setLinkedToken (d : Domain) (t : Term) (mintTok : Option Term)
  | setBurnLimit (t : Term) (n : Nat)
  | setMinFeeRate (t : Term) (n : Nat)
  | setFastFee (t : Term) (n : Nat)
  | setFeeRecipient (a : Term)
  | setMinterAllowance (t : Term) (n : Nat)
  | removeLocalMinter
  | setMaxShieldNotes (n : Nat)

/-- The effect of a Circle change. -/
def CircleOp.apply (cc : CircleChain) : CircleOp → CircleChain
  | .setPaused b => { cc with paused := b }
  | .setDenylisted a b => { cc with denylist := fun a' => if a' = a then b else cc.denylist a' }
  | .setRemoteMessenger d b =>
      { cc with remoteMessenger := fun d' => if d' = d then b else cc.remoteMessenger d' }
  | .setLinkedToken d t l =>
      { cc with linkedToken := fun d' t' => if d' = d ∧ t' = t then l else cc.linkedToken d' t' }
  | .setBurnLimit t n => { cc with burnLimit := fun t' => if t' = t then n else cc.burnLimit t' }
  | .setMinFeeRate t n => { cc with minFeeRate := fun t' => if t' = t then n else cc.minFeeRate t' }
  | .setFastFee t n => { cc with fastFee := fun t' => if t' = t then n else cc.fastFee t' }
  | .setFeeRecipient a => { cc with feeRecipient := a }
  | .setMinterAllowance t n =>
      { cc with minterAllowance := fun t' => if t' = t then n else cc.minterAllowance t' }
  | .removeLocalMinter => { cc with burnLimit := fun _ => 0, minterAllowance := fun _ => 0 }
  | .setMaxShieldNotes n => { cc with maxShieldNotes := n }

/-! ### The USDC issuer and other token issuers (assumption T-12) -/

/-- A change a token's issuer, or a misbehaving token, may make to a chain's ledger.
    `rewriteBalances` stands for any token that does not behave (rebasing, a balance that lies,
    fees on transfer, an issuer backdoor); the machine forbids it for the chain's USDC. -/
inductive LedgerOp where
  | setBlacklisted (t a : Term) (b : Bool)
  | setPaused (t : Term) (b : Bool)
  | rewriteBalances (t : Term) (f : Term → Nat)

/-- The effect of a ledger change. -/
def LedgerOp.apply (L : Ledger) : LedgerOp → Ledger
  | .setBlacklisted t a b =>
      { L with blacklisted := fun t' a' => if t' = t ∧ a' = a then b else L.blacklisted t' a' }
  | .setPaused t b => { L with paused := fun t' => if t' = t then b else L.paused t' }
  | .rewriteBalances t f => { L with balance := fun t' h => if t' = t then f h else L.balance t' h }

/-- The token a ledger change touches. -/
def LedgerOp.token : LedgerOp → Term
  | .setBlacklisted t _ _ => t
  | .setPaused t _ => t
  | .rewriteBalances t _ => t

/-- A ledger change the environment may make on a chain whose USDC is `usdc`: anything, except
    that USDC never misbehaves (its issuer may blacklist and pause, nothing more). -/
def LedgerOp.Allowed (usdc : Term) : LedgerOp → Prop
  | .rewriteBalances t _ => t ≠ usdc
  | _ => True

/-! ### The attestation service (assumptions T-1′, T-2b, T-8, T-9, T-21) -/

/-- Iris never gives one burn two nonces, and never gives two messages the same nonce. -/
def Iris.NonceFresh (iris : Iris) (att : Attestation) : Prop :=
  ∀ a ∈ iris.issued, (a.msg = att.msg → a.nonce = att.nonce) ∧ (a.nonce = att.nonce → a.msg = att.msg)

/-- Iris attests burn `b`. A FAST attestation needs the burn in its chain's canonical log and a
    `maxFee` that covers the fast fee; a STANDARD one needs the burn finalized. The executed
    finality is at least the burn's request and at least Circle's floor of 500
    (FinalityThresholds.sol:27), and below 2000 exactly for FAST (MessageTransmitterV2.sol:224-244
    routes on it). -/
def Iris.AttestBurn (iris : Iris) (b : BurnRecord) (canonical finalized : Prop) (fastFee : Nat)
    (fast : Bool) (att : Attestation) (iris' : Iris) : Prop :=
  att.msg = .burn b ∧ att.epoch = iris.epoch ∧ iris.NonceFresh att ∧
  b.requested.value ≤ att.executed ∧ 500 ≤ att.executed ∧
  (if fast = true then canonical ∧ att.executed < 2000 ∧ fastFee ≤ b.body.maxFee
   else finalized ∧ 2000 ≤ att.executed) ∧
  iris' = { iris with issued := att :: iris.issued }

/-- Iris attests a generic message its source chain still holds. -/
def Iris.AttestGeneric (iris : Iris) (g : GenericMessage) (canonical : Prop) (att : Attestation)
    (iris' : Iris) : Prop :=
  att.msg = .generic g ∧ att.epoch = iris.epoch ∧ iris.NonceFresh att ∧ canonical ∧
  iris' = { iris with issued := att :: iris.issued }

/-- Iris re-attests a message it attested before, in the current epoch, with the same nonce and
    fee, a finality at least as high and a fresh expiry, while the source chain still holds it
    (Circle's re-attestation API; model sheet v2.1 §5.6). -/
def Iris.Reattest (iris : Iris) (old new : Attestation) (canonical : Prop) (iris' : Iris) : Prop :=
  old ∈ iris.issued ∧ new.msg = old.msg ∧ new.nonce = old.nonce ∧
  new.feeExecuted = old.feeExecuted ∧ old.executed ≤ new.executed ∧ new.epoch = iris.epoch ∧
  canonical ∧ iris' = { iris with issued := new :: iris.issued }

/-- Circle rotates its attester set: every attestation issued so far stops verifying
    (MessageTransmitterV2.sol:286-313 checks the current set). -/
def Iris.rotate (iris : Iris) : Iris := { iris with epoch := iris.epoch + 1 }

/-! ### Aave (the vault's position; model sheet v2.1 §4.6) -/

/-- A change in the vault's Aave position: a gain or loss of value, a pause, illiquidity. -/
inductive AaveOp where
  | setAssets (n : Nat)
  | setPaused (b : Bool)
  | setIlliquid (b : Bool)

/-- The effect of an Aave change. -/
def AaveOp.apply (a : AaveState) : AaveOp → AaveState
  | .setAssets n => { a with vaultAssets := n }
  | .setPaused b => { a with paused := b }
  | .setIlliquid b => { a with illiquid := b }

end ArmadaLean.Cctp
