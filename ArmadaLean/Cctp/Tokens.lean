-- ABOUTME: The token ledger of one chain: balances, blacklists, pauses and allowances, with the checks USDC applies.
-- ABOUTME: Transfers, transferFrom, approvals, mints and burns succeed only when USDC's FiatToken checks pass.
/-
  ArmadaLean.Cctp.Tokens — the token ledger of one chain.

  Design record: model sheet v2.1 §4.8 (assumption T-12: USDC is well-behaved) and the
  re-check's USDC findings (`.context/recheck/triage.md`, T6). Tokens and holders are
  symbolic terms (`ArmadaLean.Token` keeps a token as its address term). The checks are
  those of Circle's USDC contract, FiatTokenV1 (circlefin/stablecoin-evm,
  `contracts/v1/FiatTokenV1.sol`): `transfer` and `transferFrom` require the token not
  paused and no party blacklisted (FiatTokenV1.sol:287-293 for `transfer`); `mint` requires
  the minter and the recipient not blacklisted (FiatTokenV1.sol:121-127); `approve`
  requires owner and spender not blacklisted. Other tokens follow the same ledger rules
  when they behave; a misbehaving token is an environment step that rewrites its
  balances (`ArmadaLean.Cctp.Env`), and the isolation theorem bounds the damage.
-/
import ArmadaLean.Cctp.Types

namespace ArmadaLean.Cctp

/-- The token ledger of one chain, indexed by token address, then holder.
    * `balance t h`: holder `h`'s balance of token `t`.
    * `blacklisted t a`: the issuer of `t` has blacklisted `a`.
    * `paused t`: the issuer of `t` has paused it.
    * `allowance t o sp`: what spender `sp` may move from owner `o`. -/
structure Ledger where
  balance : Term → Term → Nat
  blacklisted : Term → Term → Bool
  paused : Term → Bool
  allowance : Term → Term → Term → Nat

namespace Ledger

/-- Set one holder's balance of one token. -/
def setBalance (L : Ledger) (t h : Term) (v : Nat) : Ledger :=
  { L with balance := fun t' h' => if t' = t ∧ h' = h then v else L.balance t' h' }

/-- Set one allowance. -/
def setAllowance (L : Ledger) (t o sp : Term) (v : Nat) : Ledger :=
  { L with allowance := fun t' o' sp' => if t' = t ∧ o' = o ∧ sp' = sp then v else L.allowance t' o' sp' }

/-- `transfer(to, amt)` called by `src` (FiatTokenV1.sol:287-293): not paused, neither party
    blacklisted, enough balance. -/
def TransferOK (L : Ledger) (t src dst : Term) (amt : Nat) : Prop :=
  L.paused t = false ∧ L.blacklisted t src = false ∧ L.blacklisted t dst = false ∧
    amt ≤ L.balance t src

instance (L : Ledger) (t src dst : Term) (amt : Nat) : Decidable (L.TransferOK t src dst amt) := by
  unfold TransferOK; infer_instance

/-- The effect of a transfer: `amt` moves from `src` to `dst`. -/
def transferEffect (L : Ledger) (t src dst : Term) (amt : Nat) : Ledger :=
  let L₁ := L.setBalance t src (L.balance t src - amt)
  L₁.setBalance t dst (L₁.balance t dst + amt)

/-- A transfer: its effect when the checks pass, a revert otherwise. -/
def transfer (L : Ledger) (t src dst : Term) (amt : Nat) : Option Ledger :=
  if L.TransferOK t src dst amt then some (L.transferEffect t src dst amt) else none

/-- `transferFrom(from, to, amt)` called by spender `sp`: the transfer checks, the spender not
    blacklisted, and enough allowance. -/
def TransferFromOK (L : Ledger) (t sp src dst : Term) (amt : Nat) : Prop :=
  L.TransferOK t src dst amt ∧ L.blacklisted t sp = false ∧ amt ≤ L.allowance t src sp

instance (L : Ledger) (t sp src dst : Term) (amt : Nat) :
    Decidable (L.TransferFromOK t sp src dst amt) := by
  unfold TransferFromOK; infer_instance

/-- A `transferFrom`: the allowance falls by `amt`, then the transfer happens. -/
def transferFrom (L : Ledger) (t sp src dst : Term) (amt : Nat) : Option Ledger :=
  if L.TransferFromOK t sp src dst amt then
    some ((L.setAllowance t src sp (L.allowance t src sp - amt)).transferEffect t src dst amt)
  else none

/-- `approve(sp, amt)` called by `o`: not paused, neither party blacklisted. -/
def ApproveOK (L : Ledger) (t o sp : Term) : Prop :=
  L.paused t = false ∧ L.blacklisted t o = false ∧ L.blacklisted t sp = false

instance (L : Ledger) (t o sp : Term) : Decidable (L.ApproveOK t o sp) := by
  unfold ApproveOK; infer_instance

/-- An approval: the allowance is set to `amt`. -/
def approve (L : Ledger) (t o sp : Term) (amt : Nat) : Option Ledger :=
  if L.ApproveOK t o sp then some (L.setAllowance t o sp amt) else none

/-- `mint(to, amt)` by minter `m` (FiatTokenV1.sol:121-127): not paused, minter and
    recipient not blacklisted. Circle's own minter allowance is checked by the caller
    (`ArmadaLean.Cctp.Circle`). -/
def MintOK (L : Ledger) (t m dst : Term) : Prop :=
  L.paused t = false ∧ L.blacklisted t m = false ∧ L.blacklisted t dst = false

instance (L : Ledger) (t m dst : Term) : Decidable (L.MintOK t m dst) := by
  unfold MintOK; infer_instance

/-- A mint: `to`'s balance grows by `amt`. -/
def mint (L : Ledger) (t m dst : Term) (amt : Nat) : Option Ledger :=
  if L.MintOK t m dst then some (L.setBalance t dst (L.balance t dst + amt)) else none

/-- A burn of `amt` from holder `h`'s own balance: not paused, `h` not blacklisted, enough
    balance. -/
def BurnOK (L : Ledger) (t h : Term) (amt : Nat) : Prop :=
  L.paused t = false ∧ L.blacklisted t h = false ∧ amt ≤ L.balance t h

instance (L : Ledger) (t h : Term) (amt : Nat) : Decidable (L.BurnOK t h amt) := by
  unfold BurnOK; infer_instance

/-- A burn: `h`'s balance falls by `amt`. -/
def burn (L : Ledger) (t h : Term) (amt : Nat) : Option Ledger :=
  if L.BurnOK t h amt then some (L.setBalance t h (L.balance t h - amt)) else none

@[simp] theorem setBalance_balance_self (L : Ledger) (t h : Term) (v : Nat) :
    (L.setBalance t h v).balance t h = v := by
  simp only [setBalance, and_self, if_true]


end Ledger

end ArmadaLean.Cctp
