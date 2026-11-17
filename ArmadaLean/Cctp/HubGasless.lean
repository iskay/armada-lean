-- ABOUTME: The hub's gasless shield wrapper: users sign intents and permits, a relayer submits a batched local shield.
-- ABOUTME: The wrapper pulls the user's USDC and shields it as the caller; its pool address is immutable but unchecked.
/-
  ArmadaLean.Cctp.HubGasless — the hub chain's gasless shield (GaslessShieldWrapper.sol).

  Design record: model sheet v2.1 §5.1 (`gaslessShieldHub`). Intents and permits are symbolic,
  as on the client (`ArmadaLean.Cctp.Client`, assumption T-20): one enters the state only by a
  step of its signer. The wrapper's in-call `permit` (GaslessShieldWrapper.sol:201-208) runs
  under `try`, so it is `SubmitPermit` immediately before the shield: when it fails, the
  allowance must already cover the total, which the pull checks.

  The wrapper's pool address is fixed at construction and checked only to be non-zero
  (GaslessShieldWrapper.sol:100-105). When it is not the hub, the wrapper's `shield` call goes
  to a contract of the deployer's choosing: a callback frame, with the user's USDC already
  pulled into the wrapper and approved to that contract.
-/
import ArmadaLean.Cctp.HubShield

namespace ArmadaLean.Cctp

/-- A user signs a hub gasless intent. -/
def HubChain.SignIntent (s : HubChain) (signer : Term) (i : HubIntent) (s' : HubChain) : Prop :=
  i.user = signer ∧
  s' = { s with gasless := { s.gasless with signedIntents := i :: s.gasless.signedIntents } }

/-- A token holder signs an ERC-2612 permit on the hub chain. -/
def HubChain.SignPermit (s : HubChain) (signer : Term) (pm : Permit) (s' : HubChain) : Prop :=
  pm.owner = signer ∧
  s' = { s with gasless := { s.gasless with signedPermits := pm :: s.gasless.signedPermits } }

/-- Anyone submits a signed, unused, unexpired permit on the hub chain's USDC: the allowance is
    set, under USDC's approve checks, and the permit is used. -/
def HubChain.SubmitPermit (s : HubChain) (now : Nat) (pm : Permit) (s' : HubChain) : Prop :=
  pm ∈ s.gasless.signedPermits ∧ pm ∉ s.gasless.usedPermits ∧ now ≤ pm.deadline ∧
  ∃ L', s.ledger.approve s.gasless.usdc pm.owner pm.spender pm.value = some L' ∧
  s' = { s with ledger := L', gasless := { s.gasless with usedPermits := pm :: s.gasless.usedPermits } }

/-- A relayer submits a user's signed hub intent at time `now` (`gaslessShield`,
    GaslessShieldWrapper.sol:120-218): unexpired, the user's current nonce (consumed), signed;
    every request is in the wrapper's USDC with a positive value; the wrapper pulls the total
    from the user, approves the pool (reset to zero first), and calls the pool's `shield` with
    the intent's integrator, as the caller. `legs` is the shield's fee split. -/
def HubChain.GaslessShield (s : HubChain) (F : Frame) (now : Nat) (i : HubIntent)
    (legs : List FeeLeg) (s' : HubChain) : Prop :=
  let g := s.gasless
  now ≤ i.deadline ∧                                                          -- GH1
  i.nonce = g.nonces i.user ∧                                                 -- GH2
  i ∈ g.signedIntents ∧                                                       -- GH3
  i.reqs ≠ [] ∧ (∀ r ∈ i.reqs, r.token = g.usdc ∧ 0 < r.value.val) ∧          -- GH4
  let total := (i.reqs.map (·.value.val)).sum
  let s₁ := { s with gasless := { g with
    nonces := fun u => if u = i.user then g.nonces u + 1 else g.nonces u } }
  ∃ s₂, s₁.TokenCall F g.usdc (fun L => L.transferFrom g.usdc g.self i.user g.self total) s₂ ∧  -- GH5
  ∃ s₃, s₂.TokenCall F g.usdc (fun L =>
    (L.approve g.usdc g.self g.privacyPool 0).bind fun L₁ => L₁.approve g.usdc g.self g.privacyPool total) s₃ ∧
  (g.privacyPool = s.hub.self ∧ s₃.LocalShieldBatch F g.self i.integrator i.reqs legs s' ∨  -- GH6
    g.privacyPool ≠ s.hub.self ∧ F s₃ s')

end ArmadaLean.Cctp
