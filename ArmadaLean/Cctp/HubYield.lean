-- ABOUTME: The yield steps on the hub chain: vault deposit, redeem and harvest, and the adapter's lend and redeem.
-- ABOUTME: The adapter's steps compose the hub's transact and shield steps around a vault call, atomically.
/-
  ArmadaLean.Cctp.HubYield — the yield vault and the yield adapter.

  Design record: model sheet v2.1 §5.4 (decision DQ-10 (a): the full vault in scope). The
  vault's share and asset conversions are the pool model's `c2s` / `c2a`; this file adds the
  vault's fee accounting (ArmadaYieldVault.sol:358-410), its Aave calls, and its share token's
  mints and burns. The share token is the vault's own OpenZeppelin ERC-20: mints and burns
  check nothing but the burner's balance.

  `lendAndShield` and `redeemAndShield` (ArmadaYieldAdapter.sol:181-377) run a hub `transact`
  with the adapter as caller (the transaction's `adaptContract` must name the adapter, so
  only the adapter can submit it), a vault call, then a hub `shield` with the adapter as
  caller. The shield's note key comes from the `adaptParams` the user's proof binds, so the
  submitter cannot redirect it. The model has one adapter and one vault wired to each other
  and to the hub (`YieldWired`); the adapter's owner may point it elsewhere, which only puts
  the adapter's own balance at stake, and that balance is already the owner's to rescue.

  The vault reads its fee rate and harvest interval from its fee module when one is set. A
  fee module that reverts makes every vault step that reads the rate revert, including the
  owner's `setFeeModule`, which checkpoints at the old rate before switching
  (ArmadaYieldVault.sol:222-227). The model keeps that ordering exactly.

  The vault and the adapter each hold their own `nonReentrant` flag for the length of their
  steps. The vault's calls into Aave, into an untrusted underlying token and into its fee
  module's `recordYieldFee` open callback frames (model sheet v2.1 §5.0), between the state
  writes the code has made and those it has not.
-/
import ArmadaLean.Cctp.HubShield
import ArmadaLean.Cctp.HubTransact

namespace ArmadaLean.Cctp

/-! ### The vault's fee accounting -/

/-- The yield-fee rate the vault reads (`_effectiveYieldFeeBps`, ArmadaYieldVault.sol:413-418):
    its fee module's when one is set (`none` if that module reverts), its own otherwise. -/
def HubChain.vaultFeeBps (s : HubChain) : Option Nat :=
  match s.yield.vault.feeModule with
  | none => some s.yield.vault.yieldFeeBps
  | some m => if (s.comps.feeModule m).reverts = true then none else some (s.comps.feeModule m).yieldFeeBps

/-- The harvest interval the vault reads (`_effectiveHarvestInterval`,
    ArmadaYieldVault.sol:421-426): its fee module's when one is set, seven days otherwise. -/
def HubChain.harvestInterval (s : HubChain) : Option Nat :=
  match s.yield.vault.feeModule with
  | none => some 604800
  | some m =>
      if (s.comps.feeModule m).reverts = true then none else some (s.comps.feeModule m).harvestInterval

/-- Lifetime yield (`_lifetimeYield`, ArmadaYieldVault.sol:358-361) against the vault's Aave
    position worth `assets`; zero when the accounting is below the deposits. -/
def VaultState.lifetimeYield (v : VaultState) (assets : Nat) : Nat :=
  assets + v.cumulativeProtocolFee + v.totalPaidOut - v.totalDeposited

/-- The fee on yield above the high-water mark (`_unaccruedProtocolFee`,
    ArmadaYieldVault.sol:365-369). The rate is read only when there is such yield. -/
def VaultState.unaccruedFee (v : VaultState) (assets : Nat) (bps : Option Nat) : Option Nat :=
  let life := v.lifetimeYield assets
  if life ≤ v.yieldHighWaterMark then some 0
  else bps.map fun b => (life - v.yieldHighWaterMark) * b / 10000

/-- `_checkpointProtocolFee` (ArmadaYieldVault.sol:378-384): accrue the fee on new yield and
    raise the high-water mark. -/
def VaultState.checkpoint (v : VaultState) (assets : Nat) (bps : Option Nat) : Option VaultState :=
  let life := v.lifetimeYield assets
  if life ≤ v.yieldHighWaterMark then some v
  else bps.map fun b => { v with
    accruedProtocolFee := v.accruedProtocolFee + (life - v.yieldHighWaterMark) * b / 10000,
    yieldHighWaterMark := life }

/-- The assets the share holders can claim (`_userClaimableAssets`,
    ArmadaYieldVault.sol:388-391,517-521): the position minus the protocol's pending fee,
    floored at zero. -/
def VaultState.claimable (v : VaultState) (assets : Nat) (bps : Option Nat) : Option Nat :=
  (v.unaccruedFee assets bps).map fun u =>
    assets - (v.accruedProtocolFee + u - v.cumulativeProtocolFee)

/-! ### Aave and the share token -/

/-- `spoke.supply` after the vault's approval: Aave pulls `amt` of token `t` from the vault,
    and the vault's position grows. -/
def aaveSupply (L : Ledger) (a : AaveState) (t vault : Term) (amt : Nat) :
    Option (Ledger × AaveState) :=
  if a.paused = false then
    (L.transferFrom t a.spoke vault a.spoke amt).map
      fun L₁ => (L₁, { a with vaultAssets := a.vaultAssets + amt })
  else none

/-- `spoke.withdraw` to the vault: Aave unpaused and liquid, at most the position, paid from the
    spoke's USDC. -/
def aaveWithdraw (L : Ledger) (a : AaveState) (t vault : Term) (amt : Nat) :
    Option (Ledger × AaveState) :=
  if a.paused = false ∧ a.illiquid = false ∧ amt ≤ a.vaultAssets then
    (L.transfer t a.spoke vault amt).map fun L₁ => (L₁, { a with vaultAssets := a.vaultAssets - amt })
  else none

/-- A call into Aave: untrusted code, so a frame opens before and after its effect. -/
def HubChain.AaveCall (s : HubChain) (F : Frame)
    (op : Ledger → AaveState → Option (Ledger × AaveState)) (s' : HubChain) : Prop :=
  ∃ s₁ L₂ a₂, F s s₁ ∧ op s₁.ledger s₁.yield.aave = some (L₂, a₂) ∧
    F { s₁ with ledger := L₂, yield := { s₁.yield with aave := a₂ } } s'

/-- Mint vault shares (`_mint`): no checks. -/
def mintShares (L : Ledger) (share dst : Term) (n : Nat) : Ledger :=
  L.setBalance share dst (L.balance share dst + n)

/-- Burn vault shares (`_burn`): the holder must have them. -/
def burnShares (L : Ledger) (share h : Term) (n : Nat) : Option Ledger :=
  if n ≤ L.balance share h then some (L.setBalance share h (L.balance share h - n)) else none

/-- The dead address the first deposit locks `LOCKED_SHARES` to (ArmadaYieldVault.sol:85). -/
def lockedSharesHolder : Term := Term.val 0xdEaD

/-- Replace the vault's state. -/
def HubChain.setVault (s : HubChain) (v : VaultState) : HubChain :=
  { s with yield := { s.yield with vault := v } }

/-- Replace the adapter's state. -/
def HubChain.setAdapter (s : HubChain) (ad : AdapterState) : HubChain :=
  { s with yield := { s.yield with adapter := ad } }

/-! ### Vault steps -/

/-- `vault.deposit(assets, receiver)` by `caller` (ArmadaYieldVault.sol:275-305), minting
    `shares` to the receiver. The first deposit locks `LOCKED_SHARES` to the dead address and
    the deposit is counted before the transfers; the receiver's shares are minted last. -/
def HubChain.VaultDeposit (s : HubChain) (F : Frame) (caller receiver : Term) (assets shares : Nat)
    (s' : HubChain) : Prop :=
  let v := s.yield.vault
  v.guardOn = false ∧                                                         -- VD0
  0 < assets ∧ receiver ≠ Term.val 0 ∧                                        -- VD1, VD2
  ∃ minted, (v.totalSupply = 0 ∧ minted = assets ∨
    v.totalSupply ≠ 0 ∧ ∃ cl, v.claimable s.yield.aave.vaultAssets s.vaultFeeBps = some cl ∧
      minted = c2s v.totalSupply cl assets) ∧
  0 < minted ∧                                                                -- VD3
  (v.totalSupply = 0 → LOCKED_SHARES < minted) ∧                              -- VD4
  shares = (if v.totalSupply = 0 then minted - LOCKED_SHARES else minted) ∧
  let L₀ := if v.totalSupply = 0 then mintShares s.ledger v.self lockedSharesHolder LOCKED_SHARES else s.ledger
  let s₁ := ({ s with ledger := L₀ } : HubChain).setVault
    { v with guardOn := true, totalDeposited := v.totalDeposited + assets,
             totalSupply := if v.totalSupply = 0 then LOCKED_SHARES else v.totalSupply }
  ∃ s₂, s₁.TokenCall F v.underlying                                           -- VD5
    (fun L => L.transferFrom v.underlying v.self caller v.self assets) s₂ ∧
  ∃ s₃, s₂.TokenCall F v.underlying
    (fun L => L.approve v.underlying v.self s₂.yield.aave.spoke assets) s₃ ∧
  ∃ s₄, s₃.AaveCall F (fun L a => aaveSupply L a v.underlying v.self assets) s₄ ∧  -- VD6
  let v₄ := s₄.yield.vault
  s' = ({ s₄ with ledger := mintShares s₄.ledger v.self receiver shares } : HubChain).setVault
    { v₄ with guardOn := false, totalSupply := v₄.totalSupply + shares }

/-- `_settleProtocolFee` at time `now` (ArmadaYieldVault.sol:397-410): checkpoint, then pay the
    unpaid fee from Aave to the treasury and record it with the fee module, which accepts only
    its own vault (ArmadaFeeModule.sol:201-202). The recorded fee counts as wind-down revenue
    when that module is the revenue counter's fee collector. -/
def HubChain.SettleFee (s : HubChain) (F : Frame) (now : Nat) (s' : HubChain) : Prop :=
  let v := s.yield.vault
  ∃ v₁, v.checkpoint s.yield.aave.vaultAssets s.vaultFeeBps = some v₁ ∧
  v₁.cumulativeProtocolFee ≤ v₁.accruedProtocolFee ∧
  let fee := v₁.accruedProtocolFee - v₁.cumulativeProtocolFee
  if fee = 0 then s' = s.setVault { v₁ with lastHarvestTime := now }
  else
    ∃ s₂, (s.setVault v₁).AaveCall F (fun L a => aaveWithdraw L a v.underlying v.self fee) s₂ ∧
    ∃ s₃, s₂.TokenCall F v.underlying (fun L => L.transfer v.underlying v.self v.treasury fee) s₃ ∧
    let s₄ := s₃.setVault { s₃.yield.vault with
      cumulativeProtocolFee := s₃.yield.vault.cumulativeProtocolFee + fee }
    ∃ s₅, (v.feeModule = none ∧ s₅ = s₄ ∨
      ∃ m, v.feeModule = some m ∧ (s₄.comps.feeModule m).reverts = false ∧
        (s₄.comps.feeModule m).yieldVault = v.self ∧
        F { s₄ with comps := if m = s₄.comps.windDown.feeCollector
          then s₄.comps.addPending fee else s₄.comps } s₅) ∧
    s' = s₅.setVault { s₅.yield.vault with lastHarvestTime := now }

/-- `vault.redeem(shares, receiver, owner)` by `caller` at time `now`
    (ArmadaYieldVault.sol:316-348), paying `assets` to the receiver. -/
def HubChain.VaultRedeem (s : HubChain) (F : Frame) (now : Nat) (caller receiver owner : Term)
    (shares assets : Nat) (s' : HubChain) : Prop :=
  let v := s.yield.vault
  v.guardOn = false ∧                                                         -- VR0
  0 < shares ∧ receiver ≠ Term.val 0 ∧                                        -- VR1, VR2
  ∃ L₀, (caller = owner ∧ L₀ = s.ledger ∨                                     -- VR3
    caller ≠ owner ∧ shares ≤ s.ledger.allowance v.self owner caller ∧
      L₀ = s.ledger.setAllowance v.self owner caller (s.ledger.allowance v.self owner caller - shares)) ∧
  ∃ s₁, (({ s with ledger := L₀ } : HubChain).setVault { v with guardOn := true }).SettleFee F now s₁ ∧  -- VR4
  let v₁ := s₁.yield.vault
  (v₁.totalSupply = 0 ∧ assets = shares ∨
    v₁.totalSupply ≠ 0 ∧ ∃ cl, v₁.claimable s₁.yield.aave.vaultAssets s₁.vaultFeeBps = some cl ∧
      assets = c2a v₁.totalSupply cl shares) ∧
  ∃ L₂, burnShares s₁.ledger v.self owner shares = some L₂ ∧                  -- VR5
  let s₂ := ({ s₁ with ledger := L₂ } : HubChain).setVault
    { v₁ with totalPaidOut := v₁.totalPaidOut + assets, totalSupply := v₁.totalSupply - shares }
  ∃ s₃, s₂.AaveCall F (fun L a => aaveWithdraw L a v.underlying v.self assets) s₃ ∧   -- VR6
  ∃ s₄, s₃.TokenCall F v.underlying                                           -- VR7
    (fun L => L.transfer v.underlying v.self receiver assets) s₄ ∧
  s' = s₄.setVault { s₄.yield.vault with guardOn := false }

/-- `harvestProtocolFee` by anyone at time `now` (ArmadaYieldVault.sol:237-243). -/
def HubChain.Harvest (s : HubChain) (F : Frame) (now : Nat) (s' : HubChain) : Prop :=
  s.yield.vault.guardOn = false ∧
  ∃ i, s.harvestInterval = some i ∧ s.yield.vault.lastHarvestTime + i ≤ now ∧
  ∃ s₁, (s.setVault { s.yield.vault with guardOn := true }).SettleFee F now s₁ ∧
  s' = s₁.setVault { s₁.yield.vault with guardOn := false }

/-- A vault owner step (ArmadaYieldVault.sol:197-227). -/
inductive VaultOwnerOp where
  | setYieldFeeBps (b : Nat)
  | setFeeModule (a : Option Term)
  | transferOwnership (n : Term)

/-- A vault owner step by `caller`. Both rate changes checkpoint at the current rate first. -/
def HubChain.VaultOwnerStep (s : HubChain) (caller : Term) (op : VaultOwnerOp) (s' : HubChain) :
    Prop :=
  let v := s.yield.vault
  caller = v.owner ∧
  match op with
  | .setYieldFeeBps b =>
      v.feeModule = none ∧ 100 ≤ b ∧ b ≤ 5000 ∧
      ∃ v₁, v.checkpoint s.yield.aave.vaultAssets s.vaultFeeBps = some v₁ ∧
        s' = { s with yield := { s.yield with vault := { v₁ with yieldFeeBps := b } } }
  | .setFeeModule a =>
      ∃ v₁, v.checkpoint s.yield.aave.vaultAssets s.vaultFeeBps = some v₁ ∧
        s' = { s with yield := { s.yield with vault := { v₁ with feeModule := a } } }
  | .transferOwnership n =>
      n ≠ Term.val 0 ∧ s' = { s with yield := { s.yield with vault := { v with owner := n } } }

/-! ### Adapter steps -/

/-- The adapter, the vault and the hub are wired together: the adapter's vault is the vault,
    its USDC is the vault's underlying token and the hub's USDC, and it serves the hub. -/
def HubChain.YieldWired (s : HubChain) : Prop :=
  s.yield.adapter.vault = s.yield.vault.self ∧ s.yield.adapter.usdc = s.yield.vault.underlying ∧
  s.yield.adapter.usdc = s.hub.usdc ∧ s.yield.adapter.privacyPool = s.hub.self

/-- The adapter's registry check (ArmadaYieldAdapter.sol:138-152): authorized, or also
    withdraw-only when `withdrawOnlyOK`; a reverting registry reverts. -/
def HubChain.AdapterAllowed (s : HubChain) (withdrawOnlyOK : Bool) : Prop :=
  let r := s.comps.registry s.yield.adapter.registry
  r.reverts = false ∧
  (r.authorized s.yield.adapter.self = true ∨
    withdrawOnlyOK = true ∧ r.withdrawOnly s.yield.adapter.self = true)

/-- The `adaptParams` a lend binds (`YieldAdaptParams.encode`, YieldAdaptParams.sol): the note
    key and its ciphertext `ct`. -/
def yieldLendParams (npk ct : Term) : Term := Term.keccak [npk, ct]

/-- The `adaptParams` a redeem binds: the user's note key and ciphertext, the fee note's, and
    the fee amount. -/
def yieldRedeemParams (npk ct feeNpk feeCt : Term) (fee : Nat) : Term :=
  Term.keccak [npk, ct, feeNpk, feeCt, Term.val fee]

/-- A shield request the adapter builds, its value cast to `uint120` as the code does
    (ArmadaYieldAdapter.sol:245,363,372). -/
def adapterRequest (npk token : Term) (n : Nat) : ShieldRequest :=
  ⟨npk, token, ⟨n % 2 ^ 120, Nat.mod_lt _ (Nat.two_pow_pos 120)⟩⟩

/-- `lendAndShield` (ArmadaYieldAdapter.sol:181-254): unshield USDC to the adapter, deposit it,
    shield the shares to the bound note key. `decoded` is the transact's ghost decoding; `legs`
    the shield's fee legs. -/
def HubChain.LendAndShield {C : Crypto} (s : HubChain) (F : Frame) (tx : HubTx C) (npk ct : Term)
    (decoded : List (Option CommitmentPreimage)) (legs : List FeeLeg) (s' : HubChain) : Prop :=
  let ad := s.yield.adapter
  ad.guardOn = false ∧                                                        -- YL0
  s.YieldWired ∧ s.AdapterAllowed false ∧                                     -- YL1, YL2
  tx.bp.adaptContract = some ad.self ∧                                        -- YL3
  tx.bp.adaptParams = yieldLendParams npk ct ∧                                -- YL4
  tx.note.token = ad.usdc ∧ tx.kind = .normal ∧ tx.note.npk = ad.self ∧       -- YL5, YL6
  let s₀ := s.setAdapter { ad with guardOn := true }
  ∃ s₁, s₀.LocalTransactBatch F ad.self [tx] decoded s₁ ∧                     -- YL7
  0 < tx.note.value ∧                                                         -- YL8
  s₁.ledger.balance ad.usdc ad.self - s₀.ledger.balance ad.usdc ad.self = tx.note.value ∧
  ∃ s₂ shares, s₁.VaultDeposit F ad.self ad.self tx.note.value shares s₂ ∧    -- YL9
  ∃ L₃, s₂.ledger.approve ad.vault ad.self s.hub.self shares = some L₃ ∧      -- YL10
  ∃ s₄, ({ s₂ with ledger := L₃ } : HubChain).LocalShieldBatch F ad.self none -- YL11
    [adapterRequest npk ad.vault shares] legs s₄ ∧
  s' = s₄.setAdapter { s₄.yield.adapter with guardOn := false }

/-- `redeemAndShield` at time `now` (ArmadaYieldAdapter.sol:267-377): unshield shares to the
    adapter, redeem them, shield the proceeds minus the bound fee to the bound note key and the
    fee to the bound fee note key, in one privileged shield. -/
def HubChain.RedeemAndShield {C : Crypto} (s : HubChain) (F : Frame) (now : Nat) (tx : HubTx C)
    (npk ct feeNpk feeCt : Term) (feeAmount : Nat) (decoded : List (Option CommitmentPreimage))
    (legs : List FeeLeg) (s' : HubChain) : Prop :=
  let ad := s.yield.adapter
  ad.guardOn = false ∧                                                        -- YR0
  s.YieldWired ∧ s.AdapterAllowed true ∧                                      -- YR1, YR2
  tx.bp.adaptContract = some ad.self ∧                                        -- YR3
  tx.bp.adaptParams = yieldRedeemParams npk ct feeNpk feeCt feeAmount ∧       -- YR4
  tx.note.token = ad.vault ∧ tx.kind = .normal ∧ tx.note.npk = ad.self ∧      -- YR5, YR6
  let s₀ := s.setAdapter { ad with guardOn := true }
  ∃ s₁, s₀.LocalTransactBatch F ad.self [tx] decoded s₁ ∧                     -- YR7
  0 < tx.note.value ∧                                                         -- YR8
  s₁.ledger.balance ad.vault ad.self - s₀.ledger.balance ad.vault ad.self = tx.note.value ∧
  ∃ L₂, s₁.ledger.approve ad.vault ad.self ad.vault tx.note.value = some L₂ ∧
  ∃ s₂ assets, ({ s₁ with ledger := L₂ } : HubChain).VaultRedeem F now ad.self ad.self ad.self
    tx.note.value assets s₂ ∧                                                 -- YR9
  feeAmount ≤ assets ∧ (feeAmount = 0 ∨ feeNpk ≠ Term.val 0) ∧               -- YR10, YR11
  ∃ L₃, s₂.ledger.approve ad.usdc ad.self s.hub.self assets = some L₃ ∧
  ∃ s₄, ({ s₂ with ledger := L₃ } : HubChain).LocalShieldBatch F ad.self none  -- YR12
    (adapterRequest npk ad.usdc (assets - feeAmount) ::
      (if feeAmount = 0 then [] else [adapterRequest feeNpk ad.usdc feeAmount])) legs s₄ ∧
  s' = s₄.setAdapter { s₄.yield.adapter with guardOn := false }

/-- An adapter owner step (ArmadaYieldAdapter.sol:120-133,425-431). -/
inductive AdapterOwnerOp where
  | setPrivacyPool (a : Term)
  | transferOwnership (n : Term)
  | rescueTokens (t dst : Term) (amt : Nat)

/-- An adapter owner step by `caller`. -/
def HubChain.AdapterOwnerStep (s : HubChain) (caller : Term) (op : AdapterOwnerOp) (s' : HubChain) :
    Prop :=
  let ad := s.yield.adapter
  caller = ad.owner ∧
  match op with
  | .setPrivacyPool a => s' = { s with yield := { s.yield with adapter := { ad with privacyPool := a } } }
  | .transferOwnership n =>
      n ≠ Term.val 0 ∧ s' = { s with yield := { s.yield with adapter := { ad with owner := n } } }
  | .rescueTokens t dst amt =>
      ∃ L', s.ledger.transfer t ad.self dst amt = some L' ∧ s' = { s with ledger := L' }

end ArmadaLean.Cctp
