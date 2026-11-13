-- ABOUTME: Contracts the hub reaches by address: the pause controller, the fee module, the adapter registry, wind-down.
-- ABOUTME: Each may be shared by several pools, may revert, and is adversarial within the checks its callers apply.
/-
  ArmadaLean.Cctp.Shared — components the hub pool points to by address.

  Design record: model sheet v2.1 §4.5. The pool holds only the address of each component
  (`shieldPauseContract`, `feeModule`, `adapterRegistry`, PrivacyPoolStorage.sol), so one
  component may serve several pools: a pause controller wired to an old and a new hub
  (finding N-6), and one fee-module proxy wired to both the pool and the yield vault
  (`scripts/deploy_fee_module.ts:99-108`, re-check finding RC2-12). Under decision D1 (a)
  the owner and governance are adversarial, so the model keeps each component's state as
  free as the code allows; a `reverts` flag stands for a component whose calls revert
  (an EOA, a broken upgrade).
-/
import ArmadaLean.Cctp.Types

namespace ArmadaLean.Cctp

/-- A shield pause controller as the pool sees it (`IShieldPauseController`,
    IShieldPauseController.sol:11-25): three views, which may revert. The shipped
    controller (ShieldPauseController.sol:80-90) makes `shieldsPaused` and `withdrawOnly`
    permanently true once wind-down is active; an owner may install any controller. -/
structure PauseController where
  shieldsPaused : Bool
  withdrawOnly : Bool
  emergencyPaused : Bool
  windDownActive : Bool
  reverts : Bool

/-- The fee module (ArmadaFeeModule.sol), one proxy serving the pool's shield fees and the
    vault's yield fee. Its shield split is chosen per call by the adversary within the
    pool's guards (ShieldModule.sol:237-250), so it needs no state here. `privacyPool` is
    the single pool whose `recordShieldFee` calls it accepts (ArmadaFeeModule.sol:166,312);
    `yieldFeeBps` is the rate the vault reads (not clamped, solvency finding YIELD-02). -/
structure FeeModule where
  privacyPool : Term
  yieldFeeBps : Nat
  harvestInterval : Nat
  reverts : Bool

/-- The adapter registry (AdapterRegistry.sol): authorized and withdraw-only adapters,
    governance-controlled. The pool's fee exemption reads it on every shield
    (ShieldModule.sol:184,258-263,311). -/
structure AdapterRegistry where
  authorized : Term → Bool
  withdrawOnly : Term → Bool
  reverts : Bool

/-- The wind-down contract (ArmadaWindDown.sol): anyone may trigger wind-down once the
    deadline has passed and recognized revenue is below the threshold
    (ArmadaWindDown.sol:153-174); the revenue sync before the check may fail and leave a
    stale value (ArmadaWindDown.sol:167). -/
structure WindDown where
  deadline : Nat
  threshold : Nat
  revenue : Nat
  triggered : Bool
  pauseController : Term

/-- Every shared component, by address. The hub and the yield contracts hold addresses into
    these maps. -/
structure Components where
  pause : Term → PauseController
  feeModule : Term → FeeModule
  registry : Term → AdapterRegistry
  windDown : WindDown

end ArmadaLean.Cctp
