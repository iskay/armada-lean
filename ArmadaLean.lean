/-
  Armada Lean — formal verification of shielded-pool security properties.
  Root module: imports all verified components.
-/
import ArmadaLean.Machine
import ArmadaLean.Types.Reachable
import ArmadaLean.Types.Address
import ArmadaLean.SpecTools
import ArmadaLean.Field
import ArmadaLean.Poseidon
import ArmadaLean.Token
import ArmadaLean.BoundParams
import ArmadaLean.RangeCheck
import ArmadaLean.ValueConservation
import ArmadaLean.Nullifier
import ArmadaLean.Merkle
import ArmadaLean.Transact
import ArmadaLean.TransactOwned
import ArmadaLean.PoolOwned
import ArmadaLean.Pool
import ArmadaLean.PoolMachine
import ArmadaLean.PoolSafety
import ArmadaLean.PoolNonVacuity
import ArmadaLean.Yield.Vault
import ArmadaLean.Fee
-- CCTP cross-chain model (model sheet v2.1; iskay/armada-lean#1)
import ArmadaLean.Cctp.Types
import ArmadaLean.Cctp.Crypto
import ArmadaLean.Cctp.Chain
import ArmadaLean.Cctp.Tokens
import ArmadaLean.Cctp.Circle
import ArmadaLean.Cctp.Shared
import ArmadaLean.Cctp.Hub
import ArmadaLean.Cctp.Client
import ArmadaLean.Cctp.Router
import ArmadaLean.Cctp.Yield
import ArmadaLean.Cctp.HubChain
import ArmadaLean.Cctp.HubShield
import ArmadaLean.Cctp.HubTransact
import ArmadaLean.Cctp.ClientChain
import ArmadaLean.Cctp.Delivery
-- Nitro protocol specification (S1 ForceMove, S2 Nitro, S3 SATP); see docs/nitro-theorems.md
import ArmadaLean.Nitro.Address
import ArmadaLean.Nitro.Outcome
import ArmadaLean.Nitro.Channel
import ArmadaLean.Nitro.Adjudicator
import ArmadaLean.Nitro.Strategy
import ArmadaLean.Nitro.Reachable
import ArmadaLean.Nitro.Value
import ArmadaLean.Nitro.Constructions
import ArmadaLean.Nitro.SATP
import ArmadaLean.Nitro.Safety
import ArmadaLean.Nitro.Liveness
import ArmadaLean.Nitro.TakeOut
import ArmadaLean.Nitro.NonVacuity
import ArmadaLean.Nitro.OpEquations
import ArmadaLean.Spec
import ArmadaLean.Witness
