import SP1Clean.Model.FinalMemoryValue
import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection

/-! # Finalizers retaining their original rows and publishing target-check receipts

The wrapper composes the original provider and publishes its full output record. It adds no
witness cells, assertions, or lookups. Every original channel is retained, so its ordered Memory
inventory can be projected without assuming that the appended target checks balance Memory.
-/

namespace SP1Clean.FinalMemoryReceipt

open Circuit Air.Flat Channels

variable {p : ℕ} [Fact p.Prime]
variable {Input : TypeMap} [ProvableType Input]

attribute [local circuit_norm] List.subset_append_left

def circuit (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg) :
    GeneralFormalCircuit (ZMod p) Input MemoryMsg where
  name := provider.name
  main input := do
    let record ← provider input
    (FinalMemoryValue.channel ram).push record
    return record
  Assumptions := provider.Assumptions
  Spec := provider.Spec
  ProverAssumptions := provider.ProverAssumptions
  channelsWithRequirements := provider.channelsWithRequirements ++ [(FinalMemoryValue.channel ram).toRaw]
  soundness := by
    circuit_proof_start [FinalMemoryValue.channel]
    exact ⟨h_holds h_assumptions, Or.inr h_assumptions⟩
  completeness := by
    circuit_proof_start [FinalMemoryValue.channel]
    exact h_assumptions

theorem width (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg) :
    ({ circuit := circuit ram provider } : Component (ZMod p)).width = ({ circuit := provider } : Component (ZMod p)).width := rfl

theorem constraints (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg) :
    ({ circuit := circuit ram provider } : Component (ZMod p)).operations.constraints =
      ({ circuit := provider } : Component (ZMod p)).operations.constraints := by
  simp only [Component.constraints_eq, Component.rowOperations, circuit, circuit_norm]

theorem lookups (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg) :
    ({ circuit := circuit ram provider } : Component (ZMod p)).operations.lookups =
      ({ circuit := provider } : Component (ZMod p)).operations.lookups := by
  simp only [Component.lookups_eq, Component.rowOperations, circuit, circuit_norm]

/-- Exactly one new receipt is appended, at the original provider's full output record. -/
theorem receipt_interactions (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg)
    (input : Var Input (ZMod p)) (offset : ℕ) :
    (((circuit ram provider).main input).operations offset).interactionsWith (FinalMemoryValue.channel ram).toRaw =
      ((provider.main input).operations offset).interactionsWith (FinalMemoryValue.channel ram).toRaw ++
        [((FinalMemoryValue.channel ram).pushed (provider.output input offset)).toRaw] := by
  simp only [circuit, circuit_norm, GeneralFormalCircuit.toSubcircuit_interactions]
  rfl

theorem interactions (ram : Bool) (provider : GeneralFormalCircuit (ZMod p) Input MemoryMsg)
    (selected : RawChannel (ZMod p)) (different : selected ≠ (FinalMemoryValue.channel ram).toRaw) :
    ({ circuit := circuit ram provider } : Component (ZMod p)).operations.interactionsWith selected =
      ({ circuit := provider } : Component (ZMod p)).operations.interactionsWith selected := by
  simp only [Component.interactionsWith_eq, Component.rowOperations, circuit, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

end SP1Clean.FinalMemoryReceipt
