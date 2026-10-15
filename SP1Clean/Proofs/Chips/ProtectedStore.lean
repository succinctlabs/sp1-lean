import SP1Clean.Proofs.Chips.StoreByteChip.Formal
import SP1Clean.Proofs.Chips.StoreHalfChip.Formal
import SP1Clean.Proofs.Chips.StoreWordChip.Formal
import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
import SP1Clean.FormalModel.Contracts.WritePermission
import Clean.Circuit.Loops
import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection

/-! # Native store rows with byte-permission requests

Each wrapper composes the original whole chip and requests permission for its actual byte
footprint. The output, witness cells, arithmetic constraints, and existing channels are retained.
Permission is derived globally from the fixed provider and balance; the instruction contract has
no extra semantic assumption. The Rust-faithfulness anchors continue to describe the original chips.
-/

namespace SP1Clean.ProtectedStore

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def byte : GeneralFormalCircuit (ZMod p) StoreByteChip.Inputs StoreByteChip.Columns where
  name := (StoreByteChip.circuit (p := p)).name
  main input := do
    let output ← StoreByteChip.circuit input
    WritePermissionProvider.channel.pullIf input.is_real output.address_operation.addr_operation.value
    return output
  Assumptions := StoreByteChip.Assumptions
  Spec := StoreByteChip.Spec
  ProverAssumptions := StoreByteChip.ProverAssumptions
  channelsWithRequirements := StoreByteChip.circuit.channelsWithRequirements
  soundness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreByteChip.circuit]
    exact ⟨h_holds h_assumptions, h_assumptions⟩
  completeness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreByteChip.circuit]
    exact h_assumptions

def half : GeneralFormalCircuit (ZMod p) StoreHalfChip.Inputs StoreHalfChip.Columns where
  name := (StoreHalfChip.circuit (p := p)).name
  main input := do
    let output ← StoreHalfChip.circuit input
    Circuit.forEach (Vector.range 2) fun index => do
      WritePermissionProvider.channel.pullIf input.is_real
        (Address.offset output.address_operation.addr_operation.value (.const (index : ZMod p)))
    return output
  Assumptions := StoreHalfChip.Assumptions
  Spec := StoreHalfChip.Spec
  ProverAssumptions := StoreHalfChip.ProverAssumptions
  channelsWithRequirements := StoreHalfChip.circuit.channelsWithRequirements
  soundness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreHalfChip.circuit]
    exact ⟨h_holds h_assumptions, h_assumptions⟩
  completeness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreHalfChip.circuit]
    exact h_assumptions

def word : GeneralFormalCircuit (ZMod p) StoreWordChip.Inputs StoreWordChip.Columns where
  name := (StoreWordChip.circuit (p := p)).name
  main input := do
    let output ← StoreWordChip.circuit input
    Circuit.forEach (Vector.range 4) fun index => do
      WritePermissionProvider.channel.pullIf input.is_real
        (Address.offset output.address_operation.addr_operation.value (.const (index : ZMod p)))
    return output
  Assumptions := StoreWordChip.Assumptions
  Spec := StoreWordChip.Spec
  ProverAssumptions := StoreWordChip.ProverAssumptions
  channelsWithRequirements := StoreWordChip.circuit.channelsWithRequirements
  soundness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreWordChip.circuit]
    exact ⟨h_holds h_assumptions, h_assumptions⟩
  completeness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreWordChip.circuit]
    exact h_assumptions

def double : GeneralFormalCircuit (ZMod p) StoreDoubleChip.Inputs StoreDoubleChip.Columns where
  name := (StoreDoubleChip.circuit (p := p)).name
  main input := do
    let output ← StoreDoubleChip.circuit input
    Circuit.forEach (Vector.range 8) fun index => do
      WritePermissionProvider.channel.pullIf input.is_real
        (Address.offset output.address_operation.addr_operation.value (.const (index : ZMod p)))
    return output
  Assumptions := StoreDoubleChip.Assumptions
  Spec := StoreDoubleChip.Spec
  ProverAssumptions := StoreDoubleChip.ProverAssumptions
  channelsWithRequirements := StoreDoubleChip.circuit.channelsWithRequirements
  soundness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreDoubleChip.circuit]
    exact ⟨h_holds h_assumptions, h_assumptions⟩
  completeness := by
    circuit_proof_start [WritePermissionProvider.channel, StoreDoubleChip.circuit]
    exact h_assumptions

/-- The permission requests preserve the original physical row width. -/
theorem byte_width :
    ({ circuit := byte (p := p) } : Air.Flat.Component (ZMod p)).width =
      ({ circuit := StoreByteChip.circuit } : Air.Flat.Component (ZMod p)).width := rfl

/-- All original assertions remain byte-for-byte unchanged. -/
theorem byte_constraints :
    ({ circuit := byte (p := p) } : Air.Flat.Component (ZMod p)).operations.constraints =
      ({ circuit := StoreByteChip.circuit } : Air.Flat.Component (ZMod p)).operations.constraints := by
  simp only [Air.Flat.Component.constraints_eq, Air.Flat.Component.rowOperations, byte, circuit_norm]

/-- The extension introduces no additional fixed lookup. -/
theorem byte_lookups :
    ({ circuit := byte (p := p) } : Air.Flat.Component (ZMod p)).operations.lookups =
      ({ circuit := StoreByteChip.circuit } : Air.Flat.Component (ZMod p)).operations.lookups := by
  simp only [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations, byte, circuit_norm]

/-- Every pre-existing interaction ledger is preserved by the store extension. -/
theorem byte_interactions (selected : RawChannel (ZMod p))
    (different : selected ≠ WritePermissionProvider.channel.toRaw) :
    ({ circuit := byte (p := p) } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected =
      ({ circuit := StoreByteChip.circuit } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected := by
  simp only [Air.Flat.Component.interactionsWith_eq, Air.Flat.Component.rowOperations, byte, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions]
  simp only [Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

/-- The permission requests preserve the original physical row width. -/
theorem half_width :
    ({ circuit := half (p := p) } : Air.Flat.Component (ZMod p)).width =
      ({ circuit := StoreHalfChip.circuit } : Air.Flat.Component (ZMod p)).width := rfl

/-- All original assertions remain byte-for-byte unchanged. -/
theorem half_constraints :
    ({ circuit := half (p := p) } : Air.Flat.Component (ZMod p)).operations.constraints =
      ({ circuit := StoreHalfChip.circuit } : Air.Flat.Component (ZMod p)).operations.constraints := by
  simp only [Air.Flat.Component.constraints_eq, Air.Flat.Component.rowOperations, half, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The extension introduces no additional fixed lookup. -/
theorem half_lookups :
    ({ circuit := half (p := p) } : Air.Flat.Component (ZMod p)).operations.lookups =
      ({ circuit := StoreHalfChip.circuit } : Air.Flat.Component (ZMod p)).operations.lookups := by
  simp only [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations, half, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Every pre-existing interaction ledger is preserved by the store extension. -/
theorem half_interactions (selected : RawChannel (ZMod p))
    (different : selected ≠ WritePermissionProvider.channel.toRaw) :
    ({ circuit := half (p := p) } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected =
      ({ circuit := StoreHalfChip.circuit } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected := by
  simp only [Air.Flat.Component.interactionsWith_eq, Air.Flat.Component.rowOperations, half, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  simp only [Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

/-- The permission requests preserve the original physical row width. -/
theorem word_width :
    ({ circuit := word (p := p) } : Air.Flat.Component (ZMod p)).width =
      ({ circuit := StoreWordChip.circuit } : Air.Flat.Component (ZMod p)).width := rfl

/-- All original assertions remain byte-for-byte unchanged. -/
theorem word_constraints :
    ({ circuit := word (p := p) } : Air.Flat.Component (ZMod p)).operations.constraints =
      ({ circuit := StoreWordChip.circuit } : Air.Flat.Component (ZMod p)).operations.constraints := by
  simp only [Air.Flat.Component.constraints_eq, Air.Flat.Component.rowOperations, word, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The extension introduces no additional fixed lookup. -/
theorem word_lookups :
    ({ circuit := word (p := p) } : Air.Flat.Component (ZMod p)).operations.lookups =
      ({ circuit := StoreWordChip.circuit } : Air.Flat.Component (ZMod p)).operations.lookups := by
  simp only [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations, word, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Every pre-existing interaction ledger is preserved by the store extension. -/
theorem word_interactions (selected : RawChannel (ZMod p))
    (different : selected ≠ WritePermissionProvider.channel.toRaw) :
    ({ circuit := word (p := p) } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected =
      ({ circuit := StoreWordChip.circuit } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected := by
  simp only [Air.Flat.Component.interactionsWith_eq, Air.Flat.Component.rowOperations, word, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  simp only [Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

/-- The permission requests preserve the original physical row width. -/
theorem double_width :
    ({ circuit := double (p := p) } : Air.Flat.Component (ZMod p)).width =
      ({ circuit := StoreDoubleChip.circuit } : Air.Flat.Component (ZMod p)).width := rfl

/-- All original assertions remain byte-for-byte unchanged. -/
theorem double_constraints :
    ({ circuit := double (p := p) } : Air.Flat.Component (ZMod p)).operations.constraints =
      ({ circuit := StoreDoubleChip.circuit } : Air.Flat.Component (ZMod p)).operations.constraints := by
  simp only [Air.Flat.Component.constraints_eq, Air.Flat.Component.rowOperations, double, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The extension introduces no additional fixed lookup. -/
theorem double_lookups :
    ({ circuit := double (p := p) } : Air.Flat.Component (ZMod p)).operations.lookups =
      ({ circuit := StoreDoubleChip.circuit } : Air.Flat.Component (ZMod p)).operations.lookups := by
  simp only [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations, double, circuit_norm,
    Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Every pre-existing interaction ledger is preserved by the store extension. -/
theorem double_interactions (selected : RawChannel (ZMod p))
    (different : selected ≠ WritePermissionProvider.channel.toRaw) :
    ({ circuit := double (p := p) } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected =
      ({ circuit := StoreDoubleChip.circuit } : Air.Flat.Component (ZMod p)).operations.interactionsWith selected := by
  simp only [Air.Flat.Component.interactionsWith_eq, Air.Flat.Component.rowOperations, double, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, Circuit.forEach.operations_eq,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  simp only [Ne.symm different, ↓reduceIte, List.append_nil]
  rfl

end SP1Clean.ProtectedStore
