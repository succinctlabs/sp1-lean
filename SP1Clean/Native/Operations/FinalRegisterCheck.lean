import SP1Clean.FormalModel.Contracts.FinalRegisterCheck
import SP1Clean.Native.Operations.FinalMemoryChange
import SP1Clean.Native.Operations.FinalRegisterValue

/-! # Target register validation with selected change coverage

Both subcircuits use the same complete record. Every row consumes its finalizer receipt and
checks its target value, even when it contributes no changed-location key.
-/

namespace SP1Clean.FinalRegisterCheck

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose target validation and coverage on the same final register record. -/
def main (target : MemorySnapshot) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← FinalRegisterValue.circuit target input.record
  let _ ← FinalMemoryChange.circuit false input

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs unit (main target) := by elaborate_circuit

/-- Validate every register receipt, independently of its coverage selector. -/
def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.memory.check.registers.changes"
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input
  ProverAssumptions input data hint :=
    (FinalRegisterValue.circuit target).ProverAssumptions input.record data hint ∧
      FinalMemoryChange.Spec input
  channelsWithRequirements := [(FinalMemoryValue.channel false).toRaw, FinalMemoryChange.channel.toRaw]
  soundness := by
    circuit_proof_start [FinalRegisterValue.circuit, FinalMemoryChange.circuit]
    exact h_holds
  completeness := by
    circuit_proof_start [FinalRegisterValue.circuit, FinalMemoryChange.circuit]
    exact h_assumptions

/-- The two child ledgers are retained with their actual physical offsets. -/
theorem values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) (selected : RawChannel (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith selected env =
      ((FinalRegisterValue.main target input.record).operations offset).interactionValuesWith selected env ++
      ((FinalMemoryChange.main false input).operations
        (offset + (FinalRegisterValue.circuit target).localLength input.record)).interactionValuesWith selected env := by
  simp only [main, Operations.interactionValuesWith, Operations.interactionsWith, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FinalRegisterValue.circuit,
    FinalMemoryChange.circuit, List.filter_append, List.map_append, List.append_nil]

theorem receipt_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel false).toRaw env =
      [(FinalMemoryValue.channel false).pulledValue (eval env input.record)] := by
  rw [values, FinalRegisterValue.receipt_values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalMemoryChange.circuit (p := p) false).base (FinalMemoryValue.channel false).toRaw input
    (offset + (FinalRegisterValue.circuit target).localLength input.record) (by
      simp [FinalMemoryChange.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw])
  simp only [FinalMemoryChange.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.append_nil]

theorem change_values (target : MemorySnapshot) (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith FinalMemoryChange.channel.toRaw env =
      [FinalMemoryChange.channel.pushedIfValue (eval env input.selected)
        (FinalMemoryChange.key false (eval env input.record))] := by
  rw [values, FinalMemoryChange.values]
  have empty := InteractionRecovery.interactionsWith_main_eq_nil
    (FinalRegisterValue.circuit target).base FinalMemoryChange.channel.toRaw input.record offset (by
      simp [FinalRegisterValue.circuit, circuit_norm,
        FinalMemoryValue.channel, FinalMemoryChange.channel, Channel.toRaw,
        FinalRegisterValue.membership, StaticTable.channel])
  simp only [FinalRegisterValue.circuit] at empty
  simp only [Operations.interactionValuesWith, empty, List.map_nil, List.nil_append]

/-- Construction uses only the target validator and the canonical finite change inventory. -/
def populate? (source target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (Inputs (ZMod p)) :=
  (FinalRegisterValue.populate? target record).map fun value =>
    ⟨value, if MemoryMsg.locOf record ∈ source.changes target then 1 else 0⟩

theorem populate?_sound (source target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (input : Inputs (ZMod p)) (found : populate? source target record = some input)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input.record = record := by
  obtain ⟨value, checked, equal⟩ := Option.map_eq_some_iff.mp found
  obtain rfl := equal
  obtain ⟨valid, rfl⟩ := FinalRegisterValue.populate?_sound target record value checked data hint
  refine ⟨⟨valid, ?_⟩, rfl⟩
  change (if MemoryMsg.locOf value ∈ source.changes target then (1 : ZMod p) else 0) = 0 ∨ _
  split <;> simp

end SP1Clean.FinalRegisterCheck
