import SP1Clean.Proofs.Operations.OrdinaryObservation
import SP1Clean.Proofs.Completeness.ProviderWitgen

/-! # Constructing physical ordinary observation rows

The standard Clean table builder uses the same local population and witness IR as the circuit.
Computability is proved here, rather than supplied as a compiler-readiness premise. Clock order
is a semantic input condition for this subsystem; the mixed compiler derives it from execution.
-/

namespace SP1Clean

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The composed word gadgets require only the weaker field bound. -/
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem zeroComputable :
    (Gadgets.IsZeroField.circuit (F := ZMod p)).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [Gadgets.IsZeroField.circuit, circuit_norm, Operations.forAllFlat]
  refine ⟨fun _ h => ?_, fun below h => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm]),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])⟩
  · simp only [h]
  · have same := below.get_eq (by omega : k < 1 + k)
    simp only [circuit_norm, h, same]

namespace ClockOrder

/-- Clock comparison witnesses depend only on the input and previously generated cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.previousHigh h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.previousLow h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.currentHigh h),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _)
      (fun _ h => by simpa [circuit_norm] using congrArg Inputs.currentLow h),
    FlatOperation.forAll_witnessCongr_of_formalSubcircuit _ _ (by omega) zeroComputable
      (fun _ h => ?_),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      (Gadgets.ToBits.rangeCheck_computableWitnesses _ _) (fun below h => ?_)⟩
  · simp only [circuit_norm, Inputs.eval_congr_previousHigh h, Inputs.eval_congr_currentHigh h]
  · have same := below.get_eq (by omega : k + 97 < k + 98)
    simp only [Gadgets.IsZeroField.circuit, Gadgets.ToBits.rangeCheck, circuit_norm, Nat.add_assoc, same,
      Inputs.eval_congr_previousHigh h, Inputs.eval_congr_previousLow h,
      Inputs.eval_congr_currentHigh h, Inputs.eval_congr_currentLow h]

end ClockOrder

namespace OrdinaryObservation

omit [Fact (2 ^ 25 < p)] in
private theorem eval_clock (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.clock = (Eval.eval env input).clock := by
  rcases input with ⟨⟨high, low, pc0, pc1, pc2⟩, ⟨previousHigh, previousLow, counter, pc⟩, nextCounter⟩
  simp only [Inputs.clock, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_counter (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    Eval.eval env input.previous.counter = (Eval.eval env input).previous.counter := by
  rcases input with ⟨receipt, ⟨previousHigh, previousLow, counter, pc⟩, nextCounter⟩
  simp only [circuit_norm]

/-- All private cells are generated honestly by the existing clock and word gadgets. -/
theorem computableWitnesses (enabled : Bool) :
    (circuit (p := p) enabled).base.ComputableWitnessesWithData := by
  intro k input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat]
  refine ⟨FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
      ClockOrder.computableWitnesses (fun h => ?_),
    FlatOperation.forAll_witnessCongr_of_assertionSubcircuit _ _ (by omega)
      WordRangeCheck.computableWitnesses (fun _ h => ?_),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ (by simp [circuit_norm])⟩
  · simp only [CircuitType.eval_expression_prover_to_verifier, eval_clock]
    simpa only [ProvableStruct.eval_eq_eval] using congrArg Inputs.clock h
  · simp only [CircuitType.eval_expression_prover_to_verifier, eval_counter]
    simpa only [ProvableStruct.eval_eq_eval] using congrArg (fun input : Inputs (ZMod p) => input.previous.counter) h

/-- The standard table builder preserves one row per supplied observation input. -/
def construct (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) :=
  Table.build { circuit := circuit enabled } inputs data (ProverHint.empty (ZMod p))

/-- Semantic observation inputs construct all physical constraints without an extra readiness premise. -/
theorem construct_constraints (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ input ∈ inputs, Spec enabled input) : (construct enabled inputs data).Constraints data :=
  Table.build_constraints _ _ _ _ _ (computableWitnesses enabled) valid

/-- Generated rows also supply every local channel guarantee, including all counter Byte checks. -/
theorem construct_guarantees (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ input ∈ inputs, Spec enabled input) : (construct enabled inputs data).Guarantees data :=
  Table.build_guarantees _ _ _ _ _ (computableWitnesses enabled) valid

/-- Physical height is exactly the supplied observation count. -/
theorem construct_length (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) :
    (construct enabled inputs data).length = inputs.length := List.length_map ..

/-- Reading the generated physical rows recovers the exact supplied observation inventory. -/
theorem construct_inputs (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data evaluationData : ProverData (ZMod p)) :
    (construct enabled inputs data).table.map (fun physical =>
      valueFromOffset Inputs 0 (Environment.fromArray physical evaluationData)) = inputs := by
  simp only [construct, Table.build, List.map_map]
  have decode (input : Inputs (ZMod p)) :=
    Component.rowInput_buildRow ({ circuit := circuit enabled } : Component (ZMod p)) input data evaluationData (ProverHint.empty _)
  change inputs.map (fun input => ({ circuit := circuit enabled } : Component (ZMod p)).rowInput
    (Environment.fromArray (({ circuit := circuit enabled } : Component (ZMod p)).buildRow input data (ProverHint.empty _)) evaluationData)) = inputs
  simp only [decode, List.map_id']

/-- Constructed consumers pull precisely the supplied receipt sequence. -/
theorem construct_receipts (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data evaluationData : ProverData (ZMod p)) :
    (construct enabled inputs data).interactionsWith evaluationData InstructionReceipt.channel.toRaw =
      inputs.map (fun input => InstructionReceipt.channel.pulledValue input.receipt) := by
  have decoded := congrArg (List.map fun input => InstructionReceipt.channel.pulledValue input.receipt)
    (construct_inputs enabled inputs data evaluationData)
  simp only [Table.interactionsWith, construct, Table.build, receipt_values]
  rw [← List.map_eq_flatMap]
  simpa only [List.map_map, Function.comp_def, construct, Table.build] using decoded

/-- Constructed observation links preserve each supplied previous/next pair literally. -/
theorem construct_states (enabled : Bool) (inputs : List (Inputs (ZMod p))) (data evaluationData : ProverData (ZMod p)) :
    (construct enabled inputs data).interactionsWith evaluationData stateChannel.toRaw = inputs.flatMap (fun input =>
      [stateChannel.pulledValue input.previous, stateChannel.pushedValue input.next]) := by
  have decoded := congrArg (List.flatMap fun input =>
    [stateChannel.pulledValue input.previous, stateChannel.pushedValue input.next])
    (construct_inputs enabled inputs data evaluationData)
  simpa only [Table.interactionsWith, construct, Table.build, state_values,
    List.flatMap_map] using decoded

end OrdinaryObservation
end SP1Clean
