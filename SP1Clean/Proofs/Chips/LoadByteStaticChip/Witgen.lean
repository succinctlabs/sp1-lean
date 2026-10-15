import SP1Clean.Proofs.Chips.LoadByteStaticChip.Formal
import SP1Clean.Proofs.Chips.LoadByteChip.Witgen
import ToClean.Air.TableBuild

/-! # The unchanged executable witness of the fixed-byte LoadByte alternative -/

namespace SP1Clean.LoadByteStaticChip

open Circuit
open LoadByteChip (Inputs Columns eval_opBVal eval_opCImm)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- LoadByte's row has computable witnesses: the four address cells come from the composed
`AddressOperation`, whose input row is a function of this row's own input cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
      AddressOperation.computableWitnesses (fun h_input => ?_),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · have hob := Inputs.eval_congr_offset_bit h_input
    simp only [circuit_norm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa only [eval_opBVal] using hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_imm) h_input
      simpa only [eval_opCImm] using hv
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[0]) hob
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[1]) hob
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[2]) hob
    · rw [Inputs.eval_congr_is_lb h_input,
        Inputs.eval_congr_is_lbu h_input]
  all_goals simp [circuit_norm]


/-- The replacement allocates no cells and preserves every input and generated witness cell. -/
theorem witgen_eq_original (input : Var Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (init : Array (ZMod p)) :
    (main input).witgenWithData data hint init =
      (LoadByteChip.main input).witgenWithData data hint init := by
  simp only [Circuit.witgenWithData, main, LoadByteChip.main, circuit_norm,
    FlatOperation.witgenWithData, List.foldl_append, List.foldl_cons,
    FlatOperation.witgenStepWithData]

/-- The alternative component is separate from the unchanged production registry. -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Every built cell is unchanged, for arbitrary inputs (including inactive rows). -/
theorem buildRow_eq_original (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    component.buildRow input data hint =
      Air.Flat.Component.buildRow { circuit := LoadByteChip.circuit } input data hint :=
  witgen_eq_original _ _ _ _

end SP1Clean.LoadByteStaticChip
