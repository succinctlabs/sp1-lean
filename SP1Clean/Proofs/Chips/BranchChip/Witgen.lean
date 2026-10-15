import SP1Clean.Proofs.Chips.BranchChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable branch witnesses

Clean generates the comparison from the operands and selectors, then the branch decision,
then the selected next PC. Every same-row read uses an earlier witness cell.
-/

namespace SP1Clean.BranchChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Branch's row has computable witnesses. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
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
  · -- Comparison certificate from ordinary inputs.
    refine LtOperationSigned.populateFE_congr_flat env env' _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · have hv : (ProvableStruct.eval env.toEnvironment input).adapter.op_a_memory.prev_value
          = (ProvableStruct.eval env'.toEnvironment input).adapter.op_a_memory.prev_value :=
        congrArg (fun r : Inputs (ZMod p) => r.adapter.op_a_memory.prev_value) h_input
      rw [eval_rs1In env.toEnvironment input, eval_rs1In env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv : (ProvableStruct.eval env.toEnvironment input).adapter.op_b_memory.prev_value
          = (ProvableStruct.eval env'.toEnvironment input).adapter.op_b_memory.prev_value :=
        congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_rs2In env.toEnvironment input, eval_rs2In env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · simp only [circuit_norm]
      rw [Inputs.eval_congr_isBlt h_input, Inputs.eval_congr_isBge h_input]
    · simpa only [eval_isReal] using congrArg Inputs.is_real h_input
  · -- Decision from selectors and the comparison cells already written.
    simp only [branchDecision, circuit_norm]
    rw [Inputs.eval_congr_isBeq h_input, Inputs.eval_congr_isBne h_input,
      Inputs.eval_congr_isBlt h_input, Inputs.eval_congr_isBge h_input,
      Inputs.eval_congr_isBltu h_input, Inputs.eval_congr_isBgeu h_input,
      h_agree.get_eq (i := n) (by omega),
      h_agree.get_eq (i := n + 1) (by omega),
      h_agree.get_eq (i := n + 1 + 1) (by omega),
      h_agree.get_eq (i := n + 1 + 2) (by omega),
      h_agree.get_eq (i := n + 1 + 3) (by omega)]
  · -- The three `next_pc` cells: pc/imm inputs, the `is_branching` cell below, `is_real`.
    refine nextPcIR_congr env env' _ _ _ _ (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · have hv : (ProvableStruct.eval env.toEnvironment input).state.pc
          = (ProvableStruct.eval env'.toEnvironment input).state.pc :=
        congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      rw [eval_statePcIn env.toEnvironment input, eval_statePcIn env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Vector (ZMod p) 3 => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Vector (ZMod p) 3 => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Vector (ZMod p) 3 => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv : (ProvableStruct.eval env.toEnvironment input).adapter.op_c_imm
          = (ProvableStruct.eval env'.toEnvironment input).adapter.op_c_imm :=
        congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_imm) h_input
      rw [eval_opCImmIn env.toEnvironment input, eval_opCImmIn env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
    · simpa only [eval_isReal] using congrArg Inputs.is_real h_input
  all_goals simp [circuit_norm]

end SP1Clean.BranchChip
