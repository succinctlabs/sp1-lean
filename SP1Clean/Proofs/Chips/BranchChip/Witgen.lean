import SP1Clean.Proofs.Chips.BranchChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.BranchChip` — honest witness generation (`ComputableWitnesses`)

The largest hint surface so far: six opcode flags plus the single-cell `is_branching` decision
(both pure `hint` reads), the `next_pc` blend (inputs plus the `is_branching` cell below it), and
the `LtOperationSigned` block (inputs plus the two comparison flag cells). Every same-row read is
`AgreesBelow.get_eq`; every hint read closes from the fork's `hint` component. Branch has **no
trace anchor**, so `ComputableWitnesses` + the rewired completeness are the conversion's checks —
the idioms are the ones the anchored Bitwise/Lt pilots proved out. -/

namespace SP1Clean.BranchChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Branch's row has computable witnesses. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun h_agree _ => ?_,
    fun h_agree _ => ?_,
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
  · -- The six flag cells: hint only.
    exact hintFlagsIR_congr env env' h_agree.hint_eq _ _
  · -- The `is_branching` cell: hint only.
    simp [circuit_norm, h_agree.hint_eq]
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
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
      rw [← ProvableStruct.eval_eq_eval, ← ProvableStruct.eval_eq_eval] at hv
      simpa only [eval_inputIsReal] using hv
  · -- The ten `LtOperationSigned` cells: rs1/rs2 inputs, the two comparison flag cells, `is_real`.
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
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
      rw [← ProvableStruct.eval_eq_eval, ← ProvableStruct.eval_eq_eval] at hv
      simpa only [eval_inputIsReal] using hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.BranchChip
