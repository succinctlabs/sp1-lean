import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.ShiftLeftChip` — honest witness generation (`ComputableWitnesses`)

The first raw op-list chip on the IR: all nine `witnessPrefix` payloads are exportable twins
(`Populate.lean` § Witness IR), each congruence one family `_congr` lemma over the operand
projections (`eval_opBPrev`/`eval_opCPrev`/`eval_immC`) plus the fork's `hint` equation. -/

namespace SP1Clean.ShiftLeftChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- ShiftLeft's row has computable witnesses: every `witnessPrefix` payload is a function of the
input row and the hint alone. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- `a`: the placed result word.
    refine populateAIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
      rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
      exact ((Vector.getElem_map _ (by omega)).symm.trans
        (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `c_bits`.
    refine cBitsIR_congr env env' _ ?_
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `v` powers.
    refine vPowersIR_congr env env' _ ?_
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `shift_u16`.
    refine shiftU16IR_congr env env' _ ?_ h_agree.hint_eq
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `lower_limb`.
    refine lowerLimbIR_congr env env' _ _ (fun i hi => ?_) ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
      rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
      exact ((Vector.getElem_map _ (by omega)).symm.trans
        (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `higher_limb`.
    refine higherLimbIR_congr env env' _ _ (fun i hi => ?_) ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
      rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
      exact ((Vector.getElem_map _ (by omega)).symm.trans
        (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `limb_result`.
    refine limbResultIR_congr env env' _ _ (fun i hi => ?_) ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
      rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
      exact ((Vector.getElem_map _ (by omega)).symm.trans
        (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `sllw_msb`.
    refine sllwMsbIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
      interval_cases i
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[1]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[2]) hv)).trans (Vector.getElem_map _ (by omega))
      · exact ((Vector.getElem_map _ (by omega)).symm.trans
          (congrArg (fun v : Word (ZMod p) => v[3]) hv)).trans (Vector.getElem_map _ (by omega))
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
      rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
      exact ((Vector.getElem_map _ (by omega)).symm.trans
        (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `flags` (incl. `is_sllw · imm_c`).
    refine flagsIR_congr env env' _ ?_ h_agree.hint_eq
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.imm_c) h_input
    rw [eval_immC env.toEnvironment input, eval_immC env'.toEnvironment input] at hv
    exact hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.ShiftLeftChip
