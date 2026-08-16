import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.ShiftRightChip` — honest witness generation (`ComputableWitnesses`)

The largest raw op-list chip: all eleven `witnessPrefix` payloads are exportable twins
(`Populate.lean` § Witness IR), each congruence one family `_congr` lemma over the operand
projections plus the fork's `hint` equation (`cBits` reuses `ShiftLeftChip.cBitsIR_congr`). -/

namespace SP1Clean.ShiftRightChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- ShiftRight's row has computable witnesses: every `witnessPrefix` payload is a function of the
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
  · -- `b_msb`.
    refine bMsbIR_congr env env' _ (fun i hi => ?_) h_agree.hint_eq
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
  · -- `srw_msb`.
    refine srwMsbIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
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
  · -- `c_bits` (the shared `ShiftLeftChip` twin).
    refine ShiftLeftChip.cBitsIR_congr env env' _ ?_
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `sra_msb_v0123`.
    refine sraMsbV0123IR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
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
  · -- `v` inverted powers.
    refine vPowersInvIR_congr env env' _ ?_
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `lower_limb`.
    refine lowerLimbIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
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
    refine higherLimbIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
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
    refine limbResultIR_congr env env' _ _ (fun i hi => ?_) ?_ h_agree.hint_eq
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
  · -- `shift_u16`.
    refine shiftU16IR_congr env env' _ ?_ h_agree.hint_eq
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    exact ((Vector.getElem_map _ (by omega)).symm.trans
      (congrArg (fun v : Word (ZMod p) => v[0]) hv)).trans (Vector.getElem_map _ (by omega))
  · -- `flags` (incl. `(is_srlw + is_sraw) · imm_c`).
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
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.ShiftRightChip
