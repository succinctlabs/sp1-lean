import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable shift-right witnesses

All 33 witness cells depend only on operand, instruction-selector, and immediate inputs.
The generators and their evaluation laws use Clean's witness IR.
-/

namespace SP1Clean.ShiftRightChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem inputAgreement {input : Var Inputs (ZMod p)}
    {env env' : ProverEnvironment (ZMod p)}
    (h : ProvableStruct.eval env.toEnvironment input = ProvableStruct.eval env'.toEnvironment input) :
    (∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment input.adapter.op_b_memory.prev_value[i] =
        Expression.eval env'.toEnvironment input.adapter.op_b_memory.prev_value[i]) ∧
    Expression.eval env.toEnvironment input.adapter.op_c_memory.prev_value[0] =
      Expression.eval env'.toEnvironment input.adapter.op_c_memory.prev_value[0] ∧
    (∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment (#v[input.isSrl, input.isSra, input.isSrlw, input.isSraw])[i] =
        Expression.eval env'.toEnvironment (#v[input.isSrl, input.isSra, input.isSrlw, input.isSraw])[i]) ∧
    Expression.eval env.toEnvironment input.adapter.imm_c =
      Expression.eval env'.toEnvironment input.adapter.imm_c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h
    change (ProvableStruct.eval env.toEnvironment input).adapter.op_b_memory.prev_value =
      (ProvableStruct.eval env'.toEnvironment input).adapter.op_b_memory.prev_value at hv
    rw [eval_opBPrev, eval_opBPrev] at hv
    simpa only [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h
    change (ProvableStruct.eval env.toEnvironment input).adapter.op_c_memory.prev_value =
      (ProvableStruct.eval env'.toEnvironment input).adapter.op_c_memory.prev_value at hv
    rw [eval_opCPrev, eval_opCPrev] at hv
    simpa only [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[0]) hv
  · intro i hi
    interval_cases i
    · exact Inputs.eval_congr_isSrl h
    · exact Inputs.eval_congr_isSra h
    · exact Inputs.eval_congr_isSrlw h
    · exact Inputs.eval_congr_isSraw h
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.imm_c) h
    simpa only [eval_immC] using hv

/-- Input agreement determines every shift witness, independently of prover hints. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_,
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
  · have h := inputAgreement h_input
    exact populateAIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact bMsbIR_congr env env' _ _ h.1 h.2.2.1
  · have h := inputAgreement h_input
    exact srwMsbIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact ShiftLeftChip.cBitsIR_congr env env' _ h.2.1
  · have h := inputAgreement h_input
    exact sraMsbV0123IR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact vPowersInvIR_congr env env' _ h.2.1
  · have h := inputAgreement h_input
    exact lowerLimbIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact higherLimbIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact limbResultIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact shiftU16IR_congr env env' _ _ h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact wordImmIR_congr env env' _ _ h.2.2.2 h.2.2.1
  all_goals simp [circuit_norm]

end SP1Clean.ShiftRightChip
