import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable shift-left witnesses

All 31 witness cells depend only on the operand, instruction-selector, and immediate inputs.
The generators and their evaluation laws use Clean's witness IR.
-/

namespace SP1Clean.ShiftLeftChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem inputAgreement {input : Var Inputs (ZMod p)}
    {env env' : ProverEnvironment (ZMod p)}
    (h : ProvableStruct.eval env.toEnvironment input = ProvableStruct.eval env'.toEnvironment input) :
    (∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment input.op_b_val[i] =
        Expression.eval env'.toEnvironment input.op_b_val[i]) ∧
    Expression.eval env.toEnvironment input.op_c_val[0] =
      Expression.eval env'.toEnvironment input.op_c_val[0] ∧
    (∀ (i : ℕ) (_ : i < 2),
      Expression.eval env.toEnvironment (#v[input.isSll, input.isSllw])[i] =
        Expression.eval env'.toEnvironment (#v[input.isSll, input.isSllw])[i]) ∧
    Expression.eval env.toEnvironment input.isSllw =
      Expression.eval env'.toEnvironment input.isSllw ∧
    Expression.eval env.toEnvironment input.adapter.imm_c =
      Expression.eval env'.toEnvironment input.adapter.imm_c := by
  refine ⟨?_, ?_, ?_, Inputs.eval_congr_isSllw h, ?_⟩
  · intro i hi
    have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h
    change (ProvableStruct.eval env.toEnvironment input).adapter.op_b_memory.prev_value =
      (ProvableStruct.eval env'.toEnvironment input).adapter.op_b_memory.prev_value at hv
    rw [eval_opBPrev, eval_opBPrev] at hv
    simpa only [Inputs.op_b_val, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h
    change (ProvableStruct.eval env.toEnvironment input).adapter.op_c_memory.prev_value =
      (ProvableStruct.eval env'.toEnvironment input).adapter.op_c_memory.prev_value at hv
    rw [eval_opCPrev, eval_opCPrev] at hv
    simpa only [Inputs.op_c_val, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[0]) hv
  · intro i hi
    interval_cases i
    · exact Inputs.eval_congr_isSll h
    · exact Inputs.eval_congr_isSllw h
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · have h := inputAgreement h_input
    exact populateAIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · exact cBitsIR_congr env env' _ (inputAgreement h_input).2.1
  · exact vPowersIR_congr env env' _ (inputAgreement h_input).2.1
  · have h := inputAgreement h_input
    exact shiftU16IR_congr env env' _ _ h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact lowerLimbIR_congr env env' _ _ h.1 h.2.1
  · have h := inputAgreement h_input
    exact higherLimbIR_congr env env' _ _ h.1 h.2.1
  · have h := inputAgreement h_input
    exact limbResultIR_congr env env' _ _ h.1 h.2.1
  · have h := inputAgreement h_input
    exact sllwMsbIR_congr env env' _ _ _ h.1 h.2.1 h.2.2.1
  · have h := inputAgreement h_input
    exact sllwImmIR_congr env env' _ _ h.2.2.2.1 h.2.2.2.2
  all_goals simp [circuit_norm]

end SP1Clean.ShiftLeftChip
