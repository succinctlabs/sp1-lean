import SP1Clean.Proofs.Chips.MulChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable multiplication witnesses

The 45-cell arithmetic witness depends on the operands and selectors in the input row. The
four result limbs additionally read the earlier product cells. No external hint is required.
-/

namespace SP1Clean.MulChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Input agreement and earlier-cell agreement determine every multiplication witness. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree h_input => ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · refine MulOperation.populateFE_congr_flat env env' _ _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · simpa only [Inputs.eval_isMulh, ProvableType.eval_field] using congrArg (fun r : Inputs (ZMod p) => r.isMulh) h_input
    · simpa only [Inputs.eval_isMulhsu, ProvableType.eval_field] using congrArg (fun r : Inputs (ZMod p) => r.isMulhsu) h_input
    · simpa only [Inputs.eval_isMulw, ProvableType.eval_field] using congrArg (fun r : Inputs (ZMod p) => r.isMulw) h_input
  · have hm := congrArg (fun r : Inputs (ZMod p) => r.isMul) h_input
    have hh := congrArg (fun r : Inputs (ZMod p) => r.isMulh) h_input
    have hu := congrArg (fun r : Inputs (ZMod p) => r.isMulhu) h_input
    have hs := congrArg (fun r : Inputs (ZMod p) => r.isMulhsu) h_input
    have hw := congrArg (fun r : Inputs (ZMod p) => r.isMulw) h_input
    simp only [Inputs.eval_isMul, Inputs.eval_isMulh, Inputs.eval_isMulhu,
      Inputs.eval_isMulhsu, Inputs.eval_isMulw, ProvableType.eval_field] at hm hh hu hs hw
    apply Vector.ext
    intro i hi
    simp only [Witgen.WitgenIR.getElem_eval_ofExprs]
    interval_cases i <;> simp only [circuit_norm, hm, hh, hu, hs, hw]
    · rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.MulChip
