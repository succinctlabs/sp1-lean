import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable Bitwise witnesses

The sixteen byte columns depend only on the operand and selector inputs. Witness generation
uses Clean's existing IR and does not read external hints or earlier witness cells.
-/

namespace SP1Clean.BitwiseChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Input agreement determines all sixteen byte witnesses. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun _h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · refine BitwiseU16Operation.populateFE_congr_flat env env' _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hx := congrArg (fun r : Inputs (ZMod p) => r.isXor) h_input
      have ho := congrArg (fun r : Inputs (ZMod p) => r.isOr) h_input
      have ha := congrArg (fun r : Inputs (ZMod p) => r.isAnd) h_input
      simp only [Inputs.eval_isXor, Inputs.eval_isOr, Inputs.eval_isAnd,
        ProvableType.eval_field] at hx ho ha
      simp only [circuit_norm, hx, ho, ha]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.BitwiseChip
