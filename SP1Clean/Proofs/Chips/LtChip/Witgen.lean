import SP1Clean.Proofs.Chips.LtChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # Computable less-than witnesses

The ten comparison columns depend only on the operand and selector inputs. Witness generation
uses Clean's existing IR and does not read external hints or earlier witness cells.
-/

namespace SP1Clean.LtChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Input agreement determines all ten comparison witnesses. -/
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · refine LtOperationSigned.populateFE_congr_flat env env' _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simpa [circuit_norm, Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · exact Inputs.eval_congr_isSlt h_input
    · have hs := Inputs.eval_congr_isSlt h_input
      have hu := Inputs.eval_congr_isSltu h_input
      simp only [circuit_norm, hs, hu]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.LtChip
