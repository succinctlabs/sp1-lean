import SP1Clean.Proofs.Chips.SubwChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.SubwChip` — honest witness generation (`ComputableWitnesses`)

Subw on the witgen bridge (see `AddChip/Witgen.lean` for the programme note). Same two-payload shape
as Addw — the W-result's two low limbs (`valueIR`) and its sign bit (`msbIR`) — and, since Subw's
adapter is the R-type reader rather than the ALU-type one, the operand lemmas it projects through are
Sub's rather than Addw's. -/

namespace SP1Clean.SubwChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Addw's row has computable witnesses: every witnessed cell is a function of the input row alone. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun _ h_input => ?_,
    fun _ h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · refine SubwOperation.valueIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · refine SubwOperation.msbIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.SubwChip
