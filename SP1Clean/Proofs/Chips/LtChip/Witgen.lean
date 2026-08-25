import SP1Clean.Proofs.Chips.LtChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.LtChip` — honest witness generation (`ComputableWitnesses`)

The second hint-driven chip on the exportable IR (the `BitwiseChip/Witgen.lean` pattern): the
flag cells' congruence is one `hint` projection, and the `LtOperationSigned` payload is
`populateFE_congr_flat` from the operand projections, the `is_slt` flag cell below it
(`AgreesBelow.get_eq`), and the `is_real` input. -/

namespace SP1Clean.LtChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Lt's row has computable witnesses: the two flag cells are functions of the hint alone, and the
ten `LtOperationSigned` cells are functions of the input row plus the `is_slt` cell below them. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree _ => ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- The two flag cells: the payload reads the environment only through `hint`.
    exact hintFlagsIR_congr env env' h_agree.hint_eq _ _
  · -- The ten gadget cells: operand projections, the `is_slt` cell below, the `is_real` input.
    refine LtOperationSigned.populateFE_congr_flat env env' _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · -- `is_slt` is the flag cell below the payload (the Jalr same-row lesson).
      simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
    · -- `is_real` is an input column.
      have hv := congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
      rw [← ProvableStruct.eval_eq_eval, ← ProvableStruct.eval_eq_eval] at hv
      simpa only [eval_inputIsReal] using hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.LtChip
