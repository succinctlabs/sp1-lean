import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.BitwiseChip` — honest witness generation (`ComputableWitnesses`)

The W4 **pilot**: the first chip whose witnesses read the `ProverHint` through the exportable
`FExpr.hintGet` (via `hintFlagsIR`) rather than a Lean closure. Provable exactly because the
pinned Clean revision's `AgreesBelow` carries `hint`: the flag cells' congruence is one `hint`
projection (`hintFlags_eval_ir` under both environments), and the column-struct payload is
`populateFE_congr` from the operand projections plus the three *earlier flag cells of the same
row* (`AgreesBelow.get_eq` — the Jalr lesson: a witness legitimately reading its own row's
earlier cells). -/

namespace SP1Clean.BitwiseChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bitwise's row has computable witnesses: the three flag cells are functions of the hint alone,
and the sixteen `BitwiseU16Operation` cells are functions of the input row plus the flag cells
below them. -/
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- The three flag cells: the payload reads the environment only through `hint`, which
    -- `AgreesBelow` identifies.
    exact hintFlagsIR_congr env env' h_agree.hint_eq _ _
  · -- The sixteen gadget cells: operand projections from the struct-level input agreement
    -- (`eval_opBVal`/`eval_opCVal`), the opcode from the three earlier flag cells.
    refine BitwiseU16Operation.populateFE_congr_flat env env' _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · simp only [circuit_norm]
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.BitwiseChip
