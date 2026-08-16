import SP1Clean.Proofs.Chips.MulChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.MulChip` — honest witness generation (`ComputableWitnesses`)

The largest witness surface of the cutover: the five variant flags (a pure `hint` read), the
45-cell `MulOperation` schoolbook struct (operand projections plus the three signed-variant flag
cells below it — `populateFE_congr_flat` walks the whole carry-chain tower), and the four-cell
result word `a` (the first `.ofExprs` site: a pure same-row read of the flags, product bytes, and
product MSB, closed cell-by-cell from `AgreesBelow.get_eq`). -/

namespace SP1Clean.MulChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Mul's row has computable witnesses: the flag cells are functions of the hint alone, the
`MulOperation` cells of the input row plus the flag cells below them, and the result word of
earlier same-row cells alone. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree _ => ?_,
    fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    fun h_agree _ => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- The five flag cells: the payload reads the environment only through `hint`.
    exact hintFlagsIR_congr env env' h_agree.hint_eq _ _
  · -- The 45 `MulOperation` cells: operand projections from the struct-level input agreement,
    -- the three signed-variant flags from the earlier cells of the same row.
    refine MulOperation.populateFE_congr_flat env env' _ _ _ _ _
      (fun i hi => ?_) (fun i hi => ?_) ?_ ?_ ?_
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simp only [eval_opBVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_val) h_input
      simp only [eval_opCVal] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
    · simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
    · simp only [circuit_norm]
      exact h_agree.get_eq (by omega)
  · simp [circuit_norm]
  · -- The four result cells: flag selectors, product bytes, and the product MSB — all earlier
    -- cells of the same row.
    apply Vector.ext
    intro i hi
    simp only [Witgen.WitgenIR.getElem_eval_ofExprs]
    interval_cases i
    · simp only [circuit_norm]
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · simp only [circuit_norm]
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega)]
    · simp only [circuit_norm]
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega)]
    · simp only [circuit_norm]
      rw [h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega), h_agree.get_eq (by omega), h_agree.get_eq (by omega),
        h_agree.get_eq (by omega)]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.MulChip
