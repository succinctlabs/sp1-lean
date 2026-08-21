import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
import SP1Clean.Proofs.Operations.AddressOperation.Witgen
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.StoreDoubleChip` — honest witness generation (`ComputableWitnesses`)

SD on the witgen bridge (see `StoreWordChip/Witgen.lean` for the store family's shape). The
simplest row of the family: no sub-word merge and no `store_value` column — the word written is the
`rs2` read value itself — so the only witnessed cells are the four the composed `AddressOperation`
produces, and the offset bits it is passed are all literal zero (SD is 8-byte aligned). -/

namespace SP1Clean.StoreDoubleChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Operand words, in `circuit_norm`'s own orientation -/

/-- The rs1 base-address word, evaluated. -/
theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.evalITypeColumns,
    Readers.evalRegisterAccessColumns]
  exact ProvableType.eval_fields env _

/-- The sign-extended offset immediate, evaluated. -/
theorem eval_opCImm {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_imm
      = Vector.map (Expression.eval env) input.op_c_imm := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_imm, eval_inputs, Readers.evalITypeColumns]
  exact ProvableType.eval_fields env _

/-- StoreDouble's row has computable witnesses: the four address cells come from the composed
`AddressOperation`, whose input row is a function of this row's own input cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
      AddressOperation.computableWitnesses (fun h_input => ?_),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · simp only [circuit_norm]
    refine ⟨?_, ?_, ?_⟩
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa only [eval_opBVal] using hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_imm) h_input
      simpa only [eval_opCImm] using hv
    · exact congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
  all_goals simp [circuit_norm]

end SP1Clean.StoreDoubleChip
