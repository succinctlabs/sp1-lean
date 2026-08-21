import SP1Clean.Proofs.Chips.StoreByteChip.Formal
import SP1Clean.Proofs.Operations.AddressOperation.Witgen
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.StoreByteChip` — honest witness generation (`ComputableWitnesses`)

SB on the witgen bridge (see `StoreWordChip/Witgen.lean` for the store family's shape). The widest
row of the family — three offset bits, the old limb and its low byte, the register's low byte, the
signed increment and the merged word are all committed input columns — and therefore still a row
whose *only* witnessed cells are the four the composed `AddressOperation` produces. The two inline
byte-bus pulls and the nine gates witness nothing. -/

namespace SP1Clean.StoreByteChip

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

/-- The three committed offset bits, evaluated. -/
theorem eval_offsetBit {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).offset_bit
      = Vector.map (Expression.eval env) input.offset_bit := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs]
  exact ProvableType.eval_fields env _

/-- StoreByte's row has computable witnesses: the four address cells come from the composed
`AddressOperation`, whose input row is a function of this row's own input cells. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_generalSubcircuit _ _ _
      AddressOperation.computableWitnesses (fun h_input => ?_),
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
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
  · have hob := congrArg (fun r : Inputs (ZMod p) => r.offset_bit) h_input
    simp only [eval_offsetBit] at hob
    simp only [circuit_norm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa only [eval_opBVal] using hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_imm) h_input
      simpa only [eval_opCImm] using hv
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[0]) hob
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[1]) hob
    · simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[2]) hob
    · exact congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
  all_goals simp [circuit_norm]

end SP1Clean.StoreByteChip
