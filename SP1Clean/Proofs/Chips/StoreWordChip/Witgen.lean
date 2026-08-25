import SP1Clean.Proofs.Chips.StoreWordChip.Formal
import SP1Clean.Proofs.Operations.AddressOperation.Witgen
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.StoreWordChip` — honest witness generation (`ComputableWitnesses`)

SW on the witgen bridge (see `AddChip/Witgen.lean` for the programme note and
`LoadWordChip/Witgen.lean` for the memory family's shape). A store's row commits everything the AIR
reads except the address: the `offset_bit` and the read-modify-write word `store_value` are
committed input columns, so the only witnessed cells in the row are the four the composed
`AddressOperation` sub-circuit produces (three address limbs plus the reserved-page inverse).

The child's own honest-witness theorem (`AddressOperation.computableWitnesses`) discharges those
four, and `FlatOperation.forAll_witnessCongr_of_generalSubcircuit` composes it; all the parent owes
is that the child's input row is assembled from the parent's. Every other composed block — the
state reader, the memory primitive, the immutable I-type reader, and the four merge gates —
witnesses nothing and is dispatched by `localLength` alone. -/

namespace SP1Clean.StoreWordChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Operand words, in `circuit_norm`'s own orientation

The two projections the address gadget reads, stated with the projection already outside `eval` —
the form `ComputableWitnesses`'s input-agreement hypothesis hands over. -/

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

/-- StoreWord's row has computable witnesses: the four address cells come from the composed
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- the address gadget's input row: the two operand words, the offset bit, and the row selector
    simp only [circuit_norm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa only [eval_opBVal] using hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_imm) h_input
      simpa only [eval_opCImm] using hv
    · exact congrArg (fun r : Inputs (ZMod p) => r.offset_bit) h_input
    · exact congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
  all_goals simp [circuit_norm]

end SP1Clean.StoreWordChip
