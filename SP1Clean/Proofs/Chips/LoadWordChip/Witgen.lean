import SP1Clean.Proofs.Chips.LoadWordChip.Formal
import SP1Clean.Proofs.Operations.AddressOperation.Witgen
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.LoadWordChip` — honest witness generation (`ComputableWitnesses`)

LW/LWU on the witgen bridge (see `AddChip/Witgen.lean` for the programme note), and the first chip
whose witnesses are **not its own**. A load's row commits everything the AIR reads except the
address: the `offset_bit`, the selected 32-bit half, and the sign bit are committed input columns,
so the only witnessed cells in the row are the four the composed `AddressOperation` sub-circuit
produces (three address limbs plus the reserved-page inverse).

That is why this file is two lines of real content rather than a `populateIR` argument. The child's
own honest-witness theorem (`AddressOperation.computableWitnesses`) discharges its four cells, and
`FlatOperation.forAll_witnessCongr_of_generalSubcircuit` composes it; all the parent owes is that
the child's input row is assembled from the parent's, which is four `congrArg`s. Every other
composed block — the two readers, the memory primitive, the MSB gadget, the register write, and the
eight equality gates — witnesses nothing and is dispatched by `localLength` alone. -/

namespace SP1Clean.LoadWordChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ### Operand words, in `circuit_norm`'s own orientation

The two projections the address gadget reads, stated with the projection already outside `eval` —
the form `ComputableWitnesses`'s input-agreement hypothesis hands over. The sibling ALU chips carry
these in their `Defs.lean` as `@[circuit_norm]` lemmas; here they stay local and untagged, so that
adding them cannot perturb the chip's (large) soundness and completeness proofs. -/

/-- The rs1 base-address word, evaluated. -/
theorem eval_opBVal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_b_val
      = Vector.map (Expression.eval env) input.op_b_val := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_b_val, eval_inputs, Readers.ITypeReader.eval_cols,
    Readers.evalRegisterAccessColumns]
  exact ProvableType.eval_fields env _

/-- The sign-extended offset immediate, evaluated. -/
theorem eval_opCImm {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).op_c_imm
      = Vector.map (Expression.eval env) input.op_c_imm := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [Inputs.op_c_imm, eval_inputs, Readers.ITypeReader.eval_cols]
  exact ProvableType.eval_fields env _

/-- LoadWord's row has computable witnesses: the four address cells come from the composed
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · simp [circuit_norm]
  · -- the address gadget's input row: the two operand words, the offset bit, and the row selector
    simp only [circuit_norm]
    refine ⟨?_, ?_, congrArg (fun r : Inputs (ZMod p) => r.offset_bit) h_input, ?_⟩
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_b_val) h_input
      simpa only [eval_opBVal] using hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.op_c_imm) h_input
      simpa only [eval_opCImm] using hv
    · rw [congrArg (fun r : Inputs (ZMod p) => r.is_lw) h_input,
        congrArg (fun r : Inputs (ZMod p) => r.is_lwu) h_input]
  all_goals simp [circuit_norm]

end SP1Clean.LoadWordChip
