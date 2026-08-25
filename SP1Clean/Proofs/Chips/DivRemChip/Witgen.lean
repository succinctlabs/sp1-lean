import SP1Clean.Proofs.Chips.DivRemChip.Formal
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Congr
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.DivRemChip` — honest witness generation (`ComputableWitnesses`)

The terminal raw op-list chip: all thirty `populateRow` payloads are exportable twins
(`Populate/{IR,IRWord,IRCtq,FE}.lean`), each congruence one family `_congr` lemma over the
operand projections plus the `"div_rem_flags"` hint equation (`Populate/Congr.lean`). Every
slot consumes the same three facts projected from the struct-level input agreement
(`inputFacts`) plus `h_agree.hint_eq`. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section Orientation

/-! Operand projections, in `circuit_norm`'s own orientation (the `MulChip/Defs.lean`
pattern) — the `ComputableWitnesses` proof projects the struct-level input agreement
onto these. -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem eval_opBPrev {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).adapter.op_b_memory.prev_value
      = Vector.map (Expression.eval env) input.adapter.op_b_memory.prev_value := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem eval_opCPrev {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).adapter.op_c_memory.prev_value
      = Vector.map (Expression.eval env) input.adapter.op_c_memory.prev_value := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, Readers.RTypeReader.eval_cols,
    Readers.RTypeReader.eval_registerAccessCols]
  exact ProvableType.eval_fields env _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem eval_isReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
  rw [← ProvableStruct.eval_eq_eval]
  simp only [eval_inputs, CircuitType.eval_expr]

omit [Fact (2 ^ 24 < p)] in
/-- The three operand facts every payload congruence consumes, projected once from the
struct-level input agreement. -/
private theorem inputFacts {env env' : ProverEnvironment (ZMod p)}
    {input : Var Inputs (ZMod p)}
    (h_input : ProvableStruct.eval env.toEnvironment input
      = ProvableStruct.eval env'.toEnvironment input) :
    (∀ (i : ℕ) (_ : i < 4),
        Expression.eval env.toEnvironment input.adapter.op_b_memory.prev_value[i]
          = Expression.eval env'.toEnvironment input.adapter.op_b_memory.prev_value[i]) ∧
    (∀ (i : ℕ) (_ : i < 4),
        Expression.eval env.toEnvironment input.adapter.op_c_memory.prev_value[i]
          = Expression.eval env'.toEnvironment input.adapter.op_c_memory.prev_value[i]) ∧
    Expression.eval env.toEnvironment input.is_real
      = Expression.eval env'.toEnvironment input.is_real := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · have hv := congrArg
      (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
    rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
    simpa using congrArg (fun v : Word (ZMod p) => v[i]'hi) hv
  · have hv := congrArg
      (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    simpa using congrArg (fun v : Word (ZMod p) => v[i]'hi) hv
  · have hv := congrArg (fun r : Inputs (ZMod p) => r.is_real) h_input
    rw [eval_isReal env.toEnvironment input, eval_isReal env'.toEnvironment input] at hv
    exact hv

end Orientation

/-- DivRem's row has computable witnesses: every `populateRow` payload is a function of the
input row and the hint alone. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, populateRow, constrainRow, circuit_norm, Operations.forAllFlat,
    Operations.forAll]
  refine ⟨fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    fun h_agree h_input => ?_, fun h_agree h_input => ?_, fun h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact flagsCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact quotCompCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact aCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact bCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact cCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact mulLowerCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact mulUpperCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact scalCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact ctqCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, -⟩ := inputFacts h_input
    exact carryCongr env env' _ _ hB hC h_agree.hint_eq
  · obtain ⟨hB, -, hir⟩ := inputFacts h_input
    exact ovbCongr env env' _ _ hB hir h_agree.hint_eq
  · obtain ⟨-, hC, hir⟩ := inputFacts h_input
    exact ovcCongr env env' _ _ hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact isC0Congr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact absCCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact absRemCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact remCompCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact maxAbsCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact wCnegCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact wRnegCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact miscCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact clCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact ltfCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact neiCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact bitCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact remCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact quotCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact bMsbCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact cMsbCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact remMsbCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · obtain ⟨hB, hC, hir⟩ := inputFacts h_input
    exact quotMsbCongr env env' _ _ _ hB hC hir h_agree.hint_eq
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.DivRemChip
