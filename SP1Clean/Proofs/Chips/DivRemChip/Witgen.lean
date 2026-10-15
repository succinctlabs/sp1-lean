import SP1Clean.Proofs.Chips.DivRemChip.Formal
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Congr
import ToClean.Circuit.WitgenBridge

/-! # DivRem witness locality

All thirty `populateRow` payloads use Clean's witness IR. Their congruence proofs depend
only on the operand reads, row activity and explicit opcode selectors. `inputFacts` projects
these four agreements once from the structured circuit input; no external hint is needed.
-/

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

omit [Fact (2 ^ 24 < p)] in
/-- The input facts every payload congruence consumes, projected once from the
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
      = Expression.eval env'.toEnvironment input.is_real ∧
    (∀ (i : ℕ) (_ : i < 7),
        Expression.eval env.toEnvironment input.selectors[i]
          = Expression.eval env'.toEnvironment input.selectors[i]) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · have hv := congrArg
      (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
    rw [eval_opBPrev env.toEnvironment input, eval_opBPrev env'.toEnvironment input] at hv
    simpa using congrArg (fun v : Word (ZMod p) => v[i]'hi) hv
  · have hv := congrArg
      (fun r : Inputs (ZMod p) => r.adapter.op_c_memory.prev_value) h_input
    rw [eval_opCPrev env.toEnvironment input, eval_opCPrev env'.toEnvironment input] at hv
    simpa using congrArg (fun v : Word (ZMod p) => v[i]'hi) hv
  · exact Inputs.eval_congr_is_real h_input
  · have hv := Inputs.eval_congr_selectors h_input
    simpa only [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 7 => v[i]'hi) hv

end Orientation

/-- DivRem's row has computable witnesses: every `populateRow` payload is a function of the
input row alone. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnessesWithData := by
  intro n input env env'
  simp only [circuit, main, populateRow, constrainRow, circuit_norm, Operations.forAllFlat,
    Operations.forAll]
  refine ⟨fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    fun _h_agree h_input => ?_, fun _h_agree h_input => ?_, fun _h_agree h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · obtain ⟨-, -, -, hselectors⟩ := inputFacts h_input
    rw [flagF_congr input.selectors env env' hselectors 1 (by decide)]
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact quotCompCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact aCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact bCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact cCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact mulProgramCongr input.selectors env env' _ _ _ hB hC hir hselectors false
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact mulProgramCongr input.selectors env env' _ _ _ hB hC hir hselectors true
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact scalCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact ctqCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact carryCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, -, hir, hselectors⟩ := inputFacts h_input
    exact ovbCongr input.selectors env env' _ _ hB hir hselectors
  · obtain ⟨-, hC, hir, hselectors⟩ := inputFacts h_input
    exact ovcCongr input.selectors env env' _ _ hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact isC0Congr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact absCCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact absRemCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact remCompCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact maxAbsCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact wCnegCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact wRnegCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact miscCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact clCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact ltfCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact neiCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact bitCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact remCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact quotCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact bMsbCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact cMsbCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact remMsbCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · obtain ⟨hB, hC, hir, hselectors⟩ := inputFacts h_input
    exact quotMsbCongr input.selectors env env' _ _ _ hB hC hir hselectors
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.DivRemChip
