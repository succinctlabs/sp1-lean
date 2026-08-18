import SP1Clean.Proofs.Chips.UTypeChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.UTypeChip` — honest witness generation (`ComputableWitnesses`)

LUI/AUIPC on the witgen bridge (see `AddChip/Witgen.lean` for the programme note). Two witnessed
payloads of different kinds: the addend `is_auipc · pc`, witnessed as a bare literal vector, and the
result word, witnessed through `AddOperation.populateIR`. Both depend on the same three pieces of the
input row — the `is_auipc` selector, the program counter, and the immediate — so a single set of
agreement facts serves both. -/

namespace SP1Clean.UTypeChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- U-type's row has computable witnesses: both witnessed payloads are functions of the input row. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _ h_input => ?_,
    fun _ h_input => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · -- the addend `is_auipc · pc`, a literal vector
    have hpc : ∀ (j : ℕ) (hj : j < 3),
        Expression.eval env.toEnvironment input.state.pc[j]
          = Expression.eval env'.toEnvironment input.state.pc[j] := by
      intro j hj
      have hv := congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      simp only [eval_statePc] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[j]) hv
    have hsel : Expression.eval env.toEnvironment input.is_auipc
        = Expression.eval env'.toEnvironment input.is_auipc := by
      have hv := congrArg (fun r : Inputs (ZMod p) => r.is_auipc) h_input
      simpa [eval_inputs] using hv
    -- the payload is a bare `FExpr` product, so unfold the IR evaluator alone: naming
    -- `circuit_norm` here would reach the whole inline `main` (no `populateIR` opacity boundary)
    -- and blow the budget.
    apply Vector.ext; intro i hi
    simp only [Witgen.WitgenIR.eval, Witgen.evalSteps, Witgen.VExpr.eval, Vector.getElem_map]
    interval_cases i <;>
      simp [Witgen.FExpr.eval, hsel, hpc 0 (by omega), hpc 1 (by omega), hpc 2 (by omega)]
  · -- the result word
    have hpc : ∀ (j : ℕ) (hj : j < 3),
        Expression.eval env.toEnvironment input.state.pc[j]
          = Expression.eval env'.toEnvironment input.state.pc[j] := by
      intro j hj
      have hv := congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      simp only [eval_statePc] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[j]) hv
    have hsel : Expression.eval env.toEnvironment input.is_auipc
        = Expression.eval env'.toEnvironment input.is_auipc := by
      have hv := congrArg (fun r : Inputs (ZMod p) => r.is_auipc) h_input
      simpa [eval_inputs] using hv
    have hoa0 : Expression.eval env.toEnvironment input.adapter.op_a_0
        = Expression.eval env'.toEnvironment input.adapter.op_a_0 := by
      have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_a_0) h_input
      simpa only [eval_opA0] using hv
    refine AddOperation.populateIRGated_congr env env' _ _ _ hoa0
      (fun i hi => ?_) (fun i hi => ?_)
    · interval_cases i <;>
        simp [Expression.eval, hsel, hpc 0 (by omega), hpc 1 (by omega), hpc 2 (by omega)]
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_imm) h_input
      simp only [eval_opBImm] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.UTypeChip
