import SP1Clean.Proofs.Chips.JalChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.JalChip` — honest witness generation (`ComputableWitnesses`)

JAL on the witgen bridge (see `AddChip/Witgen.lean` for the programme note). Unlike the ALU chips,
neither addend is a plain operand projection: the jump target is `pc ++ 0` plus the J-type
immediate, and the link value is `pc ++ 0` plus the literal `4`. So the input agreement is projected
onto the program counter and the immediate, and the constant limbs need nothing — which is the
general shape for any chip whose witness operands are *built* rather than read. -/

namespace SP1Clean.JalChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- JAL's row has computable witnesses: both witnessed words are functions of the input row alone. -/
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
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · -- the jump target: `pc ++ 0` plus the immediate
    have hpc : ∀ (j : ℕ) (hj : j < 3),
        Expression.eval env.toEnvironment input.state.pc[j]
          = Expression.eval env'.toEnvironment input.state.pc[j] := by
      intro j hj
      have hv := congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      simp only [eval_statePc] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[j]) hv
    refine AddOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · interval_cases i <;>
        simp [Expression.eval, hpc 0 (by omega), hpc 1 (by omega), hpc 2 (by omega)]
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_b_imm) h_input
      simp only [eval_opBImm] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · -- the link value: `pc ++ 0` plus the literal 4, whose limbs are constants
    have hpc : ∀ (j : ℕ) (hj : j < 3),
        Expression.eval env.toEnvironment input.state.pc[j]
          = Expression.eval env'.toEnvironment input.state.pc[j] := by
      intro j hj
      have hv := congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      simp only [eval_statePc] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[j]) hv
    refine AddOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · interval_cases i <;>
        simp [Expression.eval, hpc 0 (by omega), hpc 1 (by omega), hpc 2 (by omega)]
    · interval_cases i <;> simp [Expression.eval]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.JalChip
