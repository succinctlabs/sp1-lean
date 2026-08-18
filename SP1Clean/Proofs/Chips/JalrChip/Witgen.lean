import SP1Clean.Proofs.Chips.JalrChip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.JalrChip` — honest witness generation (`ComputableWitnesses`)

JALR on the witgen bridge (see `AddChip/Witgen.lean` for the programme note), and the chip that
exercises the obligation's full hypothesis. Its first two witnesses are ordinary functions of the
input row — a register read plus an immediate, and the program counter plus the literal `4`.

The third is different: the alignment bit `lsb` reads `add_value[0]`, a cell this same row witnessed
earlier. That is exactly the case `ComputableWitnesses` is stated to permit — a generator may read
the environment *below its own offset* — so the proof uses the environment-agreement hypothesis
(`ProverEnvironment.AgreesBelow.get_eq`) rather than input agreement, which the other two use. The
cell sits eight positions below, so the side condition is arithmetic. -/

namespace SP1Clean.JalrChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- JALR's row has computable witnesses: two words that are functions of the input row, and an
alignment bit that reads only a cell this row already witnessed. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨fun _ h_input => ?_,
    fun _ h_input => ?_,
    fun h_agree _ => ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩
  · -- the jump target: the `rs1` register read plus the immediate
    refine AddOperation.populateIR_congr env env' _ _ (fun i hi => ?_) (fun i hi => ?_)
    · have hv := congrArg
        (fun r : Inputs (ZMod p) => r.adapter.op_b_memory.prev_value) h_input
      simp only [eval_rs1Prev] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
    · have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_c_imm) h_input
      simp only [eval_opCImm] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Word (ZMod p) => v[i]) hv
  · -- the link value: `pc ++ 0` plus the literal 4 (constant limbs), gated on `op_a_0`
    have hpc : ∀ (j : ℕ) (hj : j < 3),
        Expression.eval env.toEnvironment input.state.pc[j]
          = Expression.eval env'.toEnvironment input.state.pc[j] := by
      intro j hj
      have hv := congrArg (fun r : Inputs (ZMod p) => r.state.pc) h_input
      simp only [eval_statePc] at hv
      simpa [Vector.getElem_map] using congrArg (fun v : Vector (ZMod p) 3 => v[j]) hv
    have hoa0 : Expression.eval env.toEnvironment input.adapter.op_a_0
        = Expression.eval env'.toEnvironment input.adapter.op_a_0 := by
      have hv := congrArg (fun r : Inputs (ZMod p) => r.adapter.op_a_0) h_input
      simpa only [eval_opA0] using hv
    refine AddOperation.populateIRGated_congr env env' _ _ _ hoa0
      (fun i hi => ?_) (fun i hi => ?_)
    · interval_cases i <;>
        simp [Expression.eval, hpc 0 (by omega), hpc 1 (by omega), hpc 2 (by omega)]
    · interval_cases i <;> simp [Expression.eval]
  · -- the alignment bit, which reads a cell this row witnessed eight positions earlier
    rw [h_agree.get_eq (show n < 4 + (4 + n) by omega)]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]
  · simp [circuit_norm]

end SP1Clean.JalrChip
