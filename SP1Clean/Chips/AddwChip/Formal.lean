import SP1Clean.Chips.AddwChip.Defs

/-! # `SP1Clean.AddwChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Migrated onto the reader/bus pattern (mirrors `SubwChip` for the W-arithmetic discipline, `LtChip` for the
**ALU** adapter). This module holds the prover/verifier `Assumptions`, the soundness/completeness proofs,
and the bundled `circuit`. The headline `Spec` (inline `ALUTypeReader.Spec` ∧ binary ∧ gated `RV64.addw`)
lives in `Specs/Chip.lean`. -/

namespace SP1Clean.AddwChip

open Circuit
open Extracted (AddwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values (true on real and zero-padded rows). `is_real`-binary is proven by
soundness from the in-circuit gate; only completeness needs it as a precondition. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness (mirrors `LtChip.ProverAssumptions`, ALU adapter): operand `isU64`s,
the `is_real` binary selector, `op_a_0 = 0`, `imm_c = 0` (ADDW is register-register), the CPUState clock
bounds, and the three timestamp `Spec`s (op_c gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧ input.adapter.imm_c = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- **W-instruction soundness** — same two `circuit_proof_start` landmines as `SubwChip` (the nested
sign-fill `(output).msb.msb * 65535` is threaded through the reader's bus emits): use `.2.1`/`.2.2.1`/
`.2.2.2` projections, never `obtain`/`rcases`/`cases` on `h_holds`, and keep the `Spec` opaque (don't pass
`[Spec]`) so `RV64.addw` never reaches `circuit_norm` — the arith goes through `rv64_addw_eq` by hand.
ADDW's adapter is the `ALUTypeReader` (the `Spec`'s first conjunct), as in `LtChip`. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h_addw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  have h_bin := bool_of_mul_pred h_holds.2.2.2
  have ha := h_assumptions.1
  have hb := h_assumptions.2
  have h_as : AddwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } := ⟨ha, hb, h_bin⟩
  refine ⟨⟨?_, h_bin, fun hr => ?_⟩, ?_⟩
  · -- reader conjunct: `wv* := (resultWord cols)[i]` reduce to the four limbs `main` passed.
    simpa only [resultWord, Vector.getElem_map] using h_adapter h_bin
  · -- the `is_real`-gated W arith: bridge the gadget's `signExtend` equation to `RV64.addw`.
    refine trans ?_ (rv64_addw_eq _ _).symm
    simpa only [resultWord, AddwOperation.resultWord, Vector.getElem_map] using
      ((h_addw h_as).2 hr).2
  · -- channel-requirement tail (the readers carry the binary fact; `AddwOperation` emits the byte bus).
    and_intros <;> first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr h_as

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, himm, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  -- `op_b_val`/`op_c_val` are now the adapter's `op_b_memory`/`op_c_memory` register-read slots (no
  -- separate committed columns); their realisations are the `prev_value` leaves of those groups of
  -- `h_input` (the ALU adapter block — `op_c_memory` is *grouped* since `imm_c` is the final field).
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, ⟨hoc, -, -⟩, -⟩ := h_input
  obtain ⟨h_env_val, h_env_msb⟩ := h_env
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_b_memory_prev_value := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_c_memory_prev_value := by
    rw [← hoc]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i => var { index := i₀ + i }) : Vector (ZMod p) 2)
      = AddwOperation.addwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2) = AddwOperation.addwMsbWitness input_adapter_op_b_memory_prev_value
      input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval, hmsbeq]; exact AddwOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The ADDW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the CPUState + the immediate-capable register reader; output is the extracted `AddwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.AddwChip
