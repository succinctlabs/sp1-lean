import SP1Clean.Chips.AddiChip.Defs

/-! # `SP1Clean.AddiChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.AddiChip

open Circuit
open Extracted (AddiCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values (the register source and the immediate, both `isU64` on real and
zero-padded rows). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness (mirrors `AddChip.ProverAssumptions`, I-type adapter): the operand
`isU64`s, the `is_real` binary selector, the `op_a_0 = 0` flag, and the `is_real`-gated CPUState clock
bounds + the two register-access timestamp bounds (op_a write at `clk_low + 4`, op_b read at
`clk_low + 3`; no op_c access — it is the immediate). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_, h_add, h_adapter, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_add ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ hr).2⟩, ?_⟩
  and_intros <;>
    first | exact h_bin | exact ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ | exact Or.inl rfl | exact Or.inr h_bin
          | exact Or.inr ⟨fun _ => ⟨ha, hb⟩, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b⟩ := h_assumptions
  -- `op_b_val` is the adapter's `op_b_memory.prev_value` register-read slot (no separate committed
  -- column), so its realisation is the `prev_value` leaf of the op_b group of `h_input`; `op_c_val` is the
  -- adapter's `op_c_imm` immediate (the last top-level adapter conjunct).
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, hoc⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_b_memory_prev_value := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := by
    rw [← hoc]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b⟩, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The `Addi` chip row as a `GeneralFormalCircuit`: single-variant `is_real`-gated RV64 `add`
semantic contract over a register source + immediate, composing the witnessed `AddOperation` gadget;
output is the extracted `AddiCols` column struct. Soundness/completeness are fully proven. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddiCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.AddiChip
