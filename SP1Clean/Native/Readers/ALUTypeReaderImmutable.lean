import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.ALUTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ALUTypeReaderImmutable` reader — the ALU register-adapter with op_a a **read**

Mirrors SP1's `ALUTypeReader::eval_op_a_immutable`
(`crates/core/machine/src/adapter/register/alu_type.rs:150`), used by `AluX0Chip` (ALU instructions with
`rd = x0`). op_a is a **source read**: there is no `wv*` write value, the op_a memory receive carries
`prev_value`, and the `op_a_0` gates pin the read value of `x0` to `0` (`op_a_0 * prev_value_i = 0`).
The op_b/op_c reads and the `imm_c` immediate machinery (op_c gated `is_real - imm_c`) are as in
`ALUTypeReader`.

A `FormalAssertion` (output `unit`) over the chip-owned `cols` adapter block, emitting the Program +
Memory buses (`Guarantees := True`); faithfulness to SP1's generated constraint list is the chip's
`Faithful/AluX0.lean` anchor (the reader's constraints are inlined there — `eval_op_a_immutable` is a
plain method, not an `SP1Operation`). -/

namespace SP1Clean.Readers.ALUTypeReaderImmutable

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files.
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` per operand (op_a/op_b gated `is_real`, op_c gated `is_real - imm_c`),
impose the `op_a_0` binary + the `imm_c` immediate gates, the four op_a **read**-zeroing gates
(`op_a_0 * op_a_memory.prev_value_i = 0`), and emit the Program (`is_trusted`) + Memory buses (op_a a read:
the receive carries `prev_value`, not a write value). Returns `Unit` (the adapter block `cols` is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real - cols.imm_c, input.clk_low + 2⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  (input.is_real - 1) * cols.imm_c === 0
  (input.is_real - cols.imm_c) * (input.is_real - cols.imm_c - 1) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) === 0
  -- Program-bus instruction fetch (gated `is_trusted`): R/I-type tuple with op_c as a full word + `imm_c`.
  programChannel.emit input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
      cols.op_a_0, 0, cols.imm_c⟩ : ProgramMsg (Expression (ZMod p)))
  -- `op_a_0` READ-zeroing gates (`rd = x0 ⇒ read value pinned to 0`).
  cols.op_a_0 * cols.op_a_memory.prev_value[0] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[1] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[2] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[3] === 0
  -- op_a (read): send prior value at prev timestamp, receive the unchanged prior value at `clk_low + 4`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 4, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  -- op_b (rs1 read): send prior value, receive the unchanged prior value at `clk_low + 3`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  -- op_c (rs2 read), gated by `is_real - imm_c` (an immediate does no register read); index its low limb.
  memoryChannel.emit (input.is_real - cols.imm_c)
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-(input.is_real - cols.imm_c))
    (⟨input.clk_high, input.clk_low + 2, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  -- the `localLength_eq` default (`by intros; rfl`) whnf-unfolds all of `main` (~15s on this main);
  -- the simp route proves the same goal ~100× cheaper (see compile-profile findings 2026-06-10).
  localLength_eq := by intros; simp +arith [circuit_norm, main, RegisterAccessCols.circuit]
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements := [byteChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the `is_real`-gated op_a/op_b byte receives. The op_c gate
`is_real - imm_c` is *proven* binary in-circuit. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel, ProgramMsg.Spec, sub_eq_add_neg]
    at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_immc, h_immbin, i0, i1, i2, i3, z0, z1, z2, z3⟩ := h_holds
  -- bridge op_a_memory.prev_value eval → value for the four read-zeroing gates (nested vector field).
  have hmap_a : Vector.map (Expression.eval env) input_var_cols_op_a_memory_prev_value
      = input_cols_op_a_memory_prev_value := h_input.1.2.1.1
  have ea0 : Expression.eval env input_var_cols_op_a_memory_prev_value[0]
      = input_cols_op_a_memory_prev_value[0] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env input_var_cols_op_a_memory_prev_value[1]
      = input_cols_op_a_memory_prev_value[1] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env input_var_cols_op_a_memory_prev_value[2]
      = input_cols_op_a_memory_prev_value[2] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env input_var_cols_op_a_memory_prev_value[3]
      = input_cols_op_a_memory_prev_value[3] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  rw [ea0] at z0; rw [ea1] at z1; rw [ea2] at z2; rw [ea3] at z3
  -- the immediate gates bridge (op_c + op_c_memory.prev_value), as in `ALUTypeReader.soundness`.
  have hoc := h_input.1.2.2.2.2.2.1
  have hpv := h_input.1.2.2.2.2.2.2.1.1
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, bool_of_mul_pred h_immbin, ?_,
      h_rac_a h_assumptions, h_rac_b h_assumptions, h_rac_c (bool_of_mul_pred h_immbin)⟩,
    Or.inr h_assumptions, Or.inr h_assumptions, Or.inr (bool_of_mul_pred h_immbin), fun _ _ => bool_of_mul_pred hbin⟩
  rw [← hoc, ← hpv]; simp only [Vector.getElem_map]; exact ⟨i0, i1, i2, i3⟩

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c⟩ := h_spec
  -- bridges: op_a_memory.prev_value (zeroing gates) and op_c / op_c_memory.prev_value (immediate gates).
  have hmap_a : Vector.map (Expression.eval env.toEnvironment) input_var_cols_op_a_memory_prev_value
      = input_cols_op_a_memory_prev_value := h_input.1.2.1.1
  have ea0 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[0]
      = input_cols_op_a_memory_prev_value[0] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[1]
      = input_cols_op_a_memory_prev_value[1] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[2]
      = input_cols_op_a_memory_prev_value[2] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[3]
      = input_cols_op_a_memory_prev_value[3] := by rw [← hmap_a]; simp only [Vector.getElem_map]
  rw [← ea0] at z0; rw [← ea1] at z1; rw [← ea2] at z2; rw [← ea3] at z3
  have hoc := h_input.1.2.2.2.2.2.1
  have hpv := h_input.1.2.2.2.2.2.2.1.1
  have eoc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c[i]'hi) = input_cols_op_c[i]'hi := by
    intro i hi; rw [← hoc, Vector.getElem_map]
  have epv : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c_memory_prev_value[i]'hi)
        = input_cols_op_c_memory_prev_value[i]'hi := by
    intro i hi; rw [← hpv, Vector.getElem_map]
  simp only [sub_eq_add_neg] at h_immc h_immbin_or hrac_c i0 i1 i2 i3
  refine ⟨⟨h_assumptions, hrac_a⟩, ⟨h_assumptions, hrac_b⟩, ⟨h_immbin_or, hrac_c⟩,
    ?_, h_immc, ?_, ?_, ?_, ?_, ?_, z0, z1, z2, z3⟩
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases h_immbin_or with h | h <;> rw [h] <;> simp
  · simp only [eoc, epv]; exact i0
  · simp only [eoc, epv]; exact i1
  · simp only [eoc, epv]; exact i2
  · simp only [eoc, epv]; exact i3

/-- The native immutable ALU-type reader as a Clean `FormalAssertion`: composes a `RegisterAccessCols` per
operand (op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + immediate + read-zeroing gates, and
emits the Program/Memory buses. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

end SP1Clean.Readers.ALUTypeReaderImmutable
