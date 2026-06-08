import SP1Clean.Specs.Reader
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Channels
import SP1Clean.Readers.RegisterAccessCols
import SP1Clean.Extracted.ITypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ITypeReaderImmutable` reader — the store-adapter per-row checks as a Clean `FormalAssertion`

The register adapter for **stores** (and any I-type op where `op_a` is a source read): `op_a` = rs2 read,
`op_b` = rs1 read, `op_c_imm` = immediate. Reuses the `Extracted.ITypeReader` column struct. SP1's
`ITypeReaderImmutable::eval` (`crates/core/machine/src/adapter/register/i_type.rs`, mirrored in
`Extracted/ITypeReaderImmutable.lean`) has op_a as a **read**: the receive carries `prev_value`, the
`op_a_0` zeroing gates pin the *read* value of `x0` to `0` (`op_a_0 * prev_value_i = 0`), and there is
no `wv*` write value. -/

namespace SP1Clean.Readers.ITypeReaderImmutable

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` per operand (op_a read at `clk_low + 4`, op_b read at `clk_low + 3`)
for the timestamp byte checks; impose the `op_a_0` binary + four read-zeroing gates
(`op_a_0 * prev_value_i = 0`); emit the Program bus (`imm_c = 1`) and the four Memory **read**
interactions. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  programChannel.emit input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0,
      cols.op_c_imm[0], cols.op_c_imm[1], cols.op_c_imm[2], cols.op_c_imm[3],
      cols.op_a_0, 0, 1⟩ : ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * cols.op_a_memory.prev_value[0] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[1] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[2] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[3] === 0
  -- op_a (rs2 read): send prior value at prev timestamp, receive the unchanged prior value at `clk_low + 4`.
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

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements := [byteChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated, memoryChannel.toRaw, programChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the `is_real`-gated byte receives. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, programChannel, ProgramMsg.Spec] at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, hbin, z0, z1, z2, z3⟩ := h_holds
  -- the four `op_a_0 * prev_value_i` zeroing gates are in `eval` form; bridge each `prev_value` limb to
  -- its value via the `Vector.map`-level input equality (`prev_value` is a nested vector field, so it is
  -- not auto-converted by `circuit_proof_start` the way the scalar `wv*` of `ITypeReader` are).
  have hmap : Vector.map (Expression.eval env) input_var_cols_op_a_memory_prev_value
      = input_cols_op_a_memory_prev_value := h_input.1.2.1.1
  have ev0 : Expression.eval env input_var_cols_op_a_memory_prev_value[0]
      = input_cols_op_a_memory_prev_value[0] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env input_var_cols_op_a_memory_prev_value[1]
      = input_cols_op_a_memory_prev_value[1] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev2 : Expression.eval env input_var_cols_op_a_memory_prev_value[2]
      = input_cols_op_a_memory_prev_value[2] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev3 : Expression.eval env input_var_cols_op_a_memory_prev_value[3]
      = input_cols_op_a_memory_prev_value[3] := by rw [← hmap]; simp only [Vector.getElem_map]
  rw [ev0] at z0; rw [ev1] at z1; rw [ev2] at z2; rw [ev3] at z3
  exact ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions, h_rac_b h_assumptions⟩,
    Or.inr h_assumptions, Or.inr h_assumptions, fun _ => bool_of_mul_pred hbin⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b⟩ := h_spec
  -- bridge the `prev_value` zeroing gates from value form (in `Spec`) to `eval` form (the goal asserts).
  have hmap : Vector.map (Expression.eval env.toEnvironment) input_var_cols_op_a_memory_prev_value
      = input_cols_op_a_memory_prev_value := h_input.1.2.1.1
  have ev0 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[0]
      = input_cols_op_a_memory_prev_value[0] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev1 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[1]
      = input_cols_op_a_memory_prev_value[1] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev2 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[2]
      = input_cols_op_a_memory_prev_value[2] := by rw [← hmap]; simp only [Vector.getElem_map]
  have ev3 : Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[3]
      = input_cols_op_a_memory_prev_value[3] := by rw [← hmap]; simp only [Vector.getElem_map]
  rw [← ev0] at z0; rw [← ev1] at z1; rw [← ev2] at z2; rw [← ev3] at z3
  refine ⟨⟨h_assumptions, hrac_a⟩, ⟨h_assumptions, hrac_b⟩, ?_, z0, z1, z2, z3⟩
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The native immutable I-type reader as a Clean `FormalAssertion`: composes a `RegisterAccessCols` per
operand (both reads), imposes the `op_a_0` binary + read-zeroing gates, and emits the Program/Memory buses. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.ITypeReaderImmutable
