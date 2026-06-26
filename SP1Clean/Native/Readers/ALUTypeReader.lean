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

/-! # Native `ALUTypeReader` reader — the ALU register-adapter (immediate-capable op_c) as a `FormalAssertion`

The ALU-type sibling of `Readers/RTypeReader.lean`, for the ALU chips whose `op_c` may be an **immediate**
(`Addw`, `Lt`, `Bitwise`, `ShiftLeft`, `ShiftRight`). SP1's `ALUTypeReader::eval`
(mirrored in `Extracted/ALUTypeReader.lean`) is the `RTypeReader` fragment plus the immediate machinery:

- a flag `imm_c` and a **`Word`-typed** `op_c` (vs `RTypeReader`'s scalar register index);
- `imm_c` is boolean off padding (`(is_real - 1) * imm_c = 0`);
- when `imm_c = 1` the op_c "register read" is pinned to the immediate value
  (`imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0`);
- the op_c register byte/memory interactions are gated by **`is_real - imm_c`** (no register read for an
  immediate), and that multiplicity is itself asserted boolean.

Like `RTypeReader`, it is a `FormalAssertion` (output `unit`) over the **chip-owned** `cols` adapter block:
it composes a `RegisterAccessCols.circuit` per operand for the timestamp byte checks (op_a/op_b gated
`is_real`, op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + zeroing gates and the immediate
gates, and emits the Program + Memory buses (their per-row meaning is the trace-level multiset balance, so
`Guarantees := True`). The cross-block values (`clk_low`, the four `op_a_write_value` limbs `wv*`) stay
inputs; the `is_real` binary gate stays on the chip. Faithfulness to SP1's generated constraint list is the
separate `Faithful/ALUTypeReader.lean` anchor. -/

namespace SP1Clean.Readers.ALUTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files.
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` sub-assertion per operand (op_a/op_b gated `is_real` at clocks
`clk_low + 4/3`, op_c gated `is_real - imm_c` at `clk_low + 2`), impose the `op_a_0` binary gate, the
`imm_c` boolean/immediate gates, and emit the Program (`is_trusted`) + Memory (`±is_real`, op_c `±(is_real
- imm_c)`) buses. The op_c register index for the buses is its low limb `op_c[0]`; the four op_c word limbs
go into the Program message together with `imm_c`. Returns `Unit` (the adapter block `cols` is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- Per-operand timestamp byte checks (op_c gated by the immediate-aware `is_real - imm_c`).
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real - cols.imm_c, input.clk_low + 2⟩
  -- `op_a_0` binary (the `rd = x0` flag); `imm_c` boolean off padding; `is_real - imm_c` boolean.
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  (input.is_real - 1) * cols.imm_c === 0
  (input.is_real - cols.imm_c) * (input.is_real - cols.imm_c - 1) === 0
  -- Immediate consistency: when `imm_c = 1`, the op_c register "read" equals the immediate `op_c`.
  cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) === 0
  -- Program-bus instruction fetch (gated `is_trusted`): R/I-type tuple with op_c as a full word + `imm_c`.
  programChannel.emit input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
      cols.op_a_0, 0, cols.imm_c⟩ : ProgramMsg (Expression (ZMod p)))
  -- `op_a_0` zeroing gates (`rd = x0 ⇒ write 0`).
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- Memory bus: op_a is the `rd` write (new value `wv*`), op_b/op_c are the `rs1`/`rs2` reads. op_c is gated
  -- by `is_real - imm_c` (an immediate does no register read); its register index is the low limb `op_c[0]`.
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 4, cols.op_a, 0, 0,
      input.wv0, input.wv1, input.wv2, input.wv3⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
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

/-- `is_real` is binary — the precondition for the `is_real`-gated op_a/op_b byte receives (threaded into
the two composed `RegisterAccessCols`). The op_c gate `is_real - imm_c` is *proven* binary in-circuit. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `sub_eq_add_neg` on the goal aligns its `is_real - 1` / `is_real - imm_c` (HSub) with the `+ -1`
  -- form `circuit_norm` leaves in `h_holds`; the immediate-gate `Word` indexing is bridged below.
  simp only [circuit_norm, memoryChannel, programChannel, ProgramMsg.Spec, sub_eq_add_neg]
    at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_immc, h_immbin, i0, i1, i2, i3, z0, z1, z2, z3⟩ := h_holds
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, bool_of_mul_pred h_immbin, ?_,
      h_rac_a h_assumptions, h_rac_b h_assumptions, h_rac_c (bool_of_mul_pred h_immbin)⟩,
    Or.inr h_assumptions, Or.inr h_assumptions, Or.inr (bool_of_mul_pred h_immbin), fun _ _ => bool_of_mul_pred hbin⟩
  -- the four immediate gates: bridge `input_cols_op_c[i]` / `…prev_value[i]` (value-level) to the
  -- `Expression.eval env …[i]` form `h_holds` carries, via the `h_input` Word equalities + `getElem_map`.
  rw [← h_input.1.2.2.2.2.2.1, ← h_input.1.2.2.2.2.2.2.1.1]
  simp only [Vector.getElem_map]; exact ⟨i0, i1, i2, i3⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c⟩ := h_spec
  -- Align the `Spec`'s HSub (`-`) hyps with the goal's `circuit_norm` `+ -` form, and bridge the immediate
  -- gates' `input_cols_op_c[i]` (value) to the `Expression.eval env …[i]` form via the `h_input` Word eqs.
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

/-- The native ALUTypeReader reader as a Clean `FormalAssertion`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` per operand (op_c gated by `is_real - imm_c`), imposes the `op_a_0` +
immediate gates, and emits the Program/Memory buses, with a semantic spec. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.ALUTypeReader
