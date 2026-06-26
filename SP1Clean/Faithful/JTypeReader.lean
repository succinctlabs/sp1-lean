import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.JTypeReader

/-! # Faithfulness anchor — SP1's `JTypeReader` constraint fragment ↔ the native reader spec

Sibling of `Faithful/RTypeReader.lean`, for the J-type register-adapter fragment (JAL/JALR/UType).
Unlike `RTypeReader` (three operands), `JTypeReader` touches only `op_a` (the destination write).
SP1's generated `JTypeReader.constraints` (`Extracted/JTypeReader.lean`) emits, under
`is_real = is_trusted = 1`:

- two copies of the `is_real` binary gate `.assertZero (is_real * (is_real - 1))` (vacuous at `1`);
- the `.send (.program …) is_trusted` instruction fetch (per-row meaning `True`; its content is the
  trace-level program bus, `Soundness/ProgramConsistency.lean`);
- for `op_a`: a `.send (.byte Range diff 16 0)` (16-bit range) and a `.send (.byte U8Range 0 scaled 0)`
  (`< 256`) timestamp check, a `.send (.memory …)` (read prev) and a `.receive (.memory …)` (write
  new) — the memory interactions' per-row meaning is `True` (their content is the trace-level memory
  bus, `Soundness/MemoryConsistency.lean`);
- four `.assertZero (op_a_0 * (op_a_write_value[i] - 0))` zeroing gates (`rd = x0 ⟹ write 0`).

`jtypereader_constraints_faithful` proves the constraint lists hold exactly iff the four `op_a_0`
zeroing equations and `op_a`'s timestamp byte bounds — the native JTypeReader reader spec at
`is_real = 1` (the binary clauses drop because `is_real` is pinned). -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- **JTypeReader fragment — assertion half.** Under `is_real = 1`, SP1's generated `JTypeReader`
`asserts` list holds iff the four `op_a_0` zeroing equations (`rd = x0 ⟹ write 0`); the two binary
gates are vacuous at `is_real = 1`. -/
theorem jtypereader_asserts_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.JTypeReader (ZMod p)) :
    List.Forall (· = 0)
        (Extracted.JTypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ↔
      (cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
        cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) := by
  simp only [Extracted.JTypeReader.asserts, List.Forall, sub_self, mul_zero, sub_zero,
    true_and, and_true]

set_option maxHeartbeats 2000000 in
/-- **JTypeReader fragment — interaction half.** Under `is_real = is_trusted = 1`, SP1's generated
`JTypeReader` `interactions` list holds iff `op_a`'s timestamp byte bounds. The `.program`/`.memory`
interactions contribute `True`; the bounds come from `op_a`'s byte sends. -/
theorem jtypereader_interactions_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.JTypeReader (ZMod p)) :
    List.Forall Interaction.toProp
        (Extracted.JTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1) ↔
      (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
        ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
            - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.JTypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16_zmod_p, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor (JTypeReader fragment).** Under `is_real = is_trusted = 1`, SP1's generated
`JTypeReader` constraint list holds iff the four `op_a_0` zeroing equations and `op_a`'s timestamp byte
bounds hold. The `.program`/`.memory` interactions contribute `True`; the two binary gates are vacuous
at `is_real = 1`. -/
theorem jtypereader_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.JTypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.JTypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.JTypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1)) ↔
      ((cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
          cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  rw [jtypereader_asserts_faithful, jtypereader_interactions_faithful]

end SP1Clean.Faithful
