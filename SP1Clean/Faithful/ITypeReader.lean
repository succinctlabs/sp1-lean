import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.ITypeReader

/-! # Faithfulness anchor — SP1's `ITypeReader` constraint fragment ↔ the native reader spec

Sibling of `Faithful/RTypeReader.lean`, for the **I-type** register-adapter fragment (op_a write,
op_b read, op_c an *immediate* — no op_c register access). SP1's generated `ITypeReader.constraints`
(`Extracted/ITypeReader.lean`) emits, under `is_real = is_trusted = 1`:

- three copies of the `is_real` binary gate `.assertZero (is_real * (is_real - 1))` (vacuous at `1`);
- the `.send (.program …) is_trusted` instruction fetch (per-row meaning `True`; its content is the
  trace-level program bus, `Soundness/ProgramConsistency.lean`);
- per *register* operand (op_a, op_b only): a `.send (.byte Range diff 16 0)` (16-bit range) and a
  `.send (.byte U8Range 0 scaled 0)` (`< 256`) timestamp check, plus a `.send`/`.receive (.memory …)`
  pair (per-row meaning `True`; content is the trace-level memory bus,
  `Soundness/MemoryConsistency.lean`);
- four `.assertZero (op_a_0 * (op_a_write_value[i] - 0))` zeroing gates (`rd = x0 ⟹ write 0`).

`itypereader_constraints_faithful` proves the constraint lists hold exactly iff the four `op_a_0`
zeroing equations and the two operands' timestamp byte bounds — `Readers.ITypeReader.Spec` at
`is_real = 1`. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(16 : ZMod p).val = 16` under `Fact (2^17 < p)`. -/
private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

set_option maxHeartbeats 2000000 in
/-- **Faithfulness anchor (ITypeReader fragment).** Under `is_real = is_trusted = 1`, SP1's generated
`ITypeReader` constraint list holds iff the four `op_a_0` zeroing equations and the two register
operands' (op_a, op_b) timestamp byte bounds hold. The `.program`/`.memory` interactions contribute
`True` (their meaning is the trace-level buses); the three binary gates are vacuous at `is_real = 1`. -/
theorem itypereader_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (op_a_write_value : Word (ZMod p)) (cols : Extracted.ITypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.ITypeReader.asserts clk_high clk_low pc opcode op_a_write_value cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.ITypeReader.interactions clk_high clk_low pc opcode op_a_write_value cols 1 1)) ↔
      ((cols.op_a_0 * op_a_write_value[0] = 0 ∧ cols.op_a_0 * op_a_write_value[1] = 0 ∧
          cols.op_a_0 * op_a_write_value[2] = 0 ∧ cols.op_a_0 * op_a_write_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ITypeReader.asserts, Extracted.ITypeReader.interactions, List.Forall,
    Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

end SP1Clean.Faithful
