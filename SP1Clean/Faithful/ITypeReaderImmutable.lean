import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.ITypeReaderImmutable

/-! # Faithfulness anchor — SP1's `ITypeReaderImmutable` constraint fragment ↔ the native reader spec

Sibling of `Faithful/ITypeReader.lean`, for the **immutable** I-type register-adapter fragment used by
stores (op_a = rs2 *read*, op_b = rs1 read, op_c an immediate). SP1's generated
`ITypeReaderImmutable.constraints` (`Extracted/ITypeReaderImmutable.lean`) is `ITypeReader` with op_a a
read: the four `op_a_0` zeroing gates pin the **read** value of `x0` to `0`
(`op_a_0 * op_a_memory.prev_value[i] = 0`), and the op_a memory `.receive` carries `prev_value`
(no write value). Under `is_real = is_trusted = 1` it emits three `is_real` binary gates
(vacuous), the `.program` fetch (per-row meaning `True`), and per register operand (op_a, op_b) a
`.byte Range`/`.byte U8Range` timestamp check + a `.memory` send/receive pair (meaning `True`).

`itypereaderimmutable_constraints_faithful` proves the lists hold iff the four `op_a_0` read-zeroing
equations and the two operands' timestamp byte bounds — precisely `Readers.ITypeReaderImmutable.Spec`
restricted to `is_real = 1`. -/

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
/-- **Faithfulness anchor (ITypeReaderImmutable fragment).** Under `is_real = is_trusted = 1`, SP1's
generated `ITypeReaderImmutable` constraint list holds iff the four `op_a_0` *read*-zeroing equations and
the two register operands' (op_a, op_b) timestamp byte bounds hold. -/
theorem itypereaderimmutable_constraints_faithful
    (clk_high clk_low : ZMod p) (pc : Vector (ZMod p) 3) (opcode : ZMod p)
    (cols : Extracted.ITypeReader (ZMod p)) :
    (List.Forall (· = 0)
          (Extracted.ITypeReaderImmutable.asserts clk_high clk_low pc opcode cols 1 1) ∧
        List.Forall Interaction.toProp
          (Extracted.ITypeReaderImmutable.interactions clk_high clk_low pc opcode cols 1 1)) ↔
      ((cols.op_a_0 * cols.op_a_memory.prev_value[0] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[1] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[2] = 0 ∧
          cols.op_a_0 * cols.op_a_memory.prev_value[3] = 0) ∧
        (cols.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1
              - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
        (cols.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
          ((clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1
              - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.ITypeReaderImmutable.asserts, Extracted.ITypeReaderImmutable.interactions,
    List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

end SP1Clean.Faithful
