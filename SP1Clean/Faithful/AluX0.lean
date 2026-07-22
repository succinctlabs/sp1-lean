import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Extracted.AluX0Chip
import SP1Clean.Faithful.CPUState

/-! # Chip-level faithfulness anchor — SP1's whole `AluX0` chip constraint list ↔ combined spec

The fourth-artifact anchor for `AluX0` (ALU instructions into `x0`). SP1's generated `AluX0` constraint
list is `CPUState.{asserts,interactions} ++ [the inlined ALU-reader-immutable constraints, the LTU
`opcode < 29` range send, and the `is_real`/`op_a_0` gates]`. Unlike `LoadX0`, the register adapter is
**inlined** (SP1's `ALUTypeReader::eval_op_a_immutable` is a plain method, not an `SP1Operation`), so only
`CPUState` is a sub-call; the reader fragment is discharged directly with the same byte/memory `toProp`
reductions `Faithful/ALUTypeReader.lean` uses. Under `is_real = 1` the `is_real`-binary gates collapse and
the gated constraints reduce. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private lemma val_29'' [NeZero p] : (29 : ZMod p).val = 29 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (29 : ℕ) < p by omega)

set_option maxHeartbeats 4000000 in
/-- **Chip-level faithfulness anchor.** Under `is_real = 1`, SP1's generated `AluX0` chip constraint list
holds iff: the two CPUState clock bounds; the `op_a_0 = 1` forcing (`rd = x0`); the four op_a **read**-zeroing
gates; the op_c immediate gate (`is_real - imm_c` boolean) and the four immediate-consistency gates; the
dynamic opcode in ALU range (`opcode < 29`, the LTU send); and the op_a/op_b/op_c register timestamp byte
bounds (op_c guarded by `imm_c ≠ 1`). Every fragment reduces with the same machinery as
`Faithful/ALUTypeReader.lean`; the reader is inlined (not a sub-`asserts` call). -/
theorem alux0cols_constraints_faithful (cols : Extracted.AluX0Cols (ZMod p))
    (h_real : cols.is_real = 1) :
    (List.Forall (· = 0) (Extracted.AluX0Cols.asserts cols) ∧
      List.Forall Interaction.toProp (Extracted.AluX0Cols.interactions cols)) ↔
      ((((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 256)
        ∧ (cols.adapter.op_a_0 - 1 = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[0] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[1] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[2] = 0 ∧
            cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[3] = 0 ∧
            (1 - cols.adapter.imm_c) * (1 - cols.adapter.imm_c - 1) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[0] - cols.adapter.op_c[0]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[1] - cols.adapter.op_c[1]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[2] - cols.adapter.op_c[2]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[3] - cols.adapter.op_c[3]) = 0)
        ∧ (cols.opcode.val < 256 ∧ cols.opcode.val < 29)
          ∧ cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 65536
          ∧ ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256
          ∧ cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 65536
          ∧ ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256
          ∧ (¬1 - cols.adapter.imm_c = 0 →
              cols.adapter.op_c_memory.access_timestamp.diff_low_limb.val < 65536)
          ∧ (¬1 - cols.adapter.imm_c = 0 →
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 2
                - cols.adapter.op_c_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 256)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.AluX0Cols.asserts, Extracted.AluX0Cols.interactions]
  rw [Extracted.forall_append_pair]
  simp only [h_real]
  rw [cpustate_constraints_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.ofNat_four,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, ByteOpcode.constrain_LTU,
    val_16_zmod_p, val_29'', ZMod.val_zero, ZMod.val_one, one_ne_zero, ne_eq, not_false_eq_true,
    true_implies, sub_self, mul_zero, sub_zero, zero_mul, one_mul, Nat.ofNat_pos, true_and, and_true,
    false_or, true_iff, show (1 : ℕ) < 256 from by norm_num, show (29 : ℕ) < 256 from by norm_num,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

end SP1Clean.Faithful
