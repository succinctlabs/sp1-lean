import SP1Foundations
import SP1Operations.Reader.ITypeReader.Operation
import SP1Operations.Reader.ITypeReaderImmutable.Constraints

namespace ITypeReaderImmutable

set_option linter.style.setOption false
set_option linter.style.longLine false

attribute [-simp] Opcode.trusted_instr

lemma allHold_constraints_iff {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    [Fact (2 ^ 17 < p)]
    {clk_high clk_low : ZMod p}
    {pc : Vector (ZMod p) 3}
    {opcode : ZMod p}
    {cols : ITypeReader (ZMod p)}
    {is_real is_trusted : ZMod p} :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode cols is_real is_trusted) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_trusted = 0 →
      Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
      cols.op_a < (32 : ZMod p) ∧
      cols.op_b < (65536 : ZMod p) ∧
      cols.op_c_imm[0] < (65536 : ZMod p) ∧ cols.op_c_imm[1] < (65536 : ZMod p) ∧ cols.op_c_imm[2] < (65536 : ZMod p) ∧ cols.op_c_imm[3] < (65536 : ZMod p) ∧
      (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
      (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
      pc[0] % 4 = 0 ∧
      pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p)) ∧
    (¬is_real = 0 →
      cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]]) ∧
    (cols.op_a_0 ≠ 0 →
      cols.op_a_memory.prev_value[0] = 0 ∧
      cols.op_a_memory.prev_value[1] = 0 ∧
      cols.op_a_memory.prev_value[2] = 0 ∧
      cols.op_a_memory.prev_value[3] = 0)
  := by
    have h16 : (16 : ZMod p).val = 16 := by
      have := (Fact.out : 2 ^ 17 < p)
      exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)
    have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
      change (0 : ZMod p).val < (256 : ZMod p).val; simp
    have h0_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := by
      change (0 : ZMod p).val < (65536 : ZMod p).val; simp
    simp [constraints, sub_eq_zero, SP1Constraint.toProp, h16, h0_lt_256, h0_lt_65536, and_assoc]
    intros h_is_real
    rcases h_is_real with h | h
    · simp [h]
      by_cases ha0 : cols.op_a_0 = 0
      · simp [ha0]
      · tauto
    · simp [h]
      by_cases hop_a_0 : cols.op_a_0 = 0
      · simp [hop_a_0]
      · simp [hop_a_0]
        aesop

/-- Polymorphic specialization of `allHold_constraints_iff` to `is_real = 1`. -/
lemma allHold_constraints_iff_is_real
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p] [Fact (2 ^ 17 < p)]
    {clk_high clk_low : ZMod p}
    {pc : Vector (ZMod p) 3}
    {opcode : ZMod p}
    {cols : ITypeReader (ZMod p)}
    {is_real is_trusted : ZMod p}
    (h : is_real = 1) (h_trusted : is_trusted = 1) :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode cols is_real is_trusted) ↔
    Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
    cols.op_a < (32 : ZMod p) ∧
    cols.op_b < (65536 : ZMod p) ∧
    cols.op_c_imm[0] < (65536 : ZMod p) ∧ cols.op_c_imm[1] < (65536 : ZMod p) ∧ cols.op_c_imm[2] < (65536 : ZMod p) ∧ cols.op_c_imm[3] < (65536 : ZMod p) ∧
    (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
    (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
    pc[0] % 4 = 0 ∧
    pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p) ∧
    cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
    cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
    (cols.op_a_0 ≠ 0 →
      cols.op_a_memory.prev_value[0] = 0 ∧
      cols.op_a_memory.prev_value[1] = 0 ∧
      cols.op_a_memory.prev_value[2] = 0 ∧
      cols.op_a_memory.prev_value[3] = 0) := by
  simp [allHold_constraints_iff, h, h_trusted, and_assoc]

end ITypeReaderImmutable
