import SP1Operations.Reader.RTypeReader.Operation
import SP1Operations.Reader.RTypeReader.Constraints

namespace RTypeReader

attribute [-simp] Opcode.trusted_instr Opcode.trusted_instr_poly

-- iff-characterization of RTypeReader constraints
lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c 0 0 0 0 0 ∧
      cols.op_a < 32 ∧
      cols.op_b < 65536 ∧
      cols.op_c < 65536 ∧
      (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
      (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
      pc[0] % 4 = 0 ∧
      pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536 ∧
      cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb < 65536 ∧
      (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256 ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256 ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256 ∧
      Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0) := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp, Fin.lt_def]
    intro h_is_real
    rcases h_is_real with h_is_real | h_is_real
    · simp [h_is_real]
      by_cases hop_a_0 : cols.op_a_0 = 0
      · simp [hop_a_0]
      · tauto
    · by_cases hop_a_0 : cols.op_a_0 = 0
      · simp [hop_a_0]
        aesop
      · simp [hop_a_0]
        aesop

lemma allHold_constraints_iff_is_real
    (h : is_real = 1) :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c 0 0 0 0 0 ∧
    cols.op_a < 32 ∧
    cols.op_b < 65536 ∧
    cols.op_c < 65536 ∧
    (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
    (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
    (pc[0] % 4 = 0 ∧
     pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536) ∧
    ((cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb < 65536) ∧
     ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256 ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256 ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : Fin KB)⁻¹ < 256) ∧
     (Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]])) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0) := by
  simp [allHold_constraints_iff, h, and_assoc]

/-- Polymorphic companion of `allHold_constraints_iff`. RHS uses `.val`-level
Nat-arithmetic for `Range`-opcode-derived bounds (diff_low_limb.val < 65536);
field-level `<` for U8Range bounds and program-clause bounds. -/
lemma allHold_constraints_iff_poly {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    [Fact (2 ^ 17 < p)]
    {clk_high clk_low : ZMod p}
    {pc : Vector (ZMod p) 3}
    {opcode : ZMod p}
    {instr_field_consts : Vector (ZMod p) 4}
    {op_a_write_value : Word (ZMod p)}
    {cols : RTypeReader (ZMod p)}
    {is_real : ZMod p} :
  List.Forall SP1Constraint.toProp_poly (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      Opcode.trusted_instr_poly (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c 0 0 0 0 0 ∧
      cols.op_a < (32 : ZMod p) ∧
      cols.op_b < (65536 : ZMod p) ∧
      cols.op_c < (65536 : ZMod p) ∧
      (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
      (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
      pc[0] % 4 = 0 ∧
      pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p) ∧
      cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      Word.isU64_poly #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64_poly #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
      Word.isU64_poly #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0) := by
  have h16 : (16 : ZMod p).val = 16 := by
    have := (Fact.out : 2 ^ 17 < p)
    exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  have h0_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val; simp
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly, h16, h0_lt_256, h0_lt_65536]
  intro h_is_real
  rcases h_is_real with h_is_real | h_is_real
  · simp [h_is_real]
    by_cases hop_a_0 : cols.op_a_0 = 0
    · simp [hop_a_0]
    · tauto
  · by_cases hop_a_0 : cols.op_a_0 = 0
    · simp [hop_a_0]
      aesop
    · simp [hop_a_0]
      aesop

/-- Polymorphic companion of `allHold_constraints_iff_is_real`. Specializes
the polymorphic iff to `is_real = 1`. Mirrors the `Fin KB` corollary's
proof structure. -/
lemma allHold_constraints_iff_is_real_poly
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p] [Fact (2 ^ 17 < p)]
    {clk_high clk_low : ZMod p}
    {pc : Vector (ZMod p) 3}
    {opcode : ZMod p}
    {instr_field_consts : Vector (ZMod p) 4}
    {op_a_write_value : Word (ZMod p)}
    {cols : RTypeReader (ZMod p)}
    {is_real : ZMod p}
    (h : is_real = 1) :
  List.Forall SP1Constraint.toProp_poly (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    Opcode.trusted_instr_poly (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c 0 0 0 0 0 ∧
    cols.op_a < (32 : ZMod p) ∧
    cols.op_b < (65536 : ZMod p) ∧
    cols.op_c < (65536 : ZMod p) ∧
    (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
    (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
    (pc[0] % 4 = 0 ∧
     pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p)) ∧
    ((cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536) ∧
     ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹ < (256 : ZMod p)) ∧
     (Word.isU64_poly #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64_poly #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
      Word.isU64_poly #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]])) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0) := by
  simp [allHold_constraints_iff_poly, h, and_assoc]

end RTypeReader
