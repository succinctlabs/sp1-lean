import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ITypeReader

/-! # Reusable `ITypeReader` Spec helper

Packages the RHS of `_root_.ITypeReader.allHold_constraints_iff_is_real_poly`
as a named predicate `itypeReaderSpec`. Chip-level Specs that consume this
get the I-type-reader constraint surface as a single named conjunct rather
than the ~20 inline clauses currently in `SP1Clean.Addi.Spec`.
-/

namespace SP1Clean.ITypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ITypeReader.allHold_constraints_iff_is_real_poly`,
packaged as a named predicate. -/
def itypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.ITypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr_poly (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b < (65536 : ZMod p) ∧
  cols.op_c_imm[0] < (65536 : ZMod p) ∧ cols.op_c_imm[1] < (65536 : ZMod p) ∧
  cols.op_c_imm[2] < (65536 : ZMod p) ∧ cols.op_c_imm[3] < (65536 : ZMod p) ∧
  (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
  (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
  pc[0] % 4 = 0 ∧
  pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p) ∧
  cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
      cols.op_b_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
      cols.op_a_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64_poly #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  Word.isU64_poly #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
    cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
  (cols.op_a_0 ≠ 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the I-type reader's
constraint list `allHold_poly` is exactly `itypeReaderSpec`. -/
theorem itypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ITypeReader (ZMod p)} :
    (_root_.ITypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold_poly ↔
      itypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ITypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold_poly
        = List.Forall SP1Constraint.toProp_poly
            (_root_.ITypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.ITypeReader.allHold_constraints_iff_is_real_poly rfl rfl]
  rfl

end SP1Clean.ITypeReader
