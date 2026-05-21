import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ITypeReaderImmutable

/-! # Reusable `ITypeReaderImmutable` Spec helper

Packages the RHS of `_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real`
as a named predicate `itypeReaderImmutableSpec`. Sibling of
`SP1Clean.ITypeReader.itypeReaderSpec`; differs in that there is no
`op_a_write_value` parameter — `ITypeReaderImmutable` is the reader for
Store chips, which read op_a as the source data rather than writing it.
The `cols.op_a_0 ≠ 0 → …` trailer constrains
`cols.op_a_memory.prev_value` to zero rather than constraining a separate
write value.
-/

namespace SP1Clean.ITypeReaderImmutable

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def itypeReaderImmutableSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (cols : _root_.ITypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
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
  (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
      cols.op_a_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
      cols.op_b_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
    cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
  (cols.op_a_0 ≠ 0 →
    cols.op_a_memory.prev_value[0] = 0 ∧ cols.op_a_memory.prev_value[1] = 0 ∧
    cols.op_a_memory.prev_value[2] = 0 ∧ cols.op_a_memory.prev_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the
ITypeReaderImmutable's constraint list `allHold` is exactly
`itypeReaderImmutableSpec`. -/
theorem itypeReaderImmutableSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {cols : _root_.ITypeReader (ZMod p)} :
    (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
        cols 1 1).allHold ↔
      itypeReaderImmutableSpec clk_low opcode pc cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
        cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
              cols 1 1) from rfl]
  rw [_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real rfl rfl]
  rfl

end SP1Clean.ITypeReaderImmutable
