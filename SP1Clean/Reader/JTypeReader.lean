import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.JTypeReader
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess

/-! # Reusable `JTypeReader` Spec helper

Packages the RHS of `_root_.JTypeReader.allHold_constraints_iff_is_real_poly`
as a named predicate `jtypeReaderSpec`. Differs from `rtypeReaderSpec` by
carrying two 4-limb immediates (`op_b_imm` and `op_c_imm`) and only one
memory access (the op_a write). The chip footprint is `LUI` / `AUIPC` /
`JAL`-class — opcodes that write op_a but have no register-source reads.
-/

namespace SP1Clean.JTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.JTypeReader.allHold_constraints_iff_is_real_poly`,
packaged as a named predicate. -/
def jtypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.JTypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr_poly (Opcode.ofNat opcode.val) cols.op_a
      cols.op_b_imm[0] cols.op_b_imm[1] cols.op_b_imm[2] cols.op_b_imm[3]
      cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 1 1 ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b_imm[0] < (65536 : ZMod p) ∧ cols.op_b_imm[1] < (65536 : ZMod p) ∧
  cols.op_b_imm[2] < (65536 : ZMod p) ∧ cols.op_b_imm[3] < (65536 : ZMod p) ∧
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
  Word.isU64_poly #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  (cols.op_a_0 ≠ 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the J-type reader's
constraint list `allHold_poly` is exactly `jtypeReaderSpec`. -/
theorem jtypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.JTypeReader (ZMod p)} :
    (_root_.JTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold_poly ↔
      jtypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.JTypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold_poly
        = List.Forall SP1Constraint.toProp_poly
            (_root_.JTypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.JTypeReader.allHold_constraints_iff_is_real_poly rfl rfl]
  rfl

end SP1Clean.JTypeReader
