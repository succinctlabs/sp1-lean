import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ALUTypeReader

/-! # Reusable `ALUTypeReader` Spec helper

Packages the RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`
as a named predicate `aluTypeReaderSpec`. Differs from `rtypeReaderSpec` by
having `op_c` as a 4-limb `Word` and carrying an `imm_c` flag that gates the
op_c memory access (`imm_c = 0` ⇒ register read; `imm_c = 1` ⇒ immediate, with
`op_c_memory.prev_value` constrained to equal `op_c`).
-/

namespace SP1Clean.ALUTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def aluTypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.ALUTypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] 0 cols.imm_c ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b < (65536 : ZMod p) ∧
  (cols.op_c[0] < (65536 : ZMod p) ∧ cols.op_c[1] < (65536 : ZMod p) ∧
   cols.op_c[2] < (65536 : ZMod p) ∧ cols.op_c[3] < (65536 : ZMod p)) ∧
  (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
  (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
  (cols.imm_c = 0 ∨ cols.imm_c = 1) ∧
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
  Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
    cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
  (cols.imm_c = 0 →
    (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 -
        cols.op_c_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
  (¬cols.op_a_0 = 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0) ∧
  (¬cols.imm_c = 0 →
    cols.op_c_memory.prev_value[0] = cols.op_c[0] ∧
    cols.op_c_memory.prev_value[1] = cols.op_c[1] ∧
    cols.op_c_memory.prev_value[2] = cols.op_c[2] ∧
    cols.op_c_memory.prev_value[3] = cols.op_c[3])

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the ALU-type reader's
constraint list `allHold` is exactly `aluTypeReaderSpec`. -/
theorem aluTypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ALUTypeReader (ZMod p)} :
    (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold ↔
      aluTypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.ALUTypeReader.allHold_constraints_iff_is_real rfl rfl]
  rfl

end SP1Clean.ALUTypeReader
