import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.RTypeReader
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess

/-! # Reusable `RTypeReader` Spec helper

Packages the RHS of `_root_.RTypeReader.allHold_constraints_iff_is_real_poly`
as a named predicate `rtypeReaderSpec`. Differs from `itypeReaderSpec` by
having `op_c` as a register (with full memory-access substruct) instead of
the four immediate limbs `op_c_imm`.

Also exposes `programRow` — the 16-tuple `fields 16` view of an R-type
row that is the natural argument to `lookup SP1Clean.ProgramTable`.
-/

namespace SP1Clean.RTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The 16-tuple program-bus row for an R-type instruction with opcode
`opcode`. Matches `AirInteraction.program` from `SP1Foundations/Constraint.lean`:
`#v[pc0, pc1, pc2, opcode, op_a, op_b_0..3, op_c_0..3, op_a_0, imm_b, imm_c]`,
with the R-type discipline that `op_b` and `op_c` are single-limb register
indices (limbs 1–3 are zero) and `imm_b = imm_c = 0`. -/
@[reducible]
def programRow (opcode : ZMod p) (pc : Vector (ZMod p) 3)
    (cols : _root_.RTypeReader (ZMod p)) : fields 16 (ZMod p) :=
  #v[pc[0], pc[1], pc[2], opcode,
     cols.op_a, cols.op_b, 0, 0, 0,
     cols.op_c, 0, 0, 0,
     cols.op_a_0, 0, 0]

/-- The RHS of `_root_.RTypeReader.allHold_constraints_iff_is_real_poly`,
packaged as a named predicate. -/
def rtypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.RTypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr_poly (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c 0 0 0 0 0 ∧
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
   ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 -
        cols.op_c_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
        cols.op_b_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
        cols.op_a_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p)) ∧
   (Word.isU64_poly #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
    Word.isU64_poly #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
    Word.isU64_poly #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]])) ∧
  (cols.op_a_0 ≠ 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the R-type reader's
constraint list `allHold_poly` is exactly `rtypeReaderSpec`. -/
theorem rtypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.RTypeReader (ZMod p)} :
    (_root_.RTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold_poly ↔
      rtypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.RTypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold_poly
        = List.Forall SP1Constraint.toProp_poly
            (_root_.RTypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.RTypeReader.allHold_constraints_iff_is_real_poly rfl rfl]
  rfl

end SP1Clean.RTypeReader
