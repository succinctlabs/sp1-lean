import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

--- A Reader that only accesses values of type `T`.
structure RTypeReader where
  op_a : BabyBear
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : BabyBear
  op_b : BabyBear
  op_b_memory : MemoryAccessInSharedCols
  op_c : BabyBear
  op_c_memory : MemoryAccessInSharedCols

namespace RTypeReader

def constraints
  (shard clk : BabyBear)
  (op_a_write_value : Word BabyBear)
  (cols : RTypeReader)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E2 : BabyBear := is_real * E0
  let E4 : BabyBear := 0 + cols.op_b
  let E6 : BabyBear := 0 + cols.op_c
  let E8 : BabyBear := op_a_write_value[0] - 0
  let E10 : BabyBear := cols.op_a_0 * E8
  let E12 : BabyBear := op_a_write_value[1] - 0
  let E14 : BabyBear := cols.op_a_0 * E12
  let E16 : BabyBear := clk + 3
  let E18 : BabyBear := is_real - 1
  let E20 : BabyBear := is_real * E18
  let E22 : BabyBear := E16 - cols.op_a_memory.access_timestamp.prev_clk
  let E24 : BabyBear := E22 - 1
  let E26 : BabyBear := E24 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E28 : BabyBear := E26 * 2013143041
  let E30 : BabyBear := clk + 2
  let E32 : BabyBear := is_real - 1
  let E34 : BabyBear := is_real * E32
  let E36 : BabyBear := E30 - cols.op_b_memory.access_timestamp.prev_clk
  let E38 : BabyBear := E36 - 1
  let E40 : BabyBear := E38 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E42 : BabyBear := E40 * 2013143041
  let E44 : BabyBear := clk + 1
  let E46 : BabyBear := is_real - 1
  let E48 : BabyBear := is_real * E46
  let E50 : BabyBear := E44 - cols.op_c_memory.access_timestamp.prev_clk
  let E52 : BabyBear := E50 - 1
  let E54 : BabyBear := E52 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E56 : BabyBear := E54 * 2013143041

  [
    .assertZero E2,
    .assertZero E10,
    .assertZero E14,
    .assertZero E20,
    .send (.byte ByteOpcode.Range cols.op_a_memory.access_timestamp.diff_low_limb 14 0) is_real,
    .send (.byte ByteOpcode.Range E28 14 0) is_real,
    .send (.memory shard cols.op_a_memory.access_timestamp.prev_clk cols.op_a cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1]) is_real,
    .receive (.memory shard E16 cols.op_a op_a_write_value[0] op_a_write_value[1]) is_real,
    .assertZero E34,
    .send (.byte ByteOpcode.Range cols.op_b_memory.access_timestamp.diff_low_limb 14 0) is_real,
    .send (.byte ByteOpcode.Range E42 14 0) is_real,
    .send (.memory shard cols.op_b_memory.access_timestamp.prev_clk cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
    .receive (.memory shard E30 cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
    .assertZero E48,
    .send (.byte ByteOpcode.Range cols.op_c_memory.access_timestamp.diff_low_limb 14 0) is_real,
    .send (.byte ByteOpcode.Range E56 14 0) is_real,
    .send (.memory shard cols.op_c_memory.access_timestamp.prev_clk cols.op_c cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) is_real,
    .receive (.memory shard E44 cols.op_c cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) is_real
  ]

lemma op_b_memory_lt_of_constraints {shard clk : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints shard clk op_a_write_value 1).allHold) :
    cols.op_b_memory.prev_value[0] < 65536 ∧ cols.op_b_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_c_memory_lt_of_constraints {shard clk : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints shard clk op_a_write_value 1).allHold) :
    cols.op_c_memory.prev_value[0] < 65536 ∧ cols.op_c_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_a_write_lt_of_constraints {shard clk : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints shard clk op_a_write_value 1).allHold) :
    op_a_write_value[0] < 65536 ∧ op_a_write_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

def registerMatch (rx : regidx) (x y : BabyBear) : Prop :=
  ∀ (pf : (x.val + y.val * 65536) < 2 ^ 32),
    rX_bits rx = pure (BitVec.ofNatLT (x.val + y.val * 65536) pf)

section registerMatch

/-- The bits in the given register correspond-/
def registerMatch (rx : regidx) (low_limb high_limb : BabyBear) : Prop :=
  ∀ (pf : (low_limb.val + high_limb.val * 65536) < 2 ^ 32),
    rX_bits rx = pure (BitVec.ofNatLT (low_limb.val + high_limb.val * 65536) pf)

/-- Note: need to be very careful making this an axiom and not proving it.
Should verify that it's at least admissable / doesn't allow for a proof of `False`. -/
axiom read_b_fun (cols : RTypeReader) (rx : regidx)
    (cstrs : (RTypeReader.constraints shard clk op_a_write_value cols is_real).allHold) :
    registerMatch rx cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]

axiom read_c_fun (cols : RTypeReader) (rx : regidx)
    (cstrs : (RTypeReader.constraints shard clk op_a_write_value cols is_real).allHold) :
    registerMatch rx cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]

end registerMatch

end RTypeReader
