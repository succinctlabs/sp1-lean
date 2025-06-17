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

/- def b {T : Type} (cols : RTypeReader T) : Word T := cols.op_b_memory.prev_value -/
/- def c {T : Type} (cols : RTypeReader T) : Word T := cols.op_c_memory.prev_value -/

def constraints
  (shard clk pc opcode: BabyBear)
  (op_a_write_value : Word BabyBear)
  (cols : RTypeReader)
  (is_real : BabyBear)
  : List SP1Constraint :=
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

end RTypeReader
