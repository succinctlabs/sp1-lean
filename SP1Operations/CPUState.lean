import SP1Foundations

-- CPUState is not parameterized by a type `T` because there shouldn't be a case
-- where we want dynamically enforce the size of `shard`, `clk`, and `pc`. In
-- other words, it shouldn't happen that sometimes we want to enfroce `pc` as U8
-- and sometimes we want to enforce `pc` as U16. They should really just be
-- `BabyBear`.
structure CPUState where
  shard : BabyBear
  clk_high_limb : BabyBear
  clk_low_limb : BabyBear
  pc : BabyBear

namespace CPUState

def clk (cols : CPUState) : BabyBear := 2^14 * cols.clk_high_limb + cols.clk_low_limb

def constraints
  (cols : CPUState)
  (next_pc : BabyBear)
  (clk_increment : BabyBear)
  (is_real : BabyBear)
  : List SP1Constraint :=
  let E0 : BabyBear := 16384 * cols.clk_high_limb
  let E2 : BabyBear := E0 + cols.clk_low_limb
  let E4 : BabyBear := is_real - 1
  let E6 : BabyBear := is_real * E4
  let E8 : BabyBear := E2 + clk_increment
  [
    .assertZero E6,
    .receive (.state cols.shard E2 cols.pc) is_real,
    .send (.state cols.shard E8 next_pc) is_real,
    .send (.byte ByteOpcode.Range cols.clk_high_limb 14 0) is_real,
    .send (.byte ByteOpcode.Range cols.clk_low_limb 14 0) is_real
  ]

end CPUState
