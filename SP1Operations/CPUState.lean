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

def spec
  (cols : CPUState)
  (next_pc : BabyBear)
  (clk_increment : BabyBear)
  (is_real : U2) : Prop := by sorry

end CPUState
