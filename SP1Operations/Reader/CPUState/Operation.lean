import SP1Foundations

structure CPUState (F : Type*) where
  clk_high : F
  clk_16_24 : F
  clk_0_16 : F
  pc : Vector F 3
