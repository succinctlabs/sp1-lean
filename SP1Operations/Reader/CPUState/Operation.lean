import SP1Foundations

structure CPUState where
  clk_high: Fin BB
  clk_16_24: Fin BB
  clk_0_16: Fin BB
  pc: Vector (Fin BB) 3