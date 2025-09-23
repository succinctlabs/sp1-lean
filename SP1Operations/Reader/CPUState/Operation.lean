import SP1Foundations

structure CPUState where
  clk_high: Fin KB
  clk_16_24: Fin KB
  clk_0_16: Fin KB
  pc: Vector (Fin KB) 3
