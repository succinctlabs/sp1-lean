import SP1Foundations

structure CPUState where
  clk_high: BabyBear
  clk_16_24: BabyBear
  clk_0_16: BabyBear
  pc: BabyBear

namespace CPUState

def constraints
  (cols : CPUState)
  (next_pc : BabyBear)
  (clk_increment : BabyBear)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := cols.clk_16_24 * 65536
  let E1 : BabyBear := cols.clk_0_16 + E0
  let E2 : BabyBear := is_real - 1
  let E3 : BabyBear := is_real * E2
  let E4 : BabyBear := E1 + clk_increment
  let E5 : BabyBear := cols.clk_0_16 - 1
  let E6 : BabyBear := E5 * 1761607681
  [
    .assertZero E3,
    .receive (.state cols.clk_high E1 cols.pc) is_real,
    .send (.state cols.clk_high E4 next_pc) is_real,
    .send (.byte (ByteOpcode.ofNat 6) E6 13 0) is_real,
    .send (.byte (ByteOpcode.ofNat 3) 0 cols.clk_16_24 0) is_real
  ]

lemma is_real_is_bool_of_constraints
    (h : (constraints cols next_pc clk_increment is_real).allHold) :
    is_real = 0 ∨ is_real = 1 := by
  simp [constraints, sub_eq_zero] at h
  tauto

lemma limb_bounds_of_constraints
    (hir : is_real ≠ 0) (h : (constraints cols next_pc clk_increment is_real).allHold) :
    (cols.clk_0_16 - 1) * 1761607681 < 8192 ∧ cols.clk_16_24 < 256 := by
  simp [constraints, sub_eq_zero, hir] at h
  tauto

end CPUState
