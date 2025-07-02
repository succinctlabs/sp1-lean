import SP1Operations

namespace Jal

section constraints

def constraints (Main : Vector BabyBear 15) : SP1ConstraintList :=
  let E0 : BabyBear := Main[14] - 1
  let E1 : BabyBear := Main[14] * E0
  let E2 : BabyBear := 1 * Main[10]
  let E3 : BabyBear := 0 + E2
  let E4 : BabyBear := 65536 * Main[11]
  let E5 : BabyBear := E3 + E4
  let E6 : BabyBear := Main[1] * 65536
  let E7 : BabyBear := Main[2] + E6
  let E8 : BabyBear := Main[14] - 1
  let E9 : BabyBear := Main[14] * E8
  let E10 : BabyBear := E7 + 8
  let E11 : BabyBear := Main[2] - 1
  let E12 : BabyBear := E11 * 1761607681
  let E13 : BabyBear := Main[1] * 65536
  let E14 : BabyBear := Main[2] + E13
  let E15 : BabyBear := Main[14] - 1
  let E16 : BabyBear := Main[14] * E15
  let E17 : BabyBear := Main[12] - 0
  let E18 : BabyBear := Main[9] * E17
  let E19 : BabyBear := Main[13] - 0
  let E20 : BabyBear := Main[9] * E19
  let E21 : BabyBear := E14 + 3
  let E22 : BabyBear := Main[14] - 1
  let E23 : BabyBear := Main[14] * E22
  let E24 : BabyBear := E21 - Main[7]
  let E25 : BabyBear := E24 - 1
  let E26 : BabyBear := E25 - Main[8]
  let E27 : BabyBear := E26 * 2013235201
  [
    .assertZero E1,
    .assertZero E9,
    .receive (.state Main[0] E7 Main[3]) Main[14],
    .send (.state Main[0] E10 E5) Main[14],
    .send (.byte (ByteOpcode.ofNat 6) E12 13 0) Main[14],
    .send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[14],
    .assertZero E16,
    .assertZero E18,
    .assertZero E20,
    .assertZero E23,
    .send (.byte (ByteOpcode.ofNat 6) Main[8] 16 0) Main[14],
    .send (.byte (ByteOpcode.ofNat 3) 0 E27 0) Main[14],
    .send (.memory Main[0] Main[7] Main[4] Main[5] Main[6]) Main[14],
    .receive (.memory Main[0] E21 Main[4] Main[12] Main[13]) Main[14]
  ]

end constraints

/--
This is essentially `execute_JAL` from LeanRV32D.
-/
def specJal (rd : regidx) (imm : BitVec 21) : StateM SP1State Unit := do
  let old_pc := (← get).1
  incrementPC
  update_reg rd (old_pc + 4#32)
  setPC (old_pc + imm)

-- TODO(gzgz): this should be auto-generate-able from our constraints.
def sp1Jal (Main : Vector BabyBear 15) : StateM SP1State Unit := do
  let rd := regidx.Regidx Main[4].val
  let new_pc := BitVec.ofNat 32 (Main[10] + Main[11] * 65536)
  let old_pc := BitVec.ofNat 32 (Main[12] + Main[13] * 65536)
  if Main[14] = 1 then setPC new_pc
  if Main[14] = 1 then update_reg rd old_pc

theorem SP1JAL_correct (Main : Vector BabyBear 15)
    (_h_cstrs : (constraints Main).allHold) -- note these are unused here
    (h_is_real : Main[14] = 1) -- Is a real column
    (pc : BitVec 32) (reg_state : regidx → BitVec 32) (imm : BitVec 21)
    -- The inputs are preprocessed correctly
    (hmem₁ : .ofNat 32 (Main[12] + Main[13] * 65536) = pc + 4#32)
    (hmem₂ : .ofNat 32 (Main[10] + Main[11] * 65536) = pc + imm) :
    (sp1Jal Main).run (pc, reg_state) =
      (specJal (regidx.Regidx Main[4].val) imm).run (pc, reg_state) := by
  simp only [sp1Jal, h_is_real, Fin.isValue, ↓reduceIte, BabyBearPrime, BitVec.natCast_eq_ofNat,
    StateT.run_bind, StateT.run_modify, Prod.map_apply, id_eq, bind_pure_comp, map_pure, specJal,
    StateT.run_get]
  refine congr_arg (fun out => pure (_, out)) (Prod.eq_iff_fst_eq_snd_eq.2 ⟨?_, ?_⟩)
  · simpa using hmem₂
  · refine funext fun reg => ?_
    simp [Function.update, hmem₁]

end Jal
