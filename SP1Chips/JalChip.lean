import SP1Operations

namespace JalChip

def constraints (Main : Vector (Fin BB) 31) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30] - 1
  let E1 : Fin BB := Main[30] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]
  let E2 : Fin BB := Main[1] * 65536
  let E3 : Fin BB := Main[2] + E2
  let E4 : Fin BB := Main[30] - 1
  let E5 : Fin BB := Main[30] * E4
  let E6 : Fin BB := E3 + 8
  let E7 : Fin BB := Main[2] - 1
  let E8 : Fin BB := E7 * 1761607681
  let E9 : Fin BB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[26], Main[27], Main[28], Main[29]] } E9
  let E10 : Fin BB := Main[13] * Main[26]
  let E11 : Fin BB := Main[13] * Main[27]
  let E12 : Fin BB := Main[13] * Main[28]
  let E13 : Fin BB := Main[1] * 65536
  let E14 : Fin BB := Main[2] + E13
  let E15 : Fin BB := Main[30] - 1
  let E16 : Fin BB := Main[30] * E15
  let E17 : Fin BB := Main[26] - 0
  let E18 : Fin BB := Main[13] * E17
  let E19 : Fin BB := Main[27] - 0
  let E20 : Fin BB := Main[13] * E19
  let E21 : Fin BB := Main[28] - 0
  let E22 : Fin BB := Main[13] * E21
  let E23 : Fin BB := Main[29] - 0
  let E24 : Fin BB := Main[13] * E23
  let E25 : Fin BB := E14 + 3
  let E26 : Fin BB := Main[30] - 1
  let E27 : Fin BB := Main[30] * E26
  let E28 : Fin BB := E25 - Main[11]
  let E29 : Fin BB := E28 - 1
  let E30 : Fin BB := E29 - Main[12]
  let E31 : Fin BB := E30 * 2013235201
  [
    (.assertZero E1),
    (.assertZero Main[25]),
    (.assertZero E5),
    (.receive (.state Main[0] E3 Main[3] Main[4] Main[5]) Main[30]),
    (.send (.state Main[0] E6 Main[22] Main[23] Main[24]) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 7) E8 13 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[30]),
    (.assertZero Main[29]),
    (.assertZero E10),
    (.assertZero E11),
    (.assertZero E12),
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E27),
    (.send (.byte (ByteOpcode.ofNat 7) Main[12] 16 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E31 0) Main[30]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[30]),
    (.receive (.memory Main[0] E25 Main[6] 0 0 Main[26] Main[27] Main[28] Main[29]) Main[30]),
  ] ++ CS0 ++ CS1

end JalChip

-- namespace Jal

-- section constraints

-- def constraints (Main : Vector (Fin BB) 15) : SP1ConstraintList :=
--   let E0 : Fin BB := Main[14] - 1
--   let E1 : Fin BB := Main[14] * E0
--   let E2 : Fin BB := 1 * Main[10]
--   let E3 : Fin BB := 0 + E2
--   let E4 : Fin BB := 65536 * Main[11]
--   let E5 : Fin BB := E3 + E4
--   let E6 : Fin BB := Main[1] * 65536
--   let E7 : Fin BB := Main[2] + E6
--   let E8 : Fin BB := Main[14] - 1
--   let E9 : Fin BB := Main[14] * E8
--   let E10 : Fin BB := E7 + 8
--   let E11 : Fin BB := Main[2] - 1
--   let E12 : Fin BB := E11 * 1761607681
--   let E13 : Fin BB := Main[1] * 65536
--   let E14 : Fin BB := Main[2] + E13
--   let E15 : Fin BB := Main[14] - 1
--   let E16 : Fin BB := Main[14] * E15
--   let E17 : Fin BB := Main[12] - 0
--   let E18 : Fin BB := Main[9] * E17
--   let E19 : Fin BB := Main[13] - 0
--   let E20 : Fin BB := Main[9] * E19
--   let E21 : Fin BB := E14 + 3
--   let E22 : Fin BB := Main[14] - 1
--   let E23 : Fin BB := Main[14] * E22
--   let E24 : Fin BB := E21 - Main[7]
--   let E25 : Fin BB := E24 - 1
--   let E26 : Fin BB := E25 - Main[8]
--   let E27 : Fin BB := E26 * 2013235201
--   [
--     .assertZero E1,
--     .assertZero E9,
--     .receive (.state Main[0] E7 Main[3]) Main[14],
--     .send (.state Main[0] E10 E5) Main[14],
--     .send (.byte (ByteOpcode.ofNat 6) E12 13 0) Main[14],
--     .send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[14],
--     .assertZero E16,
--     .assertZero E18,
--     .assertZero E20,
--     .assertZero E23,
--     .send (.byte (ByteOpcode.ofNat 6) Main[8] 16 0) Main[14],
--     .send (.byte (ByteOpcode.ofNat 3) 0 E27 0) Main[14],
--     .send (.memory Main[0] Main[7] Main[4] Main[5] Main[6]) Main[14],
--     .receive (.memory Main[0] E21 Main[4] Main[12] Main[13]) Main[14]
--   ]

-- end constraints

-- /--
-- This is essentially `execute_JAL` from LeanRV32D.
-- -/
-- def specJal (rd : regidx) (imm : BitVec 21) : StateM SP1State Unit := do
--   let old_pc := (← get).1
--   incrementPC
--   update_reg rd (old_pc + 4#32)
--   setPC (old_pc + imm)

-- -- TODO(gzgz): this should be auto-generate-able from our constraints.
-- def sp1Jal (Main : Vector (Fin BB) 15) : StateM SP1State Unit := do
--   let rd := regidx.Regidx Main[4].val
--   let new_pc := BitVec.ofNat 32 (Main[10] + Main[11] * 65536)
--   let old_pc := BitVec.ofNat 32 (Main[12] + Main[13] * 65536)
--   if Main[14] = 1 then setPC new_pc
--   if Main[14] = 1 then update_reg rd old_pc

-- theorem SP1JAL_correct (Main : Vector (Fin BB) 15)
--     (_h_cstrs : (constraints Main).allHold) -- note these are unused here
--     (h_is_real : Main[14] = 1) -- Is a real column
--     (pc : BitVec 32) (reg_state : regidx → BitVec 32) (imm : BitVec 21)
--     -- The inputs are preprocessed correctly
--     (hmem₁ : .ofNat 32 (Main[12] + Main[13] * 65536) = pc + 4#32)
--     (hmem₂ : .ofNat 32 (Main[10] + Main[11] * 65536) = pc + imm) :
--     (sp1Jal Main).run (pc, reg_state) =
--       (specJal (regidx.Regidx Main[4].val) imm).run (pc, reg_state) := by
--   simp only [sp1Jal, h_is_real, Fin.isValue, ↓reduceIte, BB, BitVec.natCast_eq_ofNat,
--     StateT.run_bind, StateT.run_modify, Prod.map_apply, id_eq, bind_pure_comp, map_pure, specJal,
--     StateT.run_get]
--   refine congr_arg (fun out => pure (_, out)) (Prod.eq_iff_fst_eq_snd_eq.2 ⟨?_, ?_⟩)
--   · simpa using hmem₂
--   · refine funext fun reg => ?_
--     simp [Function.update, hmem₁]

-- end Jal
