import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace BitwiseChip

-- def constraints (Main : Vector BabyBear 33) : List SP1Constraint :=
--   let E0 : BabyBear := Main[30] + Main[31]
--   let E1 : BabyBear := E0 + Main[32]
--   let E2 : BabyBear := Main[30] - 1
--   let E3 : BabyBear := Main[30] * E2
--   let E4 : BabyBear := Main[31] - 1
--   let E5 : BabyBear := Main[31] * E4
--   let E6 : BabyBear := Main[32] - 1
--   let E7 : BabyBear := Main[32] * E6
--   let E8 : BabyBear := E1 - 1
--   let E9 : BabyBear := E1 * E8
--   let E10 : BabyBear := Main[30] * 2
--   let E11 : BabyBear := Main[31] * 1
--   let E12 : BabyBear := E10 + E11
--   let E13 : BabyBear := Main[32] * 0
--   let E14 : BabyBear := E12 + E13
--   let E15 : BabyBear := Main[30] * 3
--   let E16 : BabyBear := Main[31] * 4
--   let E17 : BabyBear := E15 + E16
--   let E18 : BabyBear := Main[32] * 5
--   let E19 : BabyBear := E17 + E18
--   let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints #v[Main[11], Main[12]] #v[Main[17], Main[18]] { a_low_bytes := { low_bytes := #v[Main[22], Main[23]] }, bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] }, b_low_bytes := { low_bytes := #v[Main[24], Main[25]] } } E14 E1
--   let E22 : BabyBear := Main[3] + 4
--   let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E22 8 E1
--   let E23 : BabyBear := Main[1] * 65536
--   let E24 : BabyBear := Main[2] + E23
--   let CS2 : List SP1Constraint := ALUTypeReader.constraints Main[0] E24 Main[3] E19 #v[E20, E21] { imm_c := Main[21], op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := #v[Main[15], Main[16]], op_c_memory := { access_timestamp := { diff_low_limb := Main[20], prev_low := Main[19] }, prev_value := #v[Main[17], Main[18]] } } E1
--   [
--     .assertZero E3,
--     .assertZero E5,
--     .assertZero E7,
--     .assertZero E9
--   ] ++ CS0 ++ CS1 ++ CS2

def constraints
  (Main : Vector BabyBear 33)
  : Word BabyBear × SP1ConstraintList :=
  let Expr0 := Main[30] + Main[31]
  let Expr2 := Expr0 + Main[32]
  let Expr4 := Main[30] - 1
  let Expr6 := Main[30] * Expr4
  let Expr8 := Main[31] - 1
  let Expr10 := Main[31] * Expr8
  let Expr12 := Main[32] - 1
  let Expr14 := Main[32] * Expr12
  let Expr16 := Expr2 - 1
  let Expr18 := Expr2 * Expr16
  let Expr20 := Main[30] * 2
  let Expr22 := Main[31] * 1
  let Expr24 := Expr20 + Expr22
  let Expr26 := Main[32] * 0
  let Expr28 := Expr24 + Expr26
  let Expr30 := Main[30] * 3
  let Expr32 := Main[31] * 4
  let Expr34 := Expr30 + Expr32
  let Expr36 := Main[32] * 5
  let Expr38 := Expr34 + Expr36
  let Expr42 := Main[3] + 4
  let Expr44 := 16384 * Main[1]
  let Expr46 := Expr44 + Main[2]
  let ⟨⟨⟨[Expr40, Expr41]⟩, _⟩, BitwiseU16Operation_constraints⟩ :=
    BitwiseU16Operation.constraints
      #v[Main[11], Main[12]]
      #v[Main[17], Main[18]]
      { a_low_bytes := { low_bytes := #v[Main[22], Main[23]] }
        b_low_bytes := { low_bytes := #v[Main[24], Main[25]] }
        bitwise_operation :=
          { result := #v[Main[26], Main[27], Main[28], Main[29]] } }
      Expr28
      Expr2
  let CPUState_constraints : SP1ConstraintList := CPUState.constraints
    { shard := Main[0]
      clk_high_limb := Main[1]
      clk_low_limb := Main[2]
      pc := Main[3] }
    Expr42
    4
    Expr2
  let ALUTypeReader_constraints : SP1ConstraintList := ALUTypeReader.constraints
    Main[0]
    Expr46
    Main[3]
    Expr38
    #v[Expr40, Expr41]
    { op_a := Main[4]
      op_a_memory :=
        { prev_value := #v[Main[5], Main[6]],
          access_timestamp :=
            { prev_clk := Main[7],
              diff_low_limb := Main[8] } }
      op_a_0 := Main[9],
      op_b := Main[10],
      op_b_memory :=
        { prev_value := #v[Main[11], Main[12]],
          access_timestamp :=
            { prev_clk := Main[13],
              diff_low_limb := Main[14] } }
      op_c := #v[Main[15], Main[16]],
      op_c_memory :=
        {
          prev_value := #v[Main[17], Main[18]],
          access_timestamp :=
            {
            prev_clk := Main[19],
            diff_low_limb := Main[20]
            }
        }
      imm_c := Main[21]
    }
    Expr2
  ⟨#v[Expr40, Expr41],
    [ .assertZero Expr16,
      .assertZero Expr10,
      .assertZero Expr14,
      .assertZero Expr18, ]
    ++ BitwiseU16Operation_constraints
    ++ CPUState_constraints
    ++ ALUTypeReader_constraints⟩

/-- `is_real` for the op is the sum of the individual opcodes. -/
def is_real (Main : Vector BabyBear 33) : BabyBear :=
  Main[30] + Main[31] + Main[32]

section and

def Word.bitvec_of_babybear (w : Word BabyBear) : BitVec 32 :=
  BitVec.ofNatLT ((w[0] + w[1] * 65536) % 2^32) (by omega)

-- def output_bitvec (Main : Vector BabyBear 33)

def sp1_bitwise
    (Main : Vector BabyBear 33)
    -- (cstrs : (constraints Main).allHold)
    -- (h_is_real : Main[22] = 1)
    (rd rs1 rs2 : regidx) :
    SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _rs1_value ← rX_bits rs1
  let _rs2_value ← rX_bits rs2
  let output : Word BabyBear := (constraints Main).1
  wX_bits rd (Word.bitvec_of_babybear output)

def spec_and (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_RTYPE rs2 rs1 rd rop.AND
  pure ()

def spec_or (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_RTYPE rs2 rs1 rd rop.AND
  pure ()

def spec_xor (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_RTYPE rs2 rs1 rd rop.AND
  pure ()

theorem sp1_bitwise_eq_spec_and
    (Main : Vector BabyBear 33)
    (rd rs1 rs2 : regidx)
    (h_is_and : Main[30] = 1) :
    sp1_bitwise Main rd rs1 rs2 = spec_and rd rs1 rs2 := by
  sorry

theorem sp1_bitwise_eq_spec_or
    (Main : Vector BabyBear 33)
    (rd rs1 rs2 : regidx)
    (h_is_or : Main[31] = 1) :
    sp1_bitwise Main rd rs1 rs2 = spec_or rd rs1 rs2 := by
  sorry

theorem sp1_bitwise_eq_spec_xor
    (Main : Vector BabyBear 33)
    (rd rs1 rs2 : regidx)
    (h_is_xor : Main[32] = 1) :
    sp1_bitwise Main rd rs1 rs2 = spec_xor rd rs1 rs2 := by
  sorry

end and

end BitwiseChip
