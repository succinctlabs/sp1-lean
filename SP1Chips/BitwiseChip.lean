import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace BitwiseChip

def constraints (Main : Vector BabyBear 33) : SP1ConstraintList :=
  let E0 : BabyBear := Main[30] + Main[31]
  let E1 : BabyBear := E0 + Main[32]
  let E2 : BabyBear := Main[30] - 1
  let E3 : BabyBear := Main[30] * E2
  let E4 : BabyBear := Main[31] - 1
  let E5 : BabyBear := Main[31] * E4
  let E6 : BabyBear := Main[32] - 1
  let E7 : BabyBear := Main[32] * E6
  let E8 : BabyBear := E1 - 1
  let E9 : BabyBear := E1 * E8
  let E10 : BabyBear := Main[30] * 2
  let E11 : BabyBear := Main[31] * 1
  let E12 : BabyBear := E10 + E11
  let E13 : BabyBear := Main[32] * 0
  let E14 : BabyBear := E12 + E13
  let E15 : BabyBear := Main[30] * 3
  let E16 : BabyBear := Main[31] * 4
  let E17 : BabyBear := E15 + E16
  let E18 : BabyBear := Main[32] * 5
  let E19 : BabyBear := E17 + E18
  let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints
    #v[Main[11], Main[12]] #v[Main[17], Main[18]]
    { a_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
      bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
      b_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
      E14
      E1
  let E22 : BabyBear := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints
    { clk_0_16 := Main[2],
      clk_16_24 := Main[1],
      clk_high := Main[0], pc := Main[3] } E22 8 E1
  let E23 : BabyBear := Main[1] * 65536
  let E24 : BabyBear := Main[2] + E23
  let CS2 : List SP1Constraint := ALUTypeReader.constraints
    Main[0]
    E24
    Main[3]
    E19
    #v[E20, E21]
    { imm_c := Main[21],
      op_a := Main[4],
      op_a_0 := Main[9],
      op_a_memory :=
        { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] },
          prev_value := #v[Main[5], Main[6]] },
      op_b := Main[10],
      op_b_memory :=
        { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] },
          prev_value := #v[Main[11], Main[12]] },
      op_c := #v[Main[15], Main[16]],
      op_c_memory :=
        { access_timestamp := { diff_low_limb := Main[20], prev_low := Main[19] },
          prev_value := #v[Main[17], Main[18]] } } E1
  [
    .assertZero E3,
    .assertZero E5,
    .assertZero E7,
    .assertZero E9
  ] ++ CS0 ++ CS1 ++ CS2

/-- `is_real` for the op is the sum of the individual opcodes. -/
def is_real (Main : Vector BabyBear 33) : BabyBear :=
  Main[30] + Main[31] + Main[32]

-- section and

-- def Word.bitvec_of_babybear (w : Word BabyBear) : BitVec 32 :=
--   BitVec.ofNatLT ((w[0] + w[1] * 65536) % 2^32) (by omega)

-- def main_output (Main : Vector BabyBear 33) : BitVec 32 :=
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
--   let ⟨⟨⟨[E20, E21]⟩, _⟩, CS0⟩ := BitwiseU16Operation.constraints
--     #v[Main[11], Main[12]] #v[Main[17], Main[18]]
--     { a_low_bytes := { low_bytes := #v[Main[22], Main[23]] },
--       bitwise_operation := { result := #v[Main[26], Main[27], Main[28], Main[29]] },
--       b_low_bytes := { low_bytes := #v[Main[24], Main[25]] } }
--       E14
--       E1
--   BitVec.ofNat 32 (E20 + E21 * 65536)

-- def sp1_bitwise
--     (Main : Vector BabyBear 33)
--     (rd rs1 rs2 : regidx) :
--     SailM Unit := do
--   writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--   let _rs1_value ← rX_bits rs1
--   let _rs2_value ← rX_bits rs2
--   wX_bits rd (main_output Main)

-- def spec_and (rd rs1 rs2 : regidx) : SailM Unit := do
--   writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--   let _ ← execute_RTYPE rs2 rs1 rd rop.AND
--   pure ()

-- def spec_or (rd rs1 rs2 : regidx) : SailM Unit := do
--   writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--   let _ ← execute_RTYPE rs2 rs1 rd rop.OR
--   pure ()

-- def spec_xor (rd rs1 rs2 : regidx) : SailM Unit := do
--   writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--   let _ ← execute_RTYPE rs2 rs1 rd rop.XOR
--   pure ()

-- theorem sp1_bitwise_eq_spec_xor
--     (Main : Vector BabyBear 33)
--     (cstrs : (constraints Main).allHold)
--     (rd rs1 rs2 : regidx)
--     (h_is_and : Main[30] = 1) :
--     sp1_bitwise Main rd rs1 rs2 = spec_xor rd rs1 rs2 := by
--   unfold sp1_bitwise spec_xor

--   have spare_cstrs : (constraints Main).allHold := cstrs

--   have h30_0 : Main[30] = 1 := sorry
--   have h31_0 : Main[31] = 0 := sorry
--   have h32_0 : Main[32] = 0 := sorry

--   simp only [SP1ConstraintList.allHold, constraints, BabyBearPrime, Fin.isValue, mul_one, mul_zero,
--     add_zero, WORD_SIZE, List.cons_append, List.nil_append, List.append_assoc] at cstrs
--   obtain ⟨h31, h31, h32, h_add_3, hop, hreg⟩ := cstrs
--   simp [- SP1Constraint.toProp_send_byte] at hreg

--   simp [h30_0, h31_0, h32_0, sub_eq_zero] at *
--   obtain ⟨⟨hbd0, h_xor0⟩, ⟨hbd1, h_xor1⟩, ⟨hbd2, h_xor2⟩, ⟨hbd3, h_xor3⟩, h_cpu, h_alu⟩ := hreg

--   simp [main_output, BitwiseU16Operation.constraints, execute_RTYPE]

--   have read_b := ALUTypeReader.read_b_fun _ rs1 h_alu
--   have read_c := ALUTypeReader.read_c_fun _ rs2 h_alu
--   rw [read_b, read_c]

--   refine bind_congr fun _ => ?_
--   refine bind_congr fun _ => ?_
--   refine congr_arg (wX_bits rd) ?_

--   simp
--   -- simp
--   clear read_b read_c h_alu h_cpu

--   sorry

-- end and

end BitwiseChip
