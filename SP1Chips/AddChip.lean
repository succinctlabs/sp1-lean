import SP1Operations.AddOperation
import SP1Operations.RTypeReader
import SP1Operations.CPUState
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace AddChip

section constraints

def constraints (Main : Vector BabyBear 23) : SP1ConstraintList :=
  let E0 : BabyBear := Main[22] - 1
  let E1 : BabyBear := Main[22] * E0
  let CS0 : List SP1Constraint := AddOperation.constraints #v[Main[11], Main[12]] #v[Main[16], Main[17]] { value := #v[Main[20], Main[21]] } Main[22]
  let E2 : BabyBear := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E2 8 Main[22]
  let E3 : BabyBear := Main[1] * 65536
  let E4 : BabyBear := Main[2] + E3
  let CS2 : List SP1Constraint := RTypeReader.constraints Main[0] E4 Main[3] 0 #v[Main[20], Main[21]] { op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := Main[15], op_c_memory := { access_timestamp := { diff_low_limb := Main[19], prev_low := Main[18] }, prev_value := #v[Main[16], Main[17]] } } Main[22]
  [
    .assertZero E1
  ] ++ CS0 ++ CS1 ++ CS2

lemma bound_of_constraints (Main : Vector BabyBear 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  linarith

end constraints

def sp1_add
  (Main : Vector BabyBear 23)
  (constraints : (AddChip.constraints Main).allHold)
  (h_is_real : Main[22] = 1)
  (rd rs1 rs2 : regidx)
  : SailM Unit :=
  let pf : Main[20].val + Main[21].val * 65536 < 2^32 :=
    by
      exact bound_of_constraints Main constraints h_is_real
  do
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    let rs1_val ← rX_bits rs1
    let rs2_val ← rX_bits rs2
    wX_bits rd (BitVec.ofNatLT (Main[20].val + Main[21].val * 65536) pf)

def spec_add (rd rs1 rs2 : regidx) : SailM Unit :=
  do
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
    pure ()

theorem sp1_add_implies_spec_add
  (Main : Vector BabyBear 23)
  (cstrs : (AddChip.constraints Main).allHold)
  (h_is_real : Main[22] = 1)
  (rd rs1 rs2 : regidx)
  (read_b : rX_bits rs1 = pure (BitVec.ofNat 32 (Main[11].val + Main[12].val * 65536)))
  (read_b_range : Main[11] < 65536 ∧ Main[12] < 65536)
  (read_c : rX_bits rs2 = pure (BitVec.ofNat 32 (Main[16].val + Main[17].val * 65536)))
  (read_c_range : Main[16] < 65536 ∧ Main[17] < 65536)
  :
  let res := (sp1_add Main cstrs h_is_real rd rs1 rs2).run s
  let res_spec := (spec_add rd rs1 rs2).run s
  res = res_spec :=
  by
    simp [sp1_add, spec_add, EStateM.run]
    simp [execute_RTYPE]

    simp [SP1ConstraintList.allHold] at cstrs
    simp [constraints] at cstrs
    obtain ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs

    -- Poor man's "coercion"
    let M11_U16 : U16 := ⟨Main[11], read_b_range.left⟩
    let M12_U16 : U16 := ⟨Main[12], read_b_range.right⟩
    let M16_U16 : U16 := ⟨Main[16], read_c_range.left⟩
    let M17_U16 : U16 := ⟨Main[17], read_c_range.right⟩
    let M22_U1  : U1  := ⟨Main[22], by simp [h_is_real]⟩

    let add_spec_wo_proof :=
      AddOperation.correct'
        #v[M11_U16, M12_U16]
        #v[M16_U16, M17_U16]
        { value := #v[Main[20], Main[21]] }
        M22_U1
        (by aesop)
        (by aesop)
    simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
    have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
    have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
    have h_res_is_u16 : Main[20].val + Main[21].val * 65536 < 2^32 := by clear * - h_low h_high; linarith
    let add_spec := add_spec_wo_proof h_res_is_u16
    simp [AddOperation.value, Word.toBV32_U16] at add_spec
    rw [add_spec]

    rw [read_b, read_c, pure_bind, pure_bind]
    rw [pure_bind, pure_bind]

    let h_b_is_u16 : Main[11].val + Main[12].val * 65536 < 2^32 :=
      by
        clear * - read_b_range
        simp [Fin.lt_def] at *
        linarith
    let h_c_is_u16 : Main[16].val + Main[17].val * 65536 < 2^32 :=
      by
        clear * - read_c_range
        simp [Fin.lt_def] at *
        linarith
    rw [←BitVec.ofNatLT_eq_ofNat h_b_is_u16, ←BitVec.ofNatLT_eq_ofNat h_c_is_u16]
