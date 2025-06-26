import SP1Operations

open BitVec

namespace BitwiseChip

section constraints

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


def main_output (Main : Vector BabyBear 33) : BitVec 32 :=
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
  BitVec.ofNat 32 (E20 + E21 * 65536)

-- lemma allHold_constraints_iff (Main : Vector BabyBear 33) :
--     (constraints Main).allHold ↔


end constraints

def specXor (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let b : BitVec 32 := (← get).2 op_b
  let c : BitVec 32 := (← get).2 op_c
  update_reg op_a (b ^^^ c)

def sp1Bitwise (Main : Vector BabyBear 33) : StateM SP1State Unit := do
  incrementPC
  let op_a := regidx.Regidx Main[4].val
  update_reg op_a (main_output Main)

/-- If the constraints all hold, the column is real, and `op_b` and `op_c` are loaded
into the proper registers, then the add chip conforms to the spec. -/
theorem SP1AddChip_Correct (Main : Vector BabyBear 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (opcode : ByteOpcode) (h : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h_is_xor : Main[30] = 1)
    (pc : BitVec 32) (reg_state : regidx → BitVec 32)
    (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536))
    (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 32 (Main[16] + Main[17] * 65536)) :
    (sp1Bitwise Main).run (pc, reg_state) = (specXor Main).run (pc, reg_state) := by
  unfold sp1Bitwise specXor
  rw [BitVec.natCast_eq_ofNat] at hmem₁ hmem₂
  have h31 : Main[31] = 0 := sorry
  have h32 : Main[32] = 0 := sorry
  simp [constraints, BitwiseU16Operation.constraints] at h_cstrs

  obtain ⟨h1, h2, h3, h4, bw_cstrs, cpu_strs, adapter_cstrs⟩ := h_cstrs

  simp [h_is_xor, h31, h32] at *

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound : Main[11].1 < 65536 ∧ Main[12].1 < 65536 :=
    ALUTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound : Main[17].1 < 65536 ∧ Main[18].1 < 65536 :=
    ALUTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs
  have hb1 : Main[11].val + Main[12].val * 65536 < 2 ^ 32 := by omega
  have hb2 : Main[17].val + Main[18].val * 65536 < 2 ^ 32 := by omega

  have h_add_op : (Main[20] + Main[21] * 65536 : ℕ)#'sorry =
      (Main[11] + Main[12] * 65536 : ℕ)#'hb1 ^^^ (Main[17] + Main[18] * 65536)#'hb2 := by
    sorry
    -- simpa using BitwiseOperation.eq_xor_of_constraints
    --   #v[⟨Main[11], op_b_memory_bound.1⟩, ⟨Main[12], op_b_memory_bound.2⟩]
    --   #v[⟨Main[16], op_c_memory_bound.1⟩, ⟨Main[17], op_c_memory_bound.2⟩]
    --   { value := #v[Main[20], Main[21]] }
    --   ⟨Main[22], by aesop⟩
    --   (by simp_all)
    --   (by simp [h_is_real])
    --   hb3

  -- simp [BabyBearPrime, BitVec.natCast_eq_ofNat, StateT.run_modify, StateT.run_bind,
  --   StateT.run_get, bind_pure_comp, map_pure, Prod.map_apply, id_eq]
  refine congr_arg (fun out => pure (_, (_, out))) (funext fun reg => ?_)
  by_cases hreg : (regidx.Regidx (BitVec.ofNat 5 ↑Main[4])) = reg
  · rw [hreg, Function.update_self, Function.update_self, hmem₁, hmem₂,]
    rw [main_output]
    simp [BitwiseU16Operation.constraints]

    sorry
      -- ← BitVec.ofNatLT_eq_ofNat hb3, ← BitVec.ofNatLT_eq_ofNat hb1,
      -- ← BitVec.ofNatLT_eq_ofNat hb2, h_add_op]
  · rw [Function.update_of_ne (Ne.symm hreg), Function.update_of_ne (Ne.symm hreg)]

end BitwiseChip
