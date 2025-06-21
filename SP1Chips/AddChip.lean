import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace AddChip

section constraints

def constraints
  (Main : Vector BabyBear 23)
  : SP1ConstraintList :=
  let E0 : BabyBear := Main[22] - 1
  let E2 : BabyBear := Main[22] * E0
  let E4 : BabyBear := Main[3] + 4
  let E6 : BabyBear := 16384 * Main[1]
  let E8 : BabyBear := E6 + Main[2]
  [ .assertZero E2
  ]
  ++ (AddOperation.constraints #v[Main[11], Main[12], Main[16], Main[17], Main[20], Main[21], Main[22]])
  ++ (CPUState.constraints
      { clk_high := Main[0]
      , clk_16_24 := Main[1]
      , clk_0_16 := Main[2]
      , pc := Main[3] }
      E4
      4
      Main[22])
  ++ (RTypeReader.constraints
    Main[0]
    E8
    -- Main[3]
    -- 0
    #v[Main[20], Main[21]]
    { op_a := Main[4]
    , op_a_memory :=
        { prev_value := #v[Main[5], Main[6]]
        , access_timestamp :=
            { prev_low := Main[7]
            , diff_low_limb := Main[8]
            }
        }
    , op_a_0 := Main[9]
    , op_b := Main[10]
    , op_b_memory :=
        { prev_value := #v[Main[11], Main[12]]
        , access_timestamp :=
            { prev_low := Main[13]
            , diff_low_limb := Main[14]
            }
        }
    , op_c := Main[15]
    , op_c_memory :=
        { prev_value := #v[Main[16], Main[17]]
        , access_timestamp :=
            { prev_low := Main[18]
            , diff_low_limb := Main[19]
            }
        }
    }
    Main[22])

lemma bound_of_constraints (Main : Vector BabyBear 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  linarith

lemma toSailM_constraints
    (Main : Vector BabyBear 23) :
    (constraints Main).toSailM = (do
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[4]))
      (BitVec.ofNat 32 (↑Main[20] + ↑Main[21] * 65536))
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[10]))
      (BitVec.ofNat 32 (↑Main[11] + ↑Main[12] * 65536))
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[15]))
      (BitVec.ofNat 32 (↑Main[16] + ↑Main[17] * 65536))) := by
  simp [constraints, SP1ConstraintList.toSailM,
    AddOperation.constraints, CPUState.constraints, RTypeReader.constraints]

end constraints

def spec_add' (Main : Vector BabyBear 23) : SailM Unit := do
  let _ ← wX_bits (.Regidx Main[4].1)
        (BitVec.ofNat 32 (Main[5] + Main[6] * 65536))
  let _ ← wX_bits (.Regidx Main[10].1)
    (BitVec.ofNat 32 (Main[11] + Main[12] * 65536))
  let _ ← execute_RTYPE (.Regidx Main[4].1)
    (.Regidx Main[10].1) (.Regidx Main[15].val) rop.ADD

def specAdd (Main : Vector BabyBear 23) : SailM Unit := do
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let _ ← execute_RTYPE op_a op_b op_c rop.ADD

theorem SP1Add_Correct (Main : Vector BabyBear 23)
    (h_constraints : SP1ConstraintList.allHold (constraints Main))
    (h_is_real : Main[22] = 1)
    (mstate : PreSail.SequentialState RegisterType trivialChoiceSource)
    (hmem₁ : mstate.mem[Main[4]]? = some ↑(Main[5] + Main[6] * 65536).val)
    (hmem₂ : mstate.mem[Main[10]]? = some ↑(Main[11] + Main[12] * 65536).val) :

    let sp1Add : SailM Unit := (constraints Main).toSailM
    sp1Add.run mstate = (specAdd Main).run mstate := by
  sorry

theorem sp1_add_eq_spec_add
    (Main : Vector BabyBear 23)
    (cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_real : Main[22] = 1) :
    (constraints Main).toSailM = spec_add' Main := by
  unfold spec_add'
  rw [toSailM_constraints]

  let spare_cstrs := cstrs
  -- Extract the various constraints from the assumption
  simp [constraints] at cstrs
  obtain ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  rw [h_is_real] at adapter_cstrs add_cstrs

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound := RTypeReader.op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound := RTypeReader.op_c_memory_lt_of_constraints adapter_cstrs

  -- Bounded representations of the input limbs
  let M11_U16 : U16 := ⟨Main[11], op_b_memory_bound.1⟩
  let M12_U16 : U16 := ⟨Main[12], op_b_memory_bound.2⟩
  let M16_U16 : U16 := ⟨Main[16], op_c_memory_bound.1⟩
  let M17_U16 : U16 := ⟨Main[17], op_c_memory_bound.2⟩
  let M22_U1  : U1  := ⟨Main[22], by aesop⟩
  have hb1 : Main[11].val + Main[12].val * 65536 < 2 ^ 32 := by
    have := M11_U16.in_range; have := M12_U16.in_range; linarith
  have hb2 : Main[16].val + Main[17].val * 65536 < 2 ^ 32 := by
    have := M16_U16.in_range; have := M17_U16.in_range; linarith

  simp [constraints, SP1ConstraintList.toSailM]
  simp [execute_RTYPE]

  have := AddOperation.correct' Main[20] Main[21] M11_U16 M12_U16 M16_U16 M17_U16 add_cstrs

  rw [← BitVec.ofNatLT_eq_ofNat (bound_of_constraints Main spare_cstrs h_is_real)]
  rw [this]

  sorry

end AddChip
