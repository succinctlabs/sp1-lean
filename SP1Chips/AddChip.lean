import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace AddChip

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
      { shard := Main[0]
      , clk_high_limb := Main[1]
      , clk_low_limb := Main[2]
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
            { prev_clk := Main[7]
            , diff_low_limb := Main[8]
            }
        }
    , op_a_0 := Main[9]
    , op_b := Main[10]
    , op_b_memory :=
        { prev_value := #v[Main[11], Main[12]]
        , access_timestamp :=
            { prev_clk := Main[13]
            , diff_low_limb := Main[14]
            }
        }
    , op_c := Main[15]
    , op_c_memory :=
        { prev_value := #v[Main[16], Main[17]]
        , access_timestamp :=
            { prev_clk := Main[18]
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

def sp1_add
    (Main : Vector BabyBear 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1)
    (rd rs1 rs2 : regidx) :
    SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let rs1_value ← rX_bits rs1
  let rs2_value ← rX_bits rs2
  wX_bits rd (BitVec.ofNatLT (Main[20].val + Main[21].val * 65536)
    (bound_of_constraints Main cstrs h_is_real))

def spec_add
    (rd rs1 rs2 : regidx) :
    SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add (Main : Vector BabyBear 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1) (rd rs1 rs2 : regidx) :
    sp1_add Main cstrs h_is_real rd rs1 rs2 = spec_add rd rs1 rs2 := by
  unfold sp1_add spec_add

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

  -- Correspondence between the original and newly written values
  have read_b := RTypeReader.read_b_fun _ rs1 adapter_cstrs hb1
  have read_c := RTypeReader.read_c_fun _ rs2 adapter_cstrs hb2

  -- Substitue the semantics of the underlying add operation
  rw [AddOperation.correct' Main[20] Main[21] M11_U16 M12_U16 M16_U16 M17_U16 add_cstrs]

  -- Simplify the final result
  simp [read_b, read_c, execute_RTYPE]
  rfl

end AddChip
