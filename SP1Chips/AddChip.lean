import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace AddChip

def constraints
  (Main : Vector BabyBear 23)
  : List SP1Constraint :=
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
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  linarith

def sp1_add
    (Main : Vector BabyBear 23)
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
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
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (h_is_real : Main[22] = 1) (rd rs1 rs2 : regidx) :
    sp1_add Main cstrs h_is_real rd rs1 rs2 = spec_add rd rs1 rs2 := by
  unfold sp1_add spec_add
  simp only [sp1_add, spec_add]
  -- Extract the various constraints from the assumption
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  clear cstrs

  have read_b : RTypeReader.registerMatch rs1 Main[11] Main[12] :=
    RTypeReader.read_b_fun _ _ adapter_cstrs
  have read_c : RTypeReader.registerMatch rs2 Main[16] Main[17] :=
    RTypeReader.read_c_fun _ _ adapter_cstrs

  simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at adapter_cstrs
  simp [SP1Constraint.toProp, sub_eq_zero] at orig_cstrs

  let M11_U16 : U16 := ⟨Main[11], adapter_cstrs.right.right.right.right.right.right.right.left.left⟩
  let M12_U16 : U16 := ⟨Main[12], adapter_cstrs.right.right.right.right.right.right.right.left.right⟩
  let M16_U16 : U16 := ⟨Main[16], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.left⟩
  let M17_U16 : U16 := ⟨Main[17], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.right⟩
  let M20_U16 : U16 := ⟨Main[20], adapter_cstrs.right.right.right.right.left.left⟩
  let M21_U16 : U16 := ⟨Main[21], adapter_cstrs.right.right.right.right.left.right⟩
  let M22_U1  : U1  := ⟨Main[22], by clear * - orig_cstrs; aesop⟩

  let add_spec := AddOperation.correct M20_U16 M21_U16 M11_U16 M12_U16 M16_U16 M17_U16 M22_U1 add_cstrs
  simp only [AddOperation.spec] at add_spec

  have res_eq_bv_add := add_spec (by clear * - h_is_real; aesop)
  simp [BitVec.ofU16] at res_eq_bv_add
  rw [res_eq_bv_add]

  simp only [execute_RTYPE, Nat.reducePow, Nat.reduceMul, bind_pure_comp, bind_assoc,
    bind_map_left, map_bind, Functor.map_map, id_map']

  specialize read_b (by
    have := M11_U16.in_range
    have := M12_U16.in_range
    linarith)
  specialize read_c (by
    have := M16_U16.in_range
    have := M17_U16.in_range
    linarith
  )
  simp [read_b, read_c]

  rfl

end AddChip
