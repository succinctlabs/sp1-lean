import SP1Foundations
import SP1Operations.AddOperation
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs
import SP1Operations.CPUState
import SP1Operations.RTypeReader

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

namespace Add

/- -- What we expect the generated constraint to look like: -/
/- def constraints -/
/-   (chip : AddChip) : Prop := -/
/-   let ⟨state, adapter, add_operation, is_real⟩ := chip -/
/-   state.spec (state.pc + 4) 4 is_real -/
/-   ∧ constraintSet_toProp (add_operation.constraints adapter.b adapter.c is_real) -/
/-   ∧ adapter.spec state.shard state.clk state.pc 0 /- Opcode::ADD -/ add_operation.value is_real -/

/- def read  -/
/-   (chip : AddChip) -/
/-   (rs1 rs2 : regidx) : SailM (BitVec 32 × BitVec 32 × (rs1_val = chip.adapter.b.toBV32_U16 ∧ rs2_val = chip.adapter.c.toBV32_U16)) := do -/
/-     let rs1_val ← rx_bits rs1 -/
/-     let rs2_val ← rx_bits rs2 -/
/-     pure -/
/-       ⟨rs1_val, -/
/-         ⟨rs2_val, -/
/-         sorry -/
/-         ⟩ -/
/-       ⟩ -/

def readerConstraints (Main : Vector BabyBear 23) :
    List SP1Constraint :=
  let E0 : BabyBear := Main[22] - 1
  let E2 : BabyBear := Main[22] * E0
  let E4 : BabyBear := Main[3] + 4
  let E6 : BabyBear := 16384 * Main[1]
  let E8 : BabyBear := E6 + Main[2]
  (RTypeReader.constraints
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
    ++ readerConstraints Main


def sp1_add
  (Main : Vector BabyBear 23)
  (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
  (h_is_real : Main[22] = 1)
  (rd rs1 rs2 : regidx)
  : SailM Unit :=
  let pf : Main[20].val + Main[21].val * 65536 < 2^32 :=
    by
      simp only [constraints] at cstrs
      simp at cstrs
      let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
      clear cstrs
      simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
      have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
      have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
      linarith
  do
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    let rs1_value ← rX_bits rs1
    let rs2_value ← rX_bits rs2
    wX_bits rd (BitVec.ofNatLT (Main[20].val + Main[21].val * 65536) pf)

/- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

def registerMatch (rx : regidx) (x y : BabyBear) : Prop :=
  ∀ (pf : (x.val + y.val * 65536) < 2 ^ 32),
    rX_bits rx = pure (BitVec.ofNatLT (x.val + y.val * 65536) pf)

-- def RTypeReader.registerMatch  : Prop :=
--   ∀ (pf : (x.val + y.val * 65536) < 2 ^ 32),
--     rX_bits rx = pure (BitVec.ofNatLT (x.val + y.val * 65536) pf)

lemma rTypeReader_constraints_of_constraints
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main)) :
    List.Forall SP1Constraint.toProp (readerConstraints Main) := by
  sorry

theorem sp1_add_implies_spec_add
  (Main : Vector BabyBear 23)
  (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
  (h_is_real : Main[22] = 1)
  (rd rs1 rs2 : regidx)
  (read_b_old : registerMatch rs1 Main[11] Main[12])
  -- have hread_b := rTypeReader_constraints_of_constraints cstrs
  (read_b : RTypeReader.read_b_fun (rTypeReader_constraints_of_constraints cstrs) h_is_real rs1)
  (read_c : registerMatch rs2 Main[16] Main[17])
  :
  let res := (sp1_add Main cstrs h_is_real rd rs1 rs2)
  let res_spec := (spec_add rd rs1 rs2)

  res = res_spec :=
  by
    simp [sp1_add, spec_add]

    simp [constraints] at cstrs
    let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
    clear cstrs

    simp [RTypeReader.read_b_fun] at read_b
    -- simp [registerMatch]
    -- rw? at read_b

    let add_cstrs_folded := add_cstrs
    simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
    simp [readerConstraints, RTypeReader.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at adapter_cstrs
    simp [SP1Constraint.toProp, sub_eq_zero] at orig_cstrs

    let M11_U16 : U16 := ⟨Main[11], by aesop⟩
    let M12_U16 : U16 := ⟨Main[12], adapter_cstrs.right.right.right.right.right.right.right.left.right⟩
    let M16_U16 : U16 := ⟨Main[16], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.left⟩
    let M17_U16 : U16 := ⟨Main[17], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.right⟩
    let M20_U16 : U16 := ⟨Main[20], adapter_cstrs.right.right.right.right.left.left⟩
    let M21_U16 : U16 := ⟨Main[21], adapter_cstrs.right.right.right.right.left.right⟩
    let M22_U1  : U1  := ⟨Main[22], by clear * - orig_cstrs; aesop⟩

    let add_spec := AddOperation.correct M20_U16 M21_U16 M11_U16 M12_U16 M16_U16 M17_U16 M22_U1 add_cstrs_folded
    simp only [AddOperation.spec] at add_spec

    have res_eq_bv_add := add_spec (by clear * - h_is_real; aesop)
    simp [BitVec.ofU16] at res_eq_bv_add
    rw [res_eq_bv_add]

    clear res_eq_bv_add add_spec

    simp [execute_RTYPE]

    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    specialize read_b_old (by
      have := M11_U16.in_range
      have := M12_U16.in_range
      linarith)
    specialize read_b

    specialize read_c (by
      have := M16_U16.in_range
      have := M17_U16.in_range
      linarith
    )


    simp [read_b_old, read_c]
    rfl

end Add
