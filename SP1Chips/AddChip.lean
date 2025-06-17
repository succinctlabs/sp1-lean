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
      Main[3]
      0
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


theorem sp1_add_implies_spec_add
  (Main : Vector BabyBear 23)
  (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
  (h_is_real : Main[22] = 1)
  (rd rs1 rs2 : regidx)
  :
  let res := (sp1_add Main cstrs h_is_real rd rs1 rs2)
  let res_spec := (spec_add rd rs1 rs2)
  res = res_spec :=
  by
    simp [sp1_add, spec_add]

    -- simp only [constraints] at cstrs
    -- have add_constraints := AddOperation.constraints #v[Main[11], Main[12], Main[16], Main[17], Main[20], Main[21], Main[22]]
    -- have add_cstrs : constraintSet_toProp add_constraints := by _
    -- simp only [constraintSet_toProp] at cstrs
    -- simp only [AddOperation.constraints] at cstrs
    -- simp only [RTypeReader.constraints] at cstrs
    -- simp only [SP1Constraint.toProp] at cstrs
    -- simp [h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at cstrs

    simp only [constraints] at cstrs
    simp at cstrs
    let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
    clear cstrs

    simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
    simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at adapter_cstrs

    sorry

end Add
