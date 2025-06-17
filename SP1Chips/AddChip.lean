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

<<<<<<< HEAD
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
=======
-- Add below imports to the top of the file
/- import LeanRV32D.RiscvInstsEnd -/
/- import LeanRV32D.RiscvRegs -/
>>>>>>> 997c41403074de8dd357722fd646b205687876b6

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

<<<<<<< HEAD
/-
Constraints for chip Add (main):
   Expr(0) = Main(22) - 1
   Expr(2) = Main(22) * Expr(0)
   Assert(Expr(2) == 0)
   AddOperation(Word(Main(11), Main(12)), Word(Main(16), Main(17)), AddOperation { value: Word([IrVar(Main(20)), IrVar(Main(21))]) }, Main(22))
   Expr(4) = Main(3) + 4
   Expr(6) = 16384 * Main(1)
   Expr(8) = Expr(6) + Main(2)
   Expr(10) = Main(22) - 1
   Expr(12) = Main(22) * Expr(10)
   Assert(Expr(12) == 0)
   Receive(multiplicity: Main(22), scope: Local, values: [Main(0), Expr(8), Main(3)])
   Expr(14) = Expr(8) + 4
   Send(multiplicity: Main(22), scope: Local, values: [Main(0), Expr(14), Expr(4)])
   Send(multiplicity: Main(22), scope: Local, values: [6, Main(1), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [6, Main(2), 14, 0])
   Expr(16) = 16384 * Main(1)
   Expr(18) = Expr(16) + Main(2)
   Expr(20) = Main(22) - 1
   Expr(22) = Main(22) * Expr(20)
   Assert(Expr(22) == 0)
   Expr(24) = 0 + Main(10)
   Expr(26) = 0 + Main(15)
   Send(multiplicity: Main(22), scope: Local, values: [Main(3), 0, Main(4), Expr(24), 0, Expr(26), 0, Main(9), 0, 0])
   Expr(28) = Main(20) - 0
   Expr(30) = Main(9) * Expr(28)
   Assert(Expr(30) == 0)
   Expr(32) = Main(21) - 0
   Expr(34) = Main(9) * Expr(32)
   Assert(Expr(34) == 0)
   Expr(36) = Expr(18) + 3
   Expr(38) = Main(22) - 1
   Expr(40) = Main(22) * Expr(38)
   Assert(Expr(40) == 0)
   Expr(42) = Expr(36) - Main(7)
   Expr(44) = Expr(42) - 1
   Expr(46) = Expr(44) - Main(8)
   Expr(48) = Expr(46) * 2013143041
   Send(multiplicity: Main(22), scope: Local, values: [6, Main(8), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [6, Expr(48), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [Main(0), Main(7), Main(4), Main(5), Main(6)])
   Receive(multiplicity: Main(22), scope: Local, values: [Main(0), Expr(36), Main(4), Main(20), Main(21)])
   Expr(50) = Expr(18) + 2
   Expr(52) = Main(22) - 1
   Expr(54) = Main(22) * Expr(52)
   Assert(Expr(54) == 0)
   Expr(56) = Expr(50) - Main(13)
   Expr(58) = Expr(56) - 1
   Expr(60) = Expr(58) - Main(14)
   Expr(62) = Expr(60) * 2013143041
   Send(multiplicity: Main(22), scope: Local, values: [6, Main(14), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [6, Expr(62), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [Main(0), Main(13), Main(10), Main(11), Main(12)])
   Receive(multiplicity: Main(22), scope: Local, values: [Main(0), Expr(50), Main(10), Main(11), Main(12)])
   Expr(64) = Expr(18) + 1
   Expr(66) = Main(22) - 1
   Expr(68) = Main(22) * Expr(66)
   Assert(Expr(68) == 0)
   Expr(70) = Expr(64) - Main(18)
   Expr(72) = Expr(70) - 1
   Expr(74) = Expr(72) - Main(19)
   Expr(76) = Expr(74) * 2013143041
   Send(multiplicity: Main(22), scope: Local, values: [6, Main(19), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [6, Expr(76), 14, 0])
   Send(multiplicity: Main(22), scope: Local, values: [Main(0), Main(18), Main(15), Main(16), Main(17)])
   Receive(multiplicity: Main(22), scope: Local, values: [Main(0), Expr(64), Main(15), Main(16), Main(17)])

AddOperation
Func(AddOperation(Word(Input(0), Input(1)), Word(Input(2), Input(3)), AddOperation { value: Word([IrVar(InputArg(4)), IrVar(InputArg(5))]) }, Input(6))
)
{
    Expr(0) = Input(6) - 1
    Expr(2) = Input(6) * Expr(0)
    Assert(Expr(2) == 0)
    Expr(4) = Input(0) + Input(2)
    Expr(6) = Expr(4) - Input(4)
    Expr(8) = Expr(6) + 0
    Expr(10) = Expr(8) * 2013235201
    Expr(12) = Expr(10) - 1
    Expr(14) = Expr(10) * Expr(12)
    Expr(16) = Input(6) * Expr(14)
    Assert(Expr(16) == 0)
    Expr(18) = Input(1) + Input(3)
    Expr(20) = Expr(18) - Input(5)
    Expr(22) = Expr(20) + Expr(10)
    Expr(24) = Expr(22) * 2013235201
    Expr(26) = Expr(24) - 1
    Expr(28) = Expr(24) * Expr(26)
    Expr(30) = Input(6) * Expr(28)
    Assert(Expr(30) == 0)
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(4), 16, 0])
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(5), 16, 0])
}

{
    let Expr(0) := Input(6) - 1
    Expr(2) = Input(6) * Expr(0)
    .AssertZero(Expr(2) == 0)
    let Expr(4) := Input(0) + Input(2)
    Expr(6) = Expr(4) - Input(4)
    Expr(8) = Expr(6) + 0
    Expr(10) = Expr(8) * 2013235201
    Expr(12) = Expr(10) - 1
    Expr(14) = Expr(10) * Expr(12)
    Expr(16) = Input(6) * Expr(14)
    Assert(Expr(16) == 0)
    Expr(18) = Input(1) + Input(3)
    Expr(20) = Expr(18) - Input(5)
    Expr(22) = Expr(20) + Expr(10)
    Expr(24) = Expr(22) * 2013235201
    Expr(26) = Expr(24) - 1
    Expr(28) = Expr(24) * Expr(26)
    Expr(30) = Input(6) * Expr(28)
    Assert(Expr(30) == 0)
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(4), 16, 0])
    Send(multiplicity: Input(6), scope: Local, values: [6, Input(5), 16, 0])
}
-/

-- def sp1_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) : SailM Unit := do
--     -- Model YOUR implementation's behavior
--     writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--     /- let ⟨rs1_val, ⟨rs2_val, matching⟩⟩ ← chip.read rs1 rs2 -/
--     let rs1_val ← rX_bits rs1
--     let rs2_val ← rX_bits rs2
--     /- let ⟨rs1_val, mem_read_1⟩ ← read_b -/
--     /- let ⟨rs2_val, mem_read_2⟩ ← read_c -/
--     /- let ⟨_, ⟨h_constraints_2, _⟩⟩ := constraints -/
--     by
--       /- let h_add := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real -/
--       /- rw [←mem_read_1, ←mem_read_2] at h_add -/
--       /- let res := chip.add_operation.value.toBV32_U16 -/
--       exact wX_bits rd chip.add_operation.value.toBV32_U16
-- 
-- /- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
--   writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
--   /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
--   let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
--   pure ()
-- 
-- theorem sp1_add_implies_spec_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) (s : PreSail.SequentialState RegisterType trivialChoiceSource) :
--   let res := (sp1_add chip constraints h_is_real rd rs1 rs2 read_b read_c).run s
--   let res_spec := (spec_add rd rs1 rs2).run s
--   res = res_spec :=
--   by
--     simp [EStateM.run]
--     simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
--     let add_spec := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real
--     simp [RTypeReader.read_b_fun] at read_b
--     rw [read_b]
--     simp [RTypeReader.read_c_fun] at read_c
--     rw [read_c]
--     rw [←add_spec]
--     rw [pure_bind, pure_bind]
--     rfl
-- 
-- theorem sp1_add_implies_spec_add' (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx)
--     (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) :
--   let res := (sp1_add chip constraints h_is_real rd rs1 rs2 read_b read_c)
--   let res_spec := (spec_add rd rs1 rs2)
--   res = res_spec :=
--   by
--     refine EStateM.ext fun s => ?_
--     simp [EStateM.run]
-- 
--     simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
-- 
--     let add_spec := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real
--     simp [RTypeReader.read_b_fun] at read_b
--     rw [read_b]
--     simp [RTypeReader.read_c_fun] at read_c
--     rw [read_c]
--     rw [←add_spec]
--     rw [pure_bind, pure_bind]
--     rfl
=======
open AddOperation

def AddChipConstraints
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Finset SP1Constraint :=
  AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6

def sp1_add
  -- All the columns used for `AddChip` (currently includes only those from `add_operation`)
  (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear)
  (constraints :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
  -- the following 4 proofs will come from the spec/constraints of `RTypeReader`
  -- adding in manually for now
  (read_b0_constraint : Input0.val < 65536)
  (read_b1_constraint : Input1.val < 65536)
  (read_c0_constraint : Input2.val < 65536)
  (read_c1_constraint : Input3.val < 65536)
  -- ensures this is not a padding row (we're actually running the instruction)
  (h' : Input6 ≠ 0)
  -- registers to read/write
  (rd rs1 rs2 : regidx)
  : SailM Unit :=
  -- the human part of the code generation is to fill out the `pf`s
  let Input0 : U16 := ⟨Input0, read_b0_constraint⟩
  let Input1 : U16 := ⟨Input1, read_b1_constraint⟩
  let Input2 : U16 := ⟨Input2, read_c0_constraint⟩
  let Input3 : U16 := ⟨Input3, read_c1_constraint⟩
  let hh :=
    AddOperationSpec_of_AddOperationConstraintSet Input0 Input1 Input2 Input3 _ _ _ constraints
  let pf : Input4.val + Input5.val * 65536 < 2^32 := by
    have ⟨hb, ⟨hc, _⟩⟩ := (hh.right h')
    omega

  -- below will be auto-generated
  do
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    let _ ← rX_bits rs1
    let _ ← rX_bits rs2
    -- at code-gen time, we don't know whether `Input4 + Input5 * 65536` will
    -- be in `u32` range, so we leave a placeholder for us to manually
    -- fill in
    wX_bits rd (BitVec.ofNatLT (Input4.val + Input5.val * 65536) pf)

/- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add
  (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear)
  (constraints :
    constraintSet_toProp (AddOperationConstraints Input0 Input1 Input2 Input3 Input4 Input5 Input6))
  -- the following 4 proofs will come from the spec/constraints of `RTypeReader`
  -- adding in manually for now
  (read_b0_constraint : Input0.val < 65536)
  (read_b1_constraint : Input1.val < 65536)
  (read_c0_constraint : Input2.val < 65536)
  (read_c1_constraint : Input3.val < 65536)
  -- ensures this is not a padding row (we're actually running the instruction)
  (h_is_real : Input6 ≠ 0)
  (rd rs1 rs2 : regidx)
  (read_b_fun : rX_bits rs1 = pure (BitVec.ofU16 ⟨Input0, read_b0_constraint⟩ ⟨Input1, read_b1_constraint⟩))
  (read_c_fun : rX_bits rs2 = pure (BitVec.ofU16 ⟨Input2, read_c0_constraint⟩ ⟨Input3, read_c1_constraint⟩))
  (s : PreSail.SequentialState RegisterType trivialChoiceSource)
  : let res := (sp1_add _ _ _ _ _ _ _ constraints read_b0_constraint read_b1_constraint read_c0_constraint read_c1_constraint h_is_real rd rs1 rs2).run s
    let res_spec := (spec_add rd rs1 rs2).run s
  res = res_spec :=
  by
    let Input0 : U16 := ⟨Input0, read_b0_constraint⟩
    let Input1 : U16 := ⟨Input1, read_b1_constraint⟩
    let Input2 : U16 := ⟨Input2, read_c0_constraint⟩
    let Input3 : U16 := ⟨Input3, read_c1_constraint⟩
    simp [EStateM.run]
    simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
    let h_bv :=
      AddOperation.bitVecAdd_of_addOperationConstraintSet
        (Input0 := Input0)
        (Input1 := Input1)
        (Input2 := Input2)
        (Input3 := Input3)
        constraints
        h_is_real
    rw [←h_bv]
    rw [read_b_fun, read_c_fun]
    clear h_bv read_b_fun read_c_fun
    rw [pure_bind, pure_bind]
    rfl

end Add
>>>>>>> 997c41403074de8dd357722fd646b205687876b6
