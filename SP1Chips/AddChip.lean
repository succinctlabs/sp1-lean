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

-- Add below imports to the top of the file
/- import LeanRV32D.RiscvInstsEnd -/
/- import LeanRV32D.RiscvRegs -/

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

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
