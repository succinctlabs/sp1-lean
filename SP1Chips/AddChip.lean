import SP1Foundations
import SP1Operations.AddOperation
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs
import SP1Operations.CPUState
import SP1Operations.RTypeReader

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

structure AddChip where
  state : CPUState
  adapter : RTypeReader U16
  add_operation : AddOperation
  is_real : U1

namespace AddChip

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
  : Finset SP1Constraint :=
  let E0  : BabyBear := Main[22] - 1
  let E2  : BabyBear := Main[22] * E0
  let E4  : BabyBear := Main[3] + 4
  let E6  : BabyBear := 16384 * Main[1]
  let E8  : BabyBear := E6 + Main[2]
  let E10 : BabyBear := Main[22] - 1
  let E12 : BabyBear := Main[22] * E10
  let E14 : BabyBear := E8 + 4
  let E16 : BabyBear := 16384 * Main[1]
  let E18 : BabyBear := E16 + Main[2]
  let E20 : BabyBear := Main[22] - 1
  let E22 : BabyBear := Main[22] * E20
  let E24 : BabyBear := 0 + Main[10]
  let E26 : BabyBear := 0 + Main[15]
  let E28 : BabyBear := Main[20] - 0
  let E30 : BabyBear := Main[9] * E28
  let E32 : BabyBear := Main[21] - 0
  let E34 : BabyBear := Main[9] * E32
  let E36 : BabyBear := E18 + 3
  let E38 : BabyBear := Main[22] - 1
  let E40 : BabyBear := Main[22] * E38
  let E42 : BabyBear := E36 - Main[7]
  let E44 : BabyBear := E42 - 1
  let E46 : BabyBear := E44 - Main[8]
  let E48 : BabyBear := E46 * 2013143041
  let E50 : BabyBear := E18 + 2
  let E52 : BabyBear := Main[22] - 1
  let E54 : BabyBear := Main[22] * E52
  let E56 : BabyBear := E50 - Main[13]
  let E58 : BabyBear := E56 - 1
  let E60 : BabyBear := E58 - Main[14]
  let E62 : BabyBear := E60 * 2013143041
  let E64 : BabyBear := E18 + 1
  let E66 : BabyBear := Main[22] - 1
  let E68 : BabyBear := Main[22] * E66
  let E70 : BabyBear := E64 - Main[18]
  let E72 : BabyBear := E70 - 1
  let E74 : BabyBear := E72 - Main[19]
  let E76 : BabyBear := E74 * 2013143041
  {
    .assertZero E2,
    .assertZero E12,
    .receive (.state Main[0] E8 Main[3]) Main[22],
    .send (.state Main[0] E14 E4) Main[22],
    .send (.byte (ByteOpcode.ofNat 6) Main[1] 14 0) Main[22],
    .send (.byte (ByteOpcode.ofNat 6) Main[2] 14 0) Main[22],
    .assertZero E22,
    .assertZero E30,
    .assertZero E34,
    .assertZero E40,
    .send (.byte (ByteOpcode.ofNat 6) Main[8] 14 0) Main[22],
    .send (.byte (ByteOpcode.ofNat 6) E48 14 0) Main[22],
    .send (.memory Main[0] Main[7] Main[4] Main[5] Main[6]) Main[22],
    .receive (.memory Main[0] E36 Main[4] Main[20] Main[21]) Main[22],
    .assertZero E54,
    .send (.byte (ByteOpcode.ofNat 6) Main[14] 14 0) Main[22],
    .send (.byte (ByteOpcode.ofNat 6) E62 14 0) Main[22],
    .send (.memory Main[0] Main[13] Main[10] Main[11] Main[12]) Main[22],
    .receive (.memory Main[0] Main[5] Main[10] Main[11] Main[12]) Main[22],
    .assertZero E68,
    .send (.byte (ByteOpcode.ofNat 6) Main[19] 14 0) Main[22],
    .send (.byte (ByteOpcode.ofNat 6) E76 14 0) Main[22],
    .send (.memory Main[0] Main[18] Main[15] Main[16] Main[17]) Main[22],
    .receive (.memory Main[0] E64 Main[15] Main[16] Main[17]) Main[22]
  } ∪ AddOperation.constraints #v[Main[11], Main[12], Main[16], Main[17], Main[20], Main[21], Main[22]]

def spec
  (Main : Vector BabyBear 23)
  (cstrs : constraintSet_toProp (constraints Main))
  (h_is_real : Main[22] = 1)
  : SailM Unit :=
  by
    simp [constraints, constraintSet_toProp, h_is_real] at cstrs
    simp [ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at cstrs
    exact do
      pure ()

end AddChip

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

def sp1_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) : SailM Unit := do
    -- Model YOUR implementation's behavior
    writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
    /- let ⟨rs1_val, ⟨rs2_val, matching⟩⟩ ← chip.read rs1 rs2 -/
    let rs1_val ← rX_bits rs1
    let rs2_val ← rX_bits rs2
    /- let ⟨rs1_val, mem_read_1⟩ ← read_b -/
    /- let ⟨rs2_val, mem_read_2⟩ ← read_c -/
    /- let ⟨_, ⟨h_constraints_2, _⟩⟩ := constraints -/
    by
      /- let h_add := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real -/
      /- rw [←mem_read_1, ←mem_read_2] at h_add -/
      /- let res := chip.add_operation.value.toBV32_U16 -/
      exact wX_bits rd chip.add_operation.value.toBV32_U16

/- noncomputable -/ def spec_add (rd rs1 rs2 : regidx) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  /- let _ ← execute (.RTYPE ⟨rs2, rs1, rd, rop.ADD⟩) -/ -- `execute` is uncomputable...?
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx) (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) (s : PreSail.SequentialState RegisterType trivialChoiceSource) :
  let res := (sp1_add chip constraints h_is_real rd rs1 rs2 read_b read_c).run s
  let res_spec := (spec_add rd rs1 rs2).run s
  res = res_spec :=
  by
    simp [EStateM.run]
    simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]
    let add_spec := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real
    simp [RTypeReader.read_b_fun] at read_b
    rw [read_b]
    simp [RTypeReader.read_c_fun] at read_c
    rw [read_c]
    rw [←add_spec]
    rw [pure_bind, pure_bind]
    rfl

theorem sp1_add_implies_spec_add' (chip : AddChip) (constraints : chip.constraints) (h_is_real : chip.is_real = 1) (rd rs1 rs2 : regidx)
    (read_b : chip.adapter.read_b_fun rs1) (read_c : chip.adapter.read_c_fun rs2) :
  let res := (sp1_add chip constraints h_is_real rd rs1 rs2 read_b read_c)
  let res_spec := (spec_add rd rs1 rs2)
  res = res_spec :=
  by
    refine EStateM.ext fun s => ?_
    simp [EStateM.run]

    simp [sp1_add, spec_add, /- execute, -/ execute_RTYPE]

    let add_spec := (chip.add_operation.correct chip.adapter.b chip.adapter.c chip.is_real constraints.right.left) h_is_real
    simp [RTypeReader.read_b_fun] at read_b
    rw [read_b]
    simp [RTypeReader.read_c_fun] at read_c
    rw [read_c]
    rw [←add_spec]
    rw [pure_bind, pure_bind]
    rfl
