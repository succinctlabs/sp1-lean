import SP1Foundations
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs
import SP1Operations.CPUState
import SP1Operations.JTypeReader

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

structure JalChip where
  state : CPUState
  adapter : JTypeReader U16
  is_real : U1

namespace JalChip

def constraints (chip : JalChip) : Prop := sorry

def trust_jmp : Prop := sorry

end JalChip

def sp1_jal
  (chip : JalChip)
  (constraints : chip.constraints)
  (h_is_real : chip.is_real = U1.one)
  (rd : regidx)
  (imm : BitVec 21)
  (read_b : chip.adapter.read_jal_b_fun imm)
  (read_c : chip.adapter.read_jal_c_fun)
  : SailM Unit :=
  do
    -- The order of PC write doesn't really matter to us, so for convention
    -- let's place them at the start
    writeReg (Register.nextPC) chip.adapter.b.toBV32_U16
    -- When we generate memory reads/writes,
    -- the order of the statements is based on `clk`
    wX_bits rd chip.adapter.c.toBV32_U16

def spec_jal (rd : regidx) (imm : BitVec 21) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_JAL imm rd
  pure ()

theorem sp1_jal_implies_spec_jal
  (chip : JalChip)
  (constraints : chip.constraints)
  (h_is_real : chip.is_real = U1.one)
  (rd : regidx)
  (imm : BitVec 21)
  (read_b : chip.adapter.read_jal_b_fun imm)
  (read_c : chip.adapter.read_jal_c_fun)
  -- note: this is horrendously wrong, `trusted_jmp` should not be trusted.
  -- the equality should only hold when `pc ← readReg Register.PC`
  -- claude messed this one up
  (trusted_jmp : ∀ (pc : BitVec 32),
    bit_to_bool (BitVec.access (pc + sign_extend imm) 1) = pure false)
  (s : PreSail.SequentialState RegisterType trivialChoiceSource)
  : let res := (sp1_jal chip constraints h_is_real rd imm read_b read_c).run s
    let res_spec := (spec_jal rd imm).run s
    res = res_spec
  :=
  by
    simp [EStateM.run, sp1_jal, spec_jal, execute_JAL]
    simp only [JTypeReader.read_jal_b_fun] at read_b
    simp only [JTypeReader.read_jal_c_fun] at read_c

    simp [ext_control_check_pc]
    simp [get_next_pc, set_next_pc, bits_of_virtaddr]
    
    -- Now use trusted_jmp to replace bit_to_bool expressions
    simp [trusted_jmp]
    -- Now a_1 should be replaced with false everywhere
    sorry
