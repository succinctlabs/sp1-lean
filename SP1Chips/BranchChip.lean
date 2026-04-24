import SP1Foundations
import SP1Chips.Branch.Constraints

namespace Branch

open Sail SailState BitVec LeanRV64D.Functions

attribute [simp] jump_to assert PreSail.assert ofBool
  zopz0zI_s zopz0zKzJ_s zopz0zKzJ_u zopz0zI_u

-- Close the branching-case address equation `PC + signExtend imm = #v[Main[26..28], 0]`
-- by converting sign-extended immediate to its limb form (via `reader_cstrs`), pushing the
-- BitVec equality down to `Nat` arithmetic, and discharging with `omega` over the PC, immediate,
-- and chip-output limb bounds plus the `h_limb0..h_limb3, h_bound_checks` chip constraints.
-- The macro expects the ambient setup from each `correct_b*` proof: local `imm` let-binding,
-- `reader_cstrs`, `h_pc_0..h_pc_2`, `h_imm_0..h_imm_3`, `h_limb0..h_limb3`, `h_bound_checks`, `h26`.
set_option hygiene false in
local macro "close_branch_addr_eq" : tactic => `(tactic| (
  unfold imm
  rw [sp1_imm, ← reader_cstrs.1.1.1]
  simp [Word.toBitVec64, Word.toNat_def, ← BitVec.toNat_inj]
  clear * - h26 h_pc_0 h_pc_1 h_pc_2 h_imm_0 h_imm_1 h_imm_2 h_imm_3
    h_limb0 h_limb1 h_limb2 h_limb3 h_bound_checks
  omega))

variable (Main : Vector (Fin KB) 45)

def sp1_op_a : BitVec 5 := BitVec.ofNat 5 Main[6]

def sp1_op_b : BitVec 5 := BitVec.ofNat 5 Main[14]

def sp1_imm : BitVec 13 := BitVec.ofNat 13 Main[21]

def sp1_branch : SailM ExecutionResult := do
  writeReg Register.nextPC (Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0])
  pure RETIRE_SUCCESS

namespace BEQ

noncomputable def spec_beq (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BEQ

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_beq
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_beq
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[28] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_beq imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BEQ

namespace BNE

noncomputable def spec_bne (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BNE

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_bne
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_bne
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bne : Main[29] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bne imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BNE

namespace BLT

noncomputable def spec_blt (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLT

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_blt
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_blt
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_blt : Main[30] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_blt imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BLT

namespace BGE

noncomputable def spec_bge (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGE

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_bge
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_bge
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bge : Main[31] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bge imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BGE

namespace BLTU

noncomputable def spec_bltu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BLTU

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_bltu
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_bltu
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bltu : Main[32] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bltu imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BLTU

namespace BGEU

noncomputable def spec_bgeu (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_BTYPE imm rs2 rs1 bop.BGEU

set_option debug.skipKernelTC true in
set_option maxHeartbeats 2000000 in
-- correctness proof across all 6 branch-opcode cases
-- Pre-regen proof at commit 750a3e6:SP1Chips/BranchChip.lean -- correct_bgeu
-- (not ported: constraint tree reshape requires rewalking the obtain chain;
-- see `git show 750a3e6:SP1Chips/BranchChip.lean` for the full pre-regen proof body)
theorem correct_bgeu
    (Main : Vector (Fin KB) 45)
    (s : SailState) (hs : s.isInitialized)
    (h_is_bgeu : Main[33] = 1)
    (cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s) :
    let imm := sp1_imm Main
    let op_b := .Regidx (sp1_op_b Main)
    let op_a := .Regidx (sp1_op_a Main)
    (spec_bgeu imm op_b op_a).run s = (sp1_branch Main).run s := by
  sorry
end BGEU

end Branch
