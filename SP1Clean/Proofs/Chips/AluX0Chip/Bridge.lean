import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.AluX0Chip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance
import RISCV.Instructions
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # Native Sail bridge for `AluX0` (ALU-into-`x0`) + `ChipKind`

`AluX0` validates an ALU instruction whose destination is `x0` (the hardwired-zero register): the result is
**discarded**. So the chip emulation `sp1_aluX0` is opcode-**independent** — it advances `nextPC = pc + 4`
and writes nothing (`sp1_loadX0`'s shape). The RISC-V Sail spec, by contrast, runs the real ALU instruction
with `rd = x0`; but every `execute_<family>` ends in `wX_bits rd result`, and `run_wX_bits` collapses a
write to `x0` (`rd = 0#5`) to a **no-op regardless of the result** (`Foundations/SailWrap.lean`). So
`spec_aluX0_<op> ≡ sp1_aluX0` for **every** covered ALU opcode by the same move — no `execute_*_pure =
RV64.*` result-correctness lemma is needed (the result is thrown away).

Hence five generic family-core lemmas — RTYPE (ADD/SUB/XOR/OR/AND/SLT/SLTU/SLL/SRL/SRA), RTYPEW
(ADDW/SUBW/SLLW/SRLW/SRAW), ITYPE (ADDI), MUL (MUL/MULH/MULHU/MULHSU), MULW — cover all 29 covered ALU (21 ALU + 8 DIV/REM-into-x0)
opcodes; `aluX0_chip_reaches_sail` is their 29-way conjunction. The register reads (`h_rs1`/`h_rs2`) are
needed only so the Sail reads *succeed* (their values are discarded). -/

open LeanRV64D.Defs
namespace SP1Clean.AluX0Sail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The SP1 chip emulation for ALU-into-`x0`: advance `nextPC = pc + 4` and write nothing (the result is
discarded, `wX 0` being a no-op). Opcode-independent — the same for all 29 covered ALU (21 ALU + 8 DIV/REM-into-x0) opcodes. -/
noncomputable def sp1_aluX0 (pc : BitVec 64) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)

/-! ## Family spec functions (the real Sail execution, `rd = x0`) -/

/-- RTYPE family (ADD/SUB/XOR/OR/AND/SLT/SLTU/SLL/SRL/SRA): advance `nextPC`, run `execute_RTYPE` into `x0`. -/
noncomputable def spec_aluX0_rtype (op : rop) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- RTYPEW family (ADDW/SUBW/SLLW/SRLW/SRAW): advance `nextPC`, run `execute_RTYPEW` into `x0`. -/
noncomputable def spec_aluX0_rtypew (op : ropw) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- ITYPE family (ADDI): advance `nextPC`, run `execute_ITYPE … iop.ADDI` into `x0`. -/
noncomputable def spec_aluX0_addi (imm : BitVec 12) (rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 (.Regidx 0#5) iop.ADDI
  pure ()

/-- The four `MUL` `mul_op` records (MUL/MULH/MULHU/MULHSU). -/
def mulOp_mul : mul_op := { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }
def mulOp_mulh : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
def mulOp_mulhu : mul_op := { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
def mulOp_mulhsu : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }

/-- MUL family (MUL/MULH/MULHU/MULHSU): advance `nextPC`, run `execute_MUL` into `x0`. -/
noncomputable def spec_aluX0_mul (op : mul_op) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- MULW: advance `nextPC`, run `execute_MULW` into `x0`. -/
noncomputable def spec_aluX0_mulw (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MULW rs2 rs1 (.Regidx 0#5)
  pure ()

/-! ## The five generic family-core lemmas (the no-op-write collapse) -/

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- RTYPE-into-`x0` ≡ `sp1_aluX0`: the `wX_bits 0#5` write is a no-op, so the (discarded) ALU result drops
out — generic in `op : rop`. The reads only need to succeed (`h_rs1`/`h_rs2`), values unused. -/
theorem correct_aluX0_rtype (op : rop) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_rtype op (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_rtype, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- RTYPEW-into-`x0` ≡ `sp1_aluX0` (generic in `op : ropw`). -/
theorem correct_aluX0_rtypew (op : ropw) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_rtypew op (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_rtypew, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW', h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- ADDI-into-`x0` ≡ `sp1_aluX0`. -/
theorem correct_aluX0_addi (imm : BitVec 12) (rs1 : BitVec 5) (rs1_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) :
    (spec_aluX0_addi imm (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_addi, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', h_rs1]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- MUL-into-`x0` ≡ `sp1_aluX0` (generic in `op : mul_op`), via `_root_.mul_eq`/`skeleton_binary`. -/
theorem correct_aluX0_mul (op : mul_op) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_mul op (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_mul, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [_root_.mul_eq, skeleton_binary, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- MULW-into-`x0` ≡ `sp1_aluX0`, via `_root_.mulw_eq`/`skeleton_binary`. -/
theorem correct_aluX0_mulw (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_mulw (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_mulw, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [_root_.mulw_eq, skeleton_binary, h_rs1, h_rs2]

/-- DIV family (DIV/DIVU): advance `nextPC`, run `execute_DIV` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_div (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- REM family (REM/REMU): advance `nextPC`, run `execute_REM` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_rem (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- DIVW family (DIVW/DIVUW): advance `nextPC`, run `execute_DIVW` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_divw (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- REMW family (REMW/REMUW): advance `nextPC`, run `execute_REMW` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_remw (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- DIV-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`), via `_root_.div_eq`/`skeleton_binary`. -/
theorem correct_aluX0_div (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_div is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_div, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [_root_.div_eq, skeleton_binary, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- REM-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`). -/
theorem correct_aluX0_rem (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_rem is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_rem, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  cases is_unsigned <;>
    simp [_root_.rem_signed_eq, _root_.rem_unsigned_eq, skeleton_binary, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- DIVW-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`), via `_root_.divw_eq`/`skeleton_binary`. -/
theorem correct_aluX0_divw (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_divw is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_divw, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [_root_.divw_eq, skeleton_binary, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- REMW-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`). -/
theorem correct_aluX0_remw (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_remw is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp only [spec_aluX0_remw, sp1_aluX0]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  cases is_unsigned <;>
    simp [_root_.remw_signed_eq, _root_.remw_unsigned_eq, skeleton_binary, h_rs1, h_rs2]

end SP1Clean.AluX0Sail

namespace SP1Clean.AluX0Chip

open SP1Clean.AluX0Sail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The AluX0 RowView (shared by `kind.view` and `advance`): straight-line `pc+4` next-pc, the
ALU-type adapter, the zero word as the (discarded) `x0` write, the dynamic `opcode` column,
`.noWrite` commit (rd = x0). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.AluX0Cols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, #v[(0 : ZMod p), 0, 0, 0], cols.opcode, .noWrite⟩

/-- **AluX0's advance-readiness bundle** (SC Phase 4).  Depends on `cols` only (no `inp` — the value is
discarded, so no reader-passthrough is needed).  The routing invariants the trace dispatcher supplies
beyond refinement + `Spec`: the destination is `x0` (`op_a = 0`, the dual of every register-writing
chip's `op_a ≠ 0`), the low-pc-limb bound, and — since AluX0's opcode is a single dynamic column (no
per-op flags) — the committed `(opcode, imm_c)` pair identifying WHICH of the 24 straight-line ALU ops
this row is (the decode's opcode↔imm_c correlation).  MUL/MULH/MULHU/MULHSU (11-14) and MULW (24) are
DELIBERATELY EXCLUDED — see the decode seam note below; their rows are not yet covered by AluX0.advance. -/
def advanceReady (cols : Extracted.AluX0Cols (ZMod p)) : Prop :=
  cols.adapter.op_a = 0 ∧ cols.state.pc[0].val < 2 ^ 16 ∧
  ( (cols.opcode = (Opcode.ADD.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.ADDI.toNat : ZMod p) ∧ cols.adapter.imm_c = 1) ∨
    (cols.opcode = (Opcode.SUB.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.XOR.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.OR.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.AND.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SLL.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SRL.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SRA.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SLT.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SLTU.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.DIV.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.DIVU.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.REM.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.REMU.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.ADDW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SUBW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SLLW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SRLW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.SRAW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.DIVW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.DIVUW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.REMW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.REMUW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.MULH.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.MULHU.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) ∨
    (cols.opcode = (Opcode.MULW.toNat : ZMod p) ∧ cols.adapter.imm_c = 0) )

set_option maxHeartbeats 4000000 in
/-- **`AluX0Chip.advance`** — the per-AluX0-row `try_step` lift (SC Phase 4), 24-way opcode dispatch
into the seven no-write family adapters.  `op_a = 0` (so `rd = x0`, the value discarded) and the low-pc
bound come from `advanceReady`; `himmb`/`hstraight` are `rfl` (the ALU-type `toAdapterView`).  Each
branch reads its `(opcode, imm_c)` off `advanceReady` and calls the matching
`advance_of_alu_x0_{rtype,rtypew,itype,div,rem,divw,remw}`.  This proof **is** `kind.advance` below —
stated to match the `ChipKind.advance` obligation exactly (`view := rowView`, `advanceReady := this`). -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.AluX0Cols (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (_hreal : (rowView inp cols).is_real = 1) (_hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : advanceReady cols) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hopa0, hpc0, hdisj⟩ := hready
  have himmb : (rowView inp cols).adapter.imm_b = 0 := rfl
  rcases hdisj with ⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩|⟨ho,hi⟩
  · exact advance_of_alu_x0_rtype rop.ADD hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_itype iop.ADDI hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SUB hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.XOR hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.OR hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.AND hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SLL hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SRL hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SRA hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SLT hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtype rop.SLTU hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_div false hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_div true hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rem false hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rem true hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtypew ropw.ADDW hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtypew ropw.SUBW hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtypew ropw.SLLW hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtypew ropw.SRLW hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_rtypew ropw.SRAW hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_divw false hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_divw true hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_remw false hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_remw true hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_mul mulOp_mulh
      (by rintro ⟨a, b, c⟩ hh; cases a <;> cases b <;> cases c <;> first | rfl | (exact absurd hh (by decide)))
      hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_mul mulOp_mulhu
      (by rintro ⟨a, b, c⟩ hh; cases a <;> cases b <;> cases c <;> first | rfl | (exact absurd hh (by decide)))
      hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl
  · exact advance_of_alu_x0_mulw hcfg hrom hpcread hvalb hdecrom ho himmb hi hopa0 hpc0 rfl rfl rfl

/-- `AluX0`'s `ChipKind` registration. `view.wr` is the zero word (`x0` discards the result);
`sailEquiv` is the 29-way Sail conjunction (all covered ALU opcodes into `x0`), discharged via the
five family-core lemmas. Register reads (`h_rs1`/`h_rs2`) are needed only to make Sail reads succeed.
`advance` (SC Phase 4) covers 27/29 — MUL(11) and MULHSU(14) remain the documented decode seam
(`mulOpToOpcode` is non-injective there, so the opcode can't pin the `mul_op` without `ext_decode`
output-determinism). -/
def kind : Soundness.ChipKind p where
  name := "AluX0"
  Inputs := AluX0Chip.Inputs
  Cols := Extracted.AluX0Cols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun _inp _cols s => ∀ (rs1 rs2 : BitVec 5) (imm : BitVec 12) (pc : BitVec 64)
      (rs1_val rs2_val : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some rs1_val →
    s.get_reg? rs2 = some rs2_val →
    ((spec_aluX0_rtype rop.ADD (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SUB (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.XOR (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.OR (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.AND (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SLT (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SLTU (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SLL (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SRL (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtype rop.SRA (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtypew ropw.ADDW (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtypew ropw.SUBW (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtypew ropw.SLLW (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtypew ropw.SRLW (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rtypew ropw.SRAW (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_addi imm (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_mul mulOp_mul (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_mul mulOp_mulh (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_mul mulOp_mulhu (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_mul mulOp_mulhsu (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_mulw (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_div false (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_div true (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rem false (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_rem true (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_divw false (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_divw true (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_remw false (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s) ∧
    ((spec_aluX0_remw true (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s)
  reaches_sail := fun _inp _cols _data s _h_real _h_chip rs1 rs2 imm pc rs1_val rs2_val
      h_pc h_rs1 h_rs2 =>
    ⟨correct_aluX0_rtype rop.ADD rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SUB rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.XOR rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.OR rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.AND rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SLT rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SLTU rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SLL rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SRL rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtype rop.SRA rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtypew ropw.ADDW rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtypew ropw.SUBW rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtypew ropw.SLLW rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtypew ropw.SRLW rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rtypew ropw.SRAW rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_addi imm rs1 rs1_val pc s h_pc h_rs1,
     correct_aluX0_mul mulOp_mul rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_mul mulOp_mulh rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_mul mulOp_mulhu rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_mul mulOp_mulhsu rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_mulw rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_div false rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_div true rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rem false rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_rem true rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_divw false rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_divw true rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_remw false rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2,
     correct_aluX0_remw true rs1 rs2 rs1_val rs2_val pc s h_pc h_rs1 h_rs2⟩
  advanceReady := fun _ cols _ _ => advanceReady cols
  advance := some (PLift.up advance)

end SP1Clean.AluX0Chip
