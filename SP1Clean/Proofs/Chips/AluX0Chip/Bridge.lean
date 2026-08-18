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
write to `x0` (`rd = 0#5`) to a **no-op regardless of the result** (`Model/SailWrap.lean`). So
`spec_aluX0_<op> ≡ sp1_aluX0` for **every** covered ALU opcode by the same move — no `execute_*_pure =
RV64.*` result-correctness lemma is needed (the result is thrown away).

The bridge dispatches through the verification-key-bound Program row, rather than duplicating Rust's
dynamic-opcode table as a Lean disjunction. The chip's byte lookup proves `opcode < 29`; the Program
projection then identifies one of the official Core ALU instruction families, including every immediate
and word-immediate form supported by SP1 v6.4.0. Source-register facts are needed only so the Sail reads
succeed; their values are discarded. -/

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
def rowView (inp : Inputs (ZMod p)) (cols : AluX0Chip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, #v[(0 : ZMod p), 0, 0, 0], cols.opcode, .noWrite⟩

/-- **AluX0's advance-readiness bundle.** The destination and PC facts are global routing inputs.
The dynamic-opcode range is proved locally by the chip's Byte-table lookup and passed through the
grounding contract. Its correlation with `imm_c` comes from the committed Program row itself; keeping
that correlation out of this predicate avoids a second hand-maintained instruction table. -/
def advanceReady (cols : AluX0Chip.Columns (ZMod p)) : Prop :=
  cols.adapter.op_a = 0 ∧ cols.state.pc[0].val < 2 ^ 16 ∧
  cols.opcode.val < 29

/-- **`AluX0Chip.advance`** — the per-row Sail lift. `op_a = 0` (hence `rd = x0`) and the low-PC
bound come from `advanceReady`; the chip's locally proved range fact selects the Core ALU portion of
the Program projection. `advance_of_alu_x0_program` performs the constructor-level dispatch, including
register, immediate, word, multiplication, and division/remainder families. -/
theorem advance (inp : Inputs (ZMod p)) (cols : AluX0Chip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (_hreal : (rowView inp cols).is_real = 1) (_hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : advanceReady cols) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hopa0, hpc0, hopcode⟩ := hready
  exact advance_of_alu_x0_program hcfg hrom hpcread hvalb hdecrom hopcode rfl
    hopa0 hpc0 rfl rfl rfl

/-- `AluX0`'s `ChipKind` registration. `view.wr` is the zero word (`x0` discards the result).
`advance` covers the complete v6.4.0 Core ALU range through the committed Program projection; source
register facts are needed only to make the corresponding Sail reads succeed. -/
def kind : Soundness.ChipKind p where
  name := "AluX0"
  Inputs := AluX0Chip.Inputs
  Cols := AluX0Chip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun _ cols _ _ => advanceReady cols
  advance := some (PLift.up advance)

end SP1Clean.AluX0Chip
