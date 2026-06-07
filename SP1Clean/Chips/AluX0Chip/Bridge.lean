import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.AluX0Chip.Formal
import SP1Clean.Soundness.ChipRow
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

namespace SP1Clean.AluX0Sail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The SP1 chip emulation for ALU-into-`x0`: advance `nextPC = pc + 4` and write nothing (the result is
discarded, `wX 0` being a no-op). Opcode-independent — the same for all 29 covered ALU (21 ALU + 8 DIV/REM-into-x0) opcodes. -/
noncomputable def sp1_aluX0 (pc : BitVec 64) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)

/-! ## Family spec functions (the real Sail execution, `rd = x0`) -/

/-- RTYPE family (ADD/SUB/XOR/OR/AND/SLT/SLTU/SLL/SRL/SRA): advance `nextPC`, run `execute_RTYPE` into `x0`. -/
noncomputable def spec_aluX0_rtype (op : rop) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- RTYPEW family (ADDW/SUBW/SLLW/SRLW/SRAW): advance `nextPC`, run `execute_RTYPEW` into `x0`. -/
noncomputable def spec_aluX0_rtypew (op : ropw) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- ITYPE family (ADDI): advance `nextPC`, run `execute_ITYPE … iop.ADDI` into `x0`. -/
noncomputable def spec_aluX0_addi (imm : BitVec 12) (rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 (.Regidx 0#5) iop.ADDI
  pure ()

/-- The four `MUL` `mul_op` records (MUL/MULH/MULHU/MULHSU). -/
def mulOp_mul : mul_op := { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }
def mulOp_mulh : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
def mulOp_mulhu : mul_op := { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
def mulOp_mulhsu : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }

/-- MUL family (MUL/MULH/MULHU/MULHSU): advance `nextPC`, run `execute_MUL` into `x0`. -/
noncomputable def spec_aluX0_mul (op : mul_op) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 (.Regidx 0#5) op
  pure ()

/-- MULW: advance `nextPC`, run `execute_MULW` into `x0`. -/
noncomputable def spec_aluX0_mulw (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
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
  simp [spec_aluX0_rtype, sp1_aluX0, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- RTYPEW-into-`x0` ≡ `sp1_aluX0` (generic in `op : ropw`). -/
theorem correct_aluX0_rtypew (op : ropw) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_rtypew op (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp [spec_aluX0_rtypew, sp1_aluX0, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW',
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- ADDI-into-`x0` ≡ `sp1_aluX0`. -/
theorem correct_aluX0_addi (imm : BitVec 12) (rs1 : BitVec 5) (rs1_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) :
    (spec_aluX0_addi imm (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp [spec_aluX0_addi, sp1_aluX0, execute_ITYPE,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- MUL-into-`x0` ≡ `sp1_aluX0` (generic in `op : mul_op`), via `_root_.mul_eq`/`skeleton_binary`. -/
theorem correct_aluX0_mul (op : mul_op) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_mul op (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp [spec_aluX0_mul, sp1_aluX0, _root_.mul_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- MULW-into-`x0` ≡ `sp1_aluX0`, via `_root_.mulw_eq`/`skeleton_binary`. -/
theorem correct_aluX0_mulw (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_mulw (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp [spec_aluX0_mulw, sp1_aluX0, _root_.mulw_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

/-- DIV family (DIV/DIVU): advance `nextPC`, run `execute_DIV` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_div (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- REM family (REM/REMU): advance `nextPC`, run `execute_REM` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_rem (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- DIVW family (DIVW/DIVUW): advance `nextPC`, run `execute_DIVW` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_divw (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 (.Regidx 0#5) is_unsigned
  pure ()

/-- REMW family (REMW/REMUW): advance `nextPC`, run `execute_REMW` into `x0` (generic in `is_unsigned`). -/
noncomputable def spec_aluX0_remw (is_unsigned : Bool) (rs2 rs1 : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
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
  simp [spec_aluX0_div, sp1_aluX0, _root_.div_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- REM-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`). -/
theorem correct_aluX0_rem (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_rem is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  cases is_unsigned <;>
  simp [spec_aluX0_rem, sp1_aluX0, _root_.rem_signed_eq, _root_.rem_unsigned_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- DIVW-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`), via `_root_.divw_eq`/`skeleton_binary`. -/
theorem correct_aluX0_divw (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_divw is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  simp [spec_aluX0_divw, sp1_aluX0, _root_.divw_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- REMW-into-`x0` ≡ `sp1_aluX0` (generic in `is_unsigned`). -/
theorem correct_aluX0_remw (is_unsigned : Bool) (rs1 rs2 : BitVec 5) (rs1_val rs2_val : BitVec 64)
    (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1 = some rs1_val) (h_rs2 : s.get_reg? rs2 = some rs2_val) :
    (spec_aluX0_remw is_unsigned (.Regidx rs2) (.Regidx rs1)).run s = (sp1_aluX0 pc).run s := by
  cases is_unsigned <;>
  simp [spec_aluX0_remw, sp1_aluX0, _root_.remw_signed_eq, _root_.remw_unsigned_eq, skeleton_binary,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2]

end SP1Clean.AluX0Sail

namespace SP1Clean.AluX0Chip

open SP1Clean.AluX0Sail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **`AluX0`'s `ChipKind` registration.** `view` projects the row onto the shared bus view: the rd write is
the **zero word** (`x0` discards the result) and the committed `opcode` is the dynamic ALU opcode (so the
`Emits` relation `view.opcode = i.opcode.toNat` holds for whichever ALU opcode routed here). `sailEquiv` is
the ungated 29-way conjunction — for every covered ALU opcode, its real RISC-V Sail execution into `x0`
agrees with `sp1_aluX0` (advance `nextPC`, write nothing); `reaches_sail` discharges all 29 via the five
generic family-core lemmas (the no-op-write collapse). The register reads (`h_rs1`/`h_rs2`) only make the
Sail reads succeed — their values are discarded. -/
def kind : Soundness.ChipKind p where
  name := "AluX0"
  Inputs := AluX0Chip.Inputs
  Cols := Extracted.AluX0Cols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, #v[(0 : ZMod p), 0, 0, 0], cols.opcode⟩
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

end SP1Clean.AluX0Chip
