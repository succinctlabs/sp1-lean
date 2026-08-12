import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.DivRemChip.Formal
import SP1Clean.Soundness.ChipRow
import RISCV.Instructions
import RISCV.SailToRV64
import RISCV.SailPureToInstructions
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for the `DivRem` chip (DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW) + `ChipKind`

The SP1 emulation of a divide/remainder row is opcode-agnostic (`sp1_divrem`: write `nextPC = pc + 4`
and the result register `rd`); the RISC-V Sail spec differs by variant — the eight variants are the
four Sail families (`execute_DIV`/`execute_REM`/`execute_DIVW`/`execute_REMW`) each taken at
`is_unsigned ∈ {false, true}`: signed/unsigned 64-bit divide (`div`/`divu`), signed/unsigned 64-bit
remainder (`rem`/`remu`), and the four low-32 sign-extended word variants (`divw`/`divuw`/`remw`/`remuw`).

This bridge uses the **RV64 provider library's** connection lemmas directly:
`_root_.{div_eq,divw_eq,rem_*_eq,remw_*_eq}` (`RISCV.SailToRV64`) chained with
`RV64.{div_eq,divu_eq,divw_eq,divuw_eq,rem_eq,remu_eq,remw_eq,remuw_eq}`
(`RISCV.SailPureToInstructions`). Each `correct_*_native` is pure monad plumbing — the BitVec
algebra lives in those dep lemmas.

The chip `Spec` sources operands from **inputs** `op_b_val` (rs1) / `op_c_val` (rs2), matching
the RV64 signature `f rs2_val rs1_val`. `advance` is the eight-way flag-dispatched transition.
`DivRem` carries `Fact (2 ^ 24 < p)`; the bridge derives `Fact (2 ^ 17 < p)` locally. -/

open LeanRV64D.Defs
namespace SP1Clean.DivRemSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIV` (signed 64-bit). -/
noncomputable def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVU` (unsigned 64-bit). -/
noncomputable def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REM` (signed 64-bit). -/
noncomputable def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMU` (unsigned 64-bit). -/
noncomputable def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVW` (signed low-32, sext). -/
noncomputable def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVUW` (unsigned low-32, sext). -/
noncomputable def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMW` (signed low-32, sext). -/
noncomputable def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMUW` (unsigned low-32, sext). -/
noncomputable def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for the eight divide/remainder variants): write
`nextPC = pc + 4` and the result register `rd` (the divide/remainder result word's 64-bit value). -/
def sp1_divrem (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (DIV): the chip's RV64 `div` fact plus the register/PC reads drive
`spec_div ≡ sp1_divrem`, via `_root_.div_eq` and `RV64.div_eq`. -/
theorem correct_div_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_div : Word.toBitVec64 a_val
        = RV64.div (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_div (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.div (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) false
      = RV64.div (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.div_eq _ _
  simp only [spec_div, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.div_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_div]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (DIVU): the chip's RV64 `divu` fact drives `spec_divu ≡ sp1_divrem`. -/
theorem correct_divu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_divu : Word.toBitVec64 a_val
        = RV64.divu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_divu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.div (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) true
      = RV64.divu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.divu_eq _ _
  simp only [spec_divu, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.div_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_divu]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (REM): the chip's RV64 `rem` fact drives `spec_rem ≡ sp1_divrem`. -/
theorem correct_rem_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_rem : Word.toBitVec64 a_val
        = RV64.rem (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_rem (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.rem false (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)
      = RV64.rem (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.rem_eq _ _
  simp only [spec_rem, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.rem_signed_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_rem]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (REMU): the chip's RV64 `remu` fact drives `spec_remu ≡ sp1_divrem`. -/
theorem correct_remu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_remu : Word.toBitVec64 a_val
        = RV64.remu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_remu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.rem true (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)
      = RV64.remu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.remu_eq _ _
  simp only [spec_remu, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.rem_unsigned_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_remu]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (DIVW): the chip's RV64 `divw` fact drives `spec_divw ≡ sp1_divrem`. -/
theorem correct_divw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_divw : Word.toBitVec64 a_val
        = RV64.divw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_divw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.divw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) false
      = RV64.divw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.divw_eq _ _
  simp only [spec_divw, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.divw_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_divw]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (DIVUW): the chip's RV64 `divuw` fact drives `spec_divuw ≡ sp1_divrem`. -/
theorem correct_divuw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_divuw : Word.toBitVec64 a_val
        = RV64.divuw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_divuw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.divw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) true
      = RV64.divuw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.divuw_eq _ _
  simp only [spec_divuw, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.divw_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_divuw]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (REMW): the chip's RV64 `remw` fact drives `spec_remw ≡ sp1_divrem`. -/
theorem correct_remw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_remw : Word.toBitVec64 a_val
        = RV64.remw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_remw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.remw false (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)
      = RV64.remw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.remw_eq _ _
  simp only [spec_remw, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.remw_signed_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_remw]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (REMUW): the chip's RV64 `remuw` fact drives `spec_remuw ≡ sp1_divrem`. -/
theorem correct_remuw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_remuw : Word.toBitVec64 a_val
        = RV64.remuw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_remuw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_divrem (.Regidx rd_idx) pc a_val).run s := by
  have hb : SailRV64.remw true (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)
      = RV64.remuw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val) := RV64.remuw_eq _ _
  simp only [spec_remuw, sp1_divrem]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.remw_unsigned_eq, skeleton_binary, hb, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_remuw]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- End-to-end: from the chip `Spec`, the 8-way DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW Sail
identities hold. -/
theorem divrem_chip_reaches_sail
    (input : DivRemChip.Inputs (ZMod p)) (cols : DivRemChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : DivRemChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_div = 1 →
        (spec_div (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_divu = 1 →
        (spec_divu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_rem = 1 →
        (spec_rem (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_remu = 1 →
        (spec_remu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_divw = 1 →
        (spec_divw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_remw = 1 →
        (spec_remw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_divuw = 1 →
        (spec_divuw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_remuw = 1 →
        (spec_remuw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_divrem (.Regidx rd_idx) pc cols.a).run s) := by
  have hcases := h_chip.2.cases
  exact ⟨fun h => correct_div_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .div h_real h),
    fun h => correct_divu_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .divu h_real h),
    fun h => correct_rem_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .rem h_real h),
    fun h => correct_remu_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .remu h_real h),
    fun h => correct_divw_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .divw h_real h),
    fun h => correct_remw_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .remw h_real h),
    fun h => correct_divuw_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .divuw h_real h),
    fun h => correct_remuw_native _ _ _
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (hcases .remuw h_real h)⟩

end SP1Clean.DivRemSail

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- The DivRem RowView (shared by `kind.view` and `advance`): straight-line `pc+4` next-pc, the R-type
adapter, `cols.a` as the divide/remainder write, opcode the flag-weighted R-type discriminant
(DIV 15, DIVU 16, REM 17, REMU 18, DIVW 25, DIVUW 26, REMW 27, REMUW 28). -/
def rowView (inp : Inputs (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    DivRemContract.encodedOpcode cols, .regWrite⟩

/-- **`DivRemChip.advance`** — the per-DivRem-row `try_step` lift (SC Phase 4), 8-way flag dispatch.
Each branch pins the R-type opcode `if isU then <U-op> else <s-op>`, converts the chip `Spec`'s flag-gated
`RV64.<op>` conjunct to the Sail-pure `SailRV64.<op>` write value (via `RV64.<op>_eq`, using the bridge's
explicit-`hb` typed pattern — `rw [RV64.<op>_eq]` fails on the internal `decide False`/`decide True`), and
routes to the matching `advance_of_div/rem/divw/remw isU`. `himmb`/`himmc`/`hstraight` are `rfl` (RTypeReader),
and `hpc0` comes from the reader `Spec`'s bounds. -/
theorem advance (inp : Inputs (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hnonX0⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.a := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hspec.1
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  obtain ⟨case, hselected⟩ := hspec.2.selection hreal'
  have hopSelected := hselected.encodedOpcode
  have hcase := hspec.2.cases case hreal' hselected.1
  -- Retarget the selected case's result equation onto the row's own adapter columns once, before
  -- the eight-way split; only the `Case.result` match still has to reduce per branch.
  simp only [DivRemChip.Inputs.op_c_val, DivRemChip.Inputs.op_b_val, hlink] at hcase
  cases case
  · -- is_div
    have hop : r.opcode = (((if (false:Bool) then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.div (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) false := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.div (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) false
        = RV64.div (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.div_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_div false hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_divu
    have hop : r.opcode = (((if (true:Bool) then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.div (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) true := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.div (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) true
        = RV64.divu (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.divu_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_div true hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_rem
    have hop : r.opcode = (((if (false:Bool) then Opcode.REMU else Opcode.REM)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.rem false (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.rem false (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
        = RV64.rem (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.rem_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_rem false hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_remu
    have hop : r.opcode = (((if (true:Bool) then Opcode.REMU else Opcode.REM)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.rem true (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.rem true (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
        = RV64.remu (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.remu_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_rem true hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_divw
    have hop : r.opcode = (((if (false:Bool) then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.divw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) false := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.divw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) false
        = RV64.divw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.divw_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_divw false hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_remw
    have hop : r.opcode = (((if (false:Bool) then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.remw false (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.remw false (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
        = RV64.remw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.remw_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_remw false hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_divuw
    have hop : r.opcode = (((if (true:Bool) then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.divw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) true := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.divw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) true
        = RV64.divuw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.divuw_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_divw true hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_remuw
    have hop : r.opcode = (((if (true:Bool) then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p) := by
      simpa [hr, rowView, DivRemContract.Case.opcode, Opcode.toNat] using hopSelected
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.remw true (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) := by
      simp only [DivRemContract.Case.result] at hcase
      have hb : SailRV64.remw true (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
        = RV64.remuw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.remuw_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hcase
    exact advance_of_remw true hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- `ChipKind` registration for DivRem (DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW). `rs1`/`rs2`
are sourced from inputs `op_b_val`/`op_c_val`. Carries `Fact (2 ^ 24 < p)`. -/
def kind : Soundness.ChipKind p where
  name := "DivRem"
  Inputs := DivRemChip.Inputs
  Cols := DivRemChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧
    (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.DivRemChip
