import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.DivRemChip.Formal
import SP1Clean.Soundness.ChipRow
import RISCV.Instructions
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

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
the RV64 signature `f rs2_val rs1_val`. The `ChipKind`'s `sailEquiv` is the 8-way flag-dispatched
conjunction. `DivRem` carries `Fact (2 ^ 24 < p)`; the bridge derives `Fact (2 ^ 17 < p)` locally. -/

namespace SP1Clean.DivRemSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIV` (signed 64-bit). -/
noncomputable def spec_div (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVU` (unsigned 64-bit). -/
noncomputable def spec_divu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIV rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REM` (signed 64-bit). -/
noncomputable def spec_rem (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMU` (unsigned 64-bit). -/
noncomputable def spec_remu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REM rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVW` (signed low-32, sext). -/
noncomputable def spec_divw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `DIVUW` (unsigned low-32, sext). -/
noncomputable def spec_divuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_DIVW rs2 rs1 rd true
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMW` (signed low-32, sext). -/
noncomputable def spec_remw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd false
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `REMUW` (unsigned low-32, sext). -/
noncomputable def spec_remuw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_REMW rs2 rs1 rd true
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for the eight divide/remainder variants): write
`nextPC = pc + 4` and the result register `rd` (the divide/remainder result word's 64-bit value). -/
def sp1_divrem (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
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
  simp [spec_div, sp1_divrem, _root_.div_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_div]

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
  simp [spec_divu, sp1_divrem, _root_.div_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_divu]

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
  simp [spec_rem, sp1_divrem, _root_.rem_signed_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_rem]

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
  simp [spec_remu, sp1_divrem, _root_.rem_unsigned_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_remu]

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
  simp [spec_divw, sp1_divrem, _root_.divw_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_divw]

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
  simp [spec_divuw, sp1_divrem, _root_.divw_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_divuw]

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
  simp [spec_remw, sp1_divrem, _root_.remw_signed_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_remw]

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
  simp [spec_remuw, sp1_divrem, _root_.remw_unsigned_eq, skeleton_binary, hb,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_remuw]

omit [Fact (2 ^ 24 < p)] in
/-- End-to-end: from the chip `Spec`, the 8-way DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW Sail
identities hold. -/
theorem divrem_chip_reaches_sail
    (input : DivRemChip.Inputs (ZMod p)) (cols : Extracted.DivRemCols (ZMod p))
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
  -- `DivRemChip.Spec` is now `RTypeReader.Spec ∧ is_real-binary ∧ (is_real = 1 → 8 flag conjuncts)`;
  -- the arithmetic the bridge needs is the third conjunct.
  obtain ⟨h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw⟩ := h_chip.2.2 h_real
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact correct_div_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_div h)
  · exact correct_divu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_divu h)
  · exact correct_rem_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_rem h)
  · exact correct_remu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_remu h)
  · exact correct_divw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_divw h)
  · exact correct_remw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_remw h)
  · exact correct_divuw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_divuw h)
  · exact correct_remuw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_remuw h)

end SP1Clean.DivRemSail

namespace SP1Clean.DivRemChip

open SP1Clean.DivRemSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- `ChipKind` registration for DivRem (DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW). `rs1`/`rs2`
are sourced from inputs `op_b_val`/`op_c_val`. Carries `Fact (2 ^ 24 < p)`. -/
def kind : Soundness.ChipKind p where
  name := "DivRem"
  Inputs := DivRemChip.Inputs
  Cols := Extracted.DivRemCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
      + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_div = 1 →
        (spec_div (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_divu = 1 →
        (spec_divu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_rem = 1 →
        (spec_rem (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_remu = 1 →
        (spec_remu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_divw = 1 →
        (spec_divw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_remw = 1 →
        (spec_remw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_divuw = 1 →
        (spec_divuw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_remuw = 1 →
        (spec_remuw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_divrem (.Regidx rd) pc cols.a).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    divrem_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.DivRemChip
