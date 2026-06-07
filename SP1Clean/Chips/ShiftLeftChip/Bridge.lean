import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.ShiftLeftChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for the `ShiftLeft` chip (SLL + SLLW) + `ChipKind`

The SP1 emulation of a shift-left row is opcode-agnostic (`sp1_sl`: write `nextPC = pc + 4` and the
result register `rd`); the RISC-V Sail spec differs by variant — `spec_sll` (`rop.SLL`, the 64-bit
logical left shift) vs `spec_sllw` (`ropw.SLLW`, the low-32 left shift sign-extended to 64).

`correct_sll_native`/`correct_sllw_native` route the chip's semantic RV64 `sll`/`sllw` facts straight
into the Sail `SLL`/`SLLW`, through the `execute_RTYPE_pure_sll = RV64.sll` / `execute_RTYPEW_pure_sllw
= RV64.sllw` Sail-side identities (mirrors `LtChip/Bridge.lean`'s `execute_RTYPE_pure_slt`). The
`ChipKind`'s `sailEquiv` is the **flag-dispatched** conjunction (`is_sll = 1 → SLL-equation` ∧
`is_sllw = 1 → SLLW-equation`), and `shiftleft_chip_reaches_sail` proves both from the chip `Spec`. -/

namespace SP1Clean.ShiftLeftSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLL` (64-bit logical left). -/
noncomputable def spec_sll (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLL
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLLW` (low-32 left, sext). -/
noncomputable def spec_sllw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SLLW
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for SLL/SLLW): write `nextPC = pc + 4` and the result
register `rd` (the shift result word's 64-bit value). -/
def sp1_sl (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

/-- The Sail `SLL` pure part is the clean RV64 `sll` (operand order `rs2 rs1`): both shift `rs1` left
by the low six bits of `rs2`. -/
theorem execute_RTYPE_pure_sll (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SLL = RV64.sll y x := by
  simp only [execute_RTYPE_pure, RV64.sll, Sail.shift_bits_left, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.log2_xlen]
  rfl

/-- The Sail `SLLW` pure part is the clean RV64 `sllw` (operand order `rs2 rs1`): both take the low 32
bits of `rs1`, shift left by the low five bits of `rs2`, and sign-extend to 64. -/
theorem execute_RTYPEW_pure_sllw (x y : BitVec 64) :
    execute_RTYPEW_pure x y ropw.SLLW = RV64.sllw y x := by
  simp only [execute_RTYPEW_pure, RV64.sllw, sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_left, Sail.BitVec.extractLsb]
  rfl

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SLL): the chip's semantic RV64 `sll` fact (`h_sll`) plus the register/PC
reads drive `spec_sll ≡ sp1_sl`, with no SP1Chips borrow. -/
theorem correct_sll_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_sll : Word.toBitVec64 a_val
        = RV64.sll (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_sll (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sl (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_sll, sp1_sl, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    execute_RTYPE_pure_sll, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_sll]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SLLW): the chip's semantic RV64 `sllw` fact (`h_sllw`) plus the
register/PC reads drive `spec_sllw ≡ sp1_sl`, with no SP1Chips borrow. -/
theorem correct_sllw_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_sllw : Word.toBitVec64 a_val
        = RV64.sllw (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_sllw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sl (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_sllw, sp1_sl, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW',
    execute_RTYPEW_pure_sllw, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_sllw]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: a real `ShiftLeft` chip row reaches the RISC-V Sail shift-left, flag-dispatched — the
SLL/SLLW identities flow from the chip `Spec` into `correct_sll_native`/`correct_sllw_native`. -/
theorem shiftleft_chip_reaches_sail
    (input : ShiftLeftChip.Inputs (ZMod p)) (cols : Extracted.ShiftLeftCols (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : ShiftLeftChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_sll = 1 →
        (spec_sll (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sl (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_sllw = 1 →
        (spec_sllw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sl (.Regidx rd_idx) pc cols.a).run s) := by
  refine ⟨fun hsll => ?_, fun hsllw => ?_⟩
  · exact correct_sll_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_chip h_real).1 hsll)
  · exact correct_sllw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_chip h_real).2 hsllw)

end SP1Clean.ShiftLeftSail

namespace SP1Clean.ShiftLeftChip

open SP1Clean.ShiftLeftSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **The `ShiftLeft` `ChipKind` registration** — the SLL/SLLW row's entry into the heterogeneous
trace + soundness capstone. `view` projects the immediate-capable `ALUTypeReader` adapter through the
reader-agnostic `cols.adapter.toAdapterView`; `rdWrite` is the shift result word `cols.a`; the
Program-bus opcode is `is_sll·6 + is_sllw·21`; `sailEquiv` is the flag-dispatched SLL/SLLW conjunction;
`reaches_sail` is `shiftleft_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "ShiftLeft"
  Inputs := ShiftLeftChip.Inputs
  Cols := Extracted.ShiftLeftCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    cols.is_sll * 6 + cols.is_sllw * 21⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_sll = 1 →
        (spec_sll (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_sl (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_sllw = 1 →
        (spec_sllw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_sl (.Regidx rd) pc cols.a).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    shiftleft_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.ShiftLeftChip
