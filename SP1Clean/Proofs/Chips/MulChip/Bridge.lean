import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.MulChip.Formal
import SP1Clean.Soundness.ChipRow
import RISCV.Instructions
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # Native Sail bridge for the `Mul` chip (MUL/MULH/MULHU/MULHSU/MULW) + `ChipKind`

The SP1 emulation of a multiply row is opcode-agnostic (`sp1_mul`: write `nextPC = pc + 4` and the
result register `rd`); the RISC-V Sail spec differs by variant — `spec_mul` (low 64 of the signed
product), `spec_mulh` (high 64, signed×signed), `spec_mulhu` (high 64, unsigned×unsigned), `spec_mulhsu`
(high 64, signed×unsigned), `spec_mulw` (low-32 product sign-extended). The five variants are the four
`MUL` `mul_op` records (Low/High × the signedness pair) plus `MULW`.

This bridge uses the **RV64 provider library's** connection lemmas directly:
`_root_.mul_eq`/`_root_.mulw_eq` (`RISCV.SailToRV64`) chained with
`RV64.{mul,mulh,mulhu,mulhsu,mulw}_eq` (`RISCV.SailPureToInstructions`, fully proven incl. the
MULHSU signed×unsigned high half). `correct_mul*_native` is pure monad plumbing — the BitVec
algebra lives in those dep lemmas.

The chip `Spec` sources operands from **inputs** `op_b_val` (rs1) / `op_c_val` (rs2), matching
the RV64 signature `f rs2_val rs1_val`. The `ChipKind`'s `sailEquiv` is the 5-way flag-dispatched
conjunction. `Mul` carries `Fact (2 ^ 24 < p)`; the bridge derives `Fact (2 ^ 17 < p)` locally. -/

namespace SP1Clean.MulSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The `MUL` `mul_op`: low 64 bits, signed × signed. -/
def mulOp_mul : mul_op := { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }
/-- The `MULH` `mul_op`: high 64 bits, signed × signed. -/
def mulOp_mulh : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
/-- The `MULHU` `mul_op`: high 64 bits, unsigned × unsigned. -/
def mulOp_mulhu : mul_op := { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
/-- The `MULHSU` `mul_op`: high 64 bits, signed × unsigned. -/
def mulOp_mulhsu : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MUL` (low 64, signed×signed). -/
noncomputable def spec_mul (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mul
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULH` (high 64, signed×signed). -/
noncomputable def spec_mulh (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulh
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULHU` (high 64, unsigned×unsigned). -/
noncomputable def spec_mulhu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulhu
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULHSU` (high 64, signed×unsigned). -/
noncomputable def spec_mulhsu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulhsu
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULW` (low-32 product, sext). -/
noncomputable def spec_mulw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MULW rs2 rs1 rd
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for the five multiply variants): write `nextPC = pc + 4`
and the result register `rd` (the multiply result word's 64-bit value). -/
def sp1_mul (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MUL): the chip's RV64 `mul` fact plus the register/PC reads drive
`spec_mul ≡ sp1_mul`, via `_root_.mul_eq` (`execute_MUL = skeleton_binary … SailRV64.mul`) and
`RV64.mul_eq` (`SailRV64.mul {Low,S,S} = RV64.mul`). -/
theorem correct_mul_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mul : Word.toBitVec64 a_val
        = RV64.mul (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mul (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_mul, sp1_mul, mulOp_mul, _root_.mul_eq, skeleton_binary, RV64.mul_eq,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_mul]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULH): the chip's RV64 `mulh` fact drives `spec_mulh ≡ sp1_mul`. -/
theorem correct_mulh_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulh : Word.toBitVec64 a_val
        = RV64.mulh (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulh (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_mulh, sp1_mul, mulOp_mulh, _root_.mul_eq, skeleton_binary, RV64.mulh_eq,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_mulh]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULHU): the chip's RV64 `mulhu` fact drives `spec_mulhu ≡ sp1_mul`. -/
theorem correct_mulhu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulhu : Word.toBitVec64 a_val
        = RV64.mulhu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulhu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_mulhu, sp1_mul, mulOp_mulhu, _root_.mul_eq, skeleton_binary, RV64.mulhu_eq,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_mulhu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULHSU): the chip's RV64 `mulhsu` fact drives `spec_mulhsu ≡ sp1_mul`. -/
theorem correct_mulhsu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulhsu : Word.toBitVec64 a_val
        = RV64.mulhsu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulhsu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_mulhsu, sp1_mul, mulOp_mulhsu, _root_.mul_eq, skeleton_binary, RV64.mulhsu_eq,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_mulhsu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULW): the chip's RV64 `mulw` fact drives `spec_mulw ≡ sp1_mul`, via
`_root_.mulw_eq` and `RV64.mulw_eq`. -/
theorem correct_mulw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulw : Word.toBitVec64 a_val
        = RV64.mulw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_mulw, sp1_mul, _root_.mulw_eq, skeleton_binary, RV64.mulw_eq,
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_mulw]

omit [Fact (2 ^ 24 < p)] in
/-- End-to-end: from the chip `Spec`, the 5-way MUL/MULH/MULHU/MULHSU/MULW Sail identities hold. -/
theorem mul_chip_reaches_sail
    (input : MulChip.Inputs (ZMod p)) (cols : Extracted.MulCols (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : MulChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_mul = 1 →
        (spec_mul (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulh = 1 →
        (spec_mulh (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulhu = 1 →
        (spec_mulhu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulhsu = 1 →
        (spec_mulhsu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulw = 1 →
        (spec_mulw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) := by
  -- `MulChip.Spec` is now `RTypeReader.Spec ∧ is_real-binary ∧ (is_real = 1 → 5 flag conjuncts)`;
  -- the arithmetic the bridge needs is the third conjunct.
  obtain ⟨h_mul, h_mulh, h_mulhu, h_mulhsu, h_mulw⟩ := h_chip.2.2 h_real
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact correct_mul_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mul h)
  · exact correct_mulh_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulh h)
  · exact correct_mulhu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulhu h)
  · exact correct_mulhsu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulhsu h)
  · exact correct_mulw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulw h)

end SP1Clean.MulSail

namespace SP1Clean.MulChip

open SP1Clean.MulSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- `ChipKind` registration for Mul (MUL/MULH/MULHU/MULHSU/MULW). `rs1`/`rs2` are sourced from
inputs `op_b_val`/`op_c_val`. Carries `Fact (2 ^ 24 < p)`. -/
def kind : Soundness.ChipKind p where
  name := "Mul"
  Inputs := MulChip.Inputs
  Cols := Extracted.MulCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 + cols.is_mulhsu * 14
      + cols.is_mulw * 24, .regWrite⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_mul = 1 →
        (spec_mul (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulh = 1 →
        (spec_mulh (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulhu = 1 →
        (spec_mulhu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulhsu = 1 →
        (spec_mulhsu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulw = 1 →
        (spec_mulw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    mul_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.MulChip
