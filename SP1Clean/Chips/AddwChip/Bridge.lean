import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.AddwChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for ADDW (+ `ChipKind` registration)

`correct_addw_native` proves the RISC-V Sail `ADDW` execution agrees with the SP1 chip emulation
given the chip's semantic fact `a_val = sext32→64 (op_b + op_c)` and the register/PC reads.
`addw_pure_eq` relates the Sail pure part to `signExtend 64 (setWidth 32 (b + c))`. -/

namespace SP1Clean.AddwSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The Sail `execute_RTYPEW` pure part for ADDW equals `signExtend 64 (setWidth 32 (x + y))`:
the low-32 truncations `extractLsb _ 31 0` are `setWidth 32`, and the truncated sum is the
truncation of the sum. -/
lemma addw_pure_eq (x y : BitVec 64) :
    execute_RTYPEW_pure x y .ADDW = (BitVec.setWidth 32 (x + y)).signExtend 64 := by
  simp only [execute_RTYPEW_pure, sign_extend, Sail.BitVec.signExtend]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_add, BitVec.extractLsb'_toNat,
    BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `ADDW`. -/
noncomputable def spec_addw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.ADDW
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`. -/
def sp1_addw (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_addw`) plus the register/PC reads
drive `spec_addw ≡ sp1_addw`, with no SP1Chips borrow. -/
theorem correct_addw_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_addw : Word.toBitVec64 a_val =
      (BitVec.setWidth 32 (Word.toBitVec64 op_b_val + Word.toBitVec64 op_c_val)).signExtend 64) :
    (spec_addw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addw (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_addw, sp1_addw, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW',
    addw_pure_eq, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_addw]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from the ADDW chip's verified `Spec` (gated-arith conjunct `.2.2`) plus the
register/PC reads, the RISC-V Sail `ADDW` agrees with the SP1 emulation; identity via `rv64_addw_eq`. -/
theorem addw_chip_reaches_sail
    (input : AddwChip.Inputs (ZMod p)) (cols : Extracted.AddwCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : AddwChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_addw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addw (.Regidx rd_idx) pc (AddwChip.resultWord cols)).run s :=
  correct_addw_native input.op_b_val input.op_c_val (AddwChip.resultWord cols)
    rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2
    ((h_chip.2.2 h_real).trans
      (AddwChip.rv64_addw_eq (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.AddwSail

namespace SP1Clean.AddwChip

open SP1Clean.AddwSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **ADDW's `ChipKind` registration.** Write-word is the sign-extended W result `AddwChip.resultWord`;
adapter is `ALUTypeReader`, projected via `toAdapterView`; Program-bus opcode `19`. -/
def kind : Soundness.ChipKind p where
  name := "Addw"
  Inputs := AddwChip.Inputs
  Cols := Extracted.AddwCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, AddwChip.resultWord cols, 19⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (spec_addw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_addw (.Regidx rd) pc (AddwChip.resultWord cols)).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    addw_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.AddwChip
