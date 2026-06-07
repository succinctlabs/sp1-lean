import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.SubwChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for SUBW (+ end-to-end composition)

`correct_subw_native` proves that the RISC-V Sail execution of `SUBW` (`spec_subw`, calling
LeanRV64D's `execute_RTYPEW` with `ropw.SUBW`) agrees with the SP1 chip's emulation
(`sp1_subw`: write `nextPC = pc + 4` and the result register), given the chip's **semantic**
fact `a_val = sext32→64 (op_b - op_c)` (= `SubwChip.circuit`'s `Spec`) and the register/PC reads.

`execute_RTYPEW rs2 rs1 rd .SUBW` computes `sext (rX(rs1)[31:0] - rX(rs2)[31:0])`, so with
`rs1 ↦ op_b_val` and `rs2 ↦ op_c_val` the Sail result is `sext (op_b - op_c)`, matching
`SubwChip.Spec`'s fixed (non-commutative) operand order. -/

namespace SP1Clean.SubwSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The Sail `execute_RTYPEW` pure part for SUBW equals `signExtend 64 (setWidth 32 (x - y))`. -/
lemma subw_pure_eq (x y : BitVec 64) :
    execute_RTYPEW_pure x y .SUBW = (BitVec.setWidth 32 (x - y)).signExtend 64 := by
  simp only [execute_RTYPEW_pure, sign_extend, Sail.BitVec.signExtend]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_sub, BitVec.extractLsb'_toNat,
    BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SUBW`. -/
noncomputable def spec_subw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SUBW
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`. -/
def sp1_subw (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_subw`) plus the register/PC reads
drive `spec_subw ≡ sp1_subw`, with no SP1Chips borrow. -/
theorem correct_subw_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_subw : Word.toBitVec64 a_val =
      (BitVec.setWidth 32 (Word.toBitVec64 op_b_val - Word.toBitVec64 op_c_val)).signExtend 64) :
    (spec_subw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_subw (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_subw, sp1_subw, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW',
    subw_pure_eq, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_subw]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end composition: from the SUBW chip's verified semantic contract (`SubwChip.Spec`, now the
shared `RTypeChipSpec` on the migrated `SubwCols`, on a real row) plus the register/PC reads, the RISC-V
Sail `SUBW` execution agrees with the SP1 chip emulation. The result word is the sign-extended
`SubwOperation.resultWord` (`[v0, v1, msb·65535, msb·65535]`); the subw identity is `RTypeChipSpec`'s
gated-arith conjunct (`h_chip.2.2.2`) bridged through `rv64_subw_eq` into `correct_subw_native`. -/
theorem subw_chip_reaches_sail
    (input : SubwChip.Inputs (ZMod p)) (cols : Extracted.SubwCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : SubwChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_subw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_subw (.Regidx rd_idx) pc
          #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
             cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535]).run s :=
  correct_subw_native input.op_b_val input.op_c_val
    #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
       cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535]
    rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2
    ((h_chip.2.2.2 h_real).trans
      (SubwChip.rv64_subw_eq (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.SubwSail

namespace SP1Clean.SubwChip

open SP1Clean.SubwSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **SUBW's `ChipKind` registration** — SUBW's entry into the heterogeneous trace + capstone (mirrors
`SubChip.kind`). The row's `op_a` write value / `view` write-word is the sign-extended W result
`[v0, v1, msb·65535, msb·65535]`; the Program-bus opcode is `20`; `reaches_sail` is `subw_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Subw"
  Inputs := SubwChip.Inputs
  Cols := Extracted.SubwCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real,
    #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
       cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535], 20⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (spec_subw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_subw (.Regidx rd) pc
          #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
             cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535]).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    subw_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.SubwChip
