import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.AddiChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for Addi (+ end-to-end composition)

`correct_addi_native` proves that the RISC-V Sail execution of `ADDI`
(`spec_addi`, calling LeanRV64D's `execute_ITYPE … iop.ADDI`) agrees with the SP1 chip's emulation
(`sp1_addi`: write `nextPC = pc + 4` and the result register), given:

* the chip's **semantic** fact `a_val = op_b + signExtend(imm)`,
* and the register/PC read facts (the rs1 read; in the full system supplied by the reader bus).

`addi_chip_reaches_sail` composes the verified `AddiChip.Spec` straight into the bridge: a real `Addi`
chip row reaches the RISC-V Sail spec via the gadget/chip `Spec`'s `add` identity plus an immediate-decode
fact `op_c_val = signExtend(imm)` (the I-type analogue of the second register read). The direct I-type
analogue of `Chips/AddChip/Bridge.lean` — `execute_ITYPE`'s `.ADDI` arm is `wX_bits rd (rX_bits rs1 +
signExtend imm)`, which `simp` reduces with the auto `run_rX_bits`/`run_wX_bits` lemmas. -/

namespace SP1Clean.AddiSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `ADDI`. -/
noncomputable def spec_addi (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.ADDI
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`
(x0-uniform via `wX_bits`, exactly as `execute_ITYPE` writes its result). -/
def sp1_addi (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_add`) plus the rs1/PC reads drive
`spec_addi ≡ sp1_addi`. `execute_ITYPE`'s `.ADDI` arm `wX_bits rd (rX_bits rs1 + signExtend imm)` reduces
via the auto `run_rX_bits`/`run_wX_bits` simp lemmas. -/
theorem correct_addi_native
    (op_b_val a_val : Word (ZMod p)) (rs1_idx rd_idx : BitVec 5)
    (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_add : Word.toBitVec64 a_val = Word.toBitVec64 op_b_val + sign_extend (m := 64) imm) :
    (spec_addi imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addi (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_addi, sp1_addi, execute_ITYPE, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_add]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end composition: from the `Addi` chip's verified semantic contract (`AddiChip.Spec`, on a real
row), the rs1/PC reads, and the immediate-decode fact (`op_c_val = signExtend imm`), the RISC-V Sail `ADDI`
execution agrees with the SP1 chip emulation. The add identity flows from the chip `Spec`
(`RV64.add op_c op_b` is defeq `op_b + op_c`), and `op_c_val` is the immediate word. -/
theorem addi_chip_reaches_sail
    (input : AddiChip.Inputs (ZMod p)) (cols : Extracted.AddiCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : AddiChip.Spec input cols data)
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val)) :
    (spec_addi imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addi (.Regidx rd_idx) pc cols.add_operation.value).run s :=
  correct_addi_native input.op_b_val cols.add_operation.value rs1_idx rd_idx imm pc s h_pc h_rs1
    (by rw [← h_dec]; exact h_chip.2.2 h_real)

end SP1Clean.AddiSail

namespace SP1Clean.AddiChip

open SP1Clean.AddiSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Addi's `ChipKind` registration** — enters `ADDI` rows into the heterogeneous trace and the soundness
capstone. `view` is the straight-line shape (`next_pc = pc + 4`), the I-type adapter
(`ITypeReader.toAdapterView`: `op_b` the rs1 read, `op_c = op_c_imm` the immediate, `imm_c = 1`), the
`is_real` selector, the add result `add_operation.value` as the rd write-back, opcode 1. `sailEquiv`
quantifies the PC/rs1 reads and the immediate-decode fact internally (the I-type analogue of the second
register read); `reaches_sail` is `addi_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Addi"
  Inputs := AddiChip.Inputs
  Cols := Extracted.AddiCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value, 1⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    Word.toBitVec64 inp.op_c_val = sign_extend (m := 64) imm →
    (spec_addi imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_addi (.Regidx rd) pc cols.add_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rd imm pc h_pc h_rs1 h_dec =>
    addi_chip_reaches_sail inp cols data rs1 rd imm pc s h_real h_chip h_dec h_pc h_rs1

end SP1Clean.AddiChip
