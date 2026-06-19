import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for Add (+ `ChipKind` registration)

`correct_add_native` proves the RISC-V Sail `ADD` execution agrees with the SP1 chip emulation
given the chip's semantic fact `a_val = op_b + op_c` and the register/PC reads.
`add_chip_reaches_sail` composes `AddChip.Spec` into the bridge; `AddChip.kind` registers Add
rows in the heterogeneous trace and soundness capstone. -/

namespace SP1Clean.AddSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `ADD`. -/
noncomputable def spec_add (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`
(x0-uniform via `wX_bits`, exactly as `execute_RTYPE` writes its result). -/
def sp1_add (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_add`) plus the
register/PC reads drive `spec_add ≡ sp1_add`, with no SP1Chips borrow. -/
theorem correct_add_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_add : Word.toBitVec64 a_val = Word.toBitVec64 op_b_val + Word.toBitVec64 op_c_val) :
    (spec_add (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_add (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_add, sp1_add, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    execute_RTYPE_pure, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_add]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end composition: from the Add chip's verified semantic contract
(`AddChip.Spec`, on a real row) plus the register/PC reads, the RISC-V Sail `ADD`
execution agrees with the SP1 chip emulation. The add identity flows from the chip
`Spec` straight into `correct_add_native`. -/
theorem add_chip_reaches_sail
    (input : AddChip.Inputs (ZMod p)) (cols : Extracted.AddCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : AddChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_add (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_add (.Regidx rd_idx) pc cols.add_operation.value).run s :=
  correct_add_native input.op_b_val input.op_c_val cols.add_operation.value
    rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_chip.2.2.2 h_real)

end SP1Clean.AddSail

namespace SP1Clean.AddChip

open SP1Clean.AddSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Add's `ChipKind` registration** — enters Add rows into the heterogeneous trace and the
soundness capstone. `sailEquiv`/`reaches_sail` route to `add_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Add"
  Inputs := AddChip.Inputs
  Cols := Extracted.AddCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value, 0⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (spec_add (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_add (.Regidx rd) pc cols.add_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    add_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.AddChip
