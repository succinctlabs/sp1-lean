import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.AddiChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for Addi

`correct_addi_native` proves Sail's `execute_ITYPE … iop.ADDI` agrees with the SP1 chip
emulation (`sp1_addi`: write `nextPC = pc + 4` and the result register), given the chip's
semantic `a_val = op_b + signExtend(imm)` and the rs1/PC reads. `execute_ITYPE`'s `.ADDI` arm
is `wX_bits rd (rX_bits rs1 + signExtend imm)`, closed by `simp` with the auto
`run_rX_bits`/`run_wX_bits` lemmas. -/

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
/-- End-to-end: from `AddiChip.Spec`, rs1/PC reads, and the immediate-decode fact, Sail's `ADDI`
agrees with the SP1 chip emulation. -/
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
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Addi's committed bus view** — the chip-agnostic `RowView` (opcode `1`, the `pc+4` straight-line
next-pc, `add_operation` result as `rdWrite`). Standalone so `AddiChip.advance` can be supplied *as*
`kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.AddiCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value, 1, .regWrite⟩

/-- **`AddiChip.advance`** — the per-Addi-row `try_step` lift (SC Phase 4), the first I-type migrated chip: a
thin adapter over `advance_of_itype` with opcode `ADDI` + the write-value identity `hval`
(`rdWrite = op_b + op_c`, from `AddiChip.Spec`'s gated `RV64.add` conjunct; the immediate `op_c = op_c_imm`
round-trip is inside `advance_of_itype`). The `advanceReady` bundle carries the extra state passthrough
`inp.state = cols.state` (I-type reads its pc bound off `cols.state`). Stated to match the
`ChipKind.advance` obligation exactly, so `kind.advance := some (PLift.up advance)` type-checks directly. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.AddiCols (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1)
    (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ inp.state = cols.state ∧
      (rowView inp cols).adapter.op_a ≠ 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hstatelink, hnonX0⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopc : r.adapter.op_c = cols.adapter.op_c_imm := rfl
  obtain ⟨hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  rw [hstatelink] at hpc0
  have hop : r.opcode = ((iopToOpcode iop.ADDI).toNat : ZMod p) := by
    simp [hr, rowView, iopToOpcode, Opcode.toNat]
  have hval : Word.toBitVec64 r.rdWrite
      = Word.toBitVec64 r.adapter.op_b_memory.prev_value + Word.toBitVec64 r.adapter.op_c := by
    have hidentity := harith hreal'
    simp only [AddiChip.Inputs.op_b_val, AddiChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopc, hidentity, RV64.add]
  exact advance_of_itype iop.ADDI hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- `ChipKind` registration for Addi (ADDI, opcode 1). `sailEquiv` carries the immediate-decode fact
`op_c_val = signExtend imm`; `advance`/`advanceReady` (SC Phase 4) route to `AddiChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Addi"
  Inputs := AddiChip.Inputs
  Cols := Extracted.AddiCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    Word.toBitVec64 inp.op_c_val = sign_extend (m := 64) imm →
    (spec_addi imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_addi (.Regidx rd) pc cols.add_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rd imm pc h_pc h_rs1 h_dec =>
    addi_chip_reaches_sail inp cols data rs1 rd imm pc s h_real h_chip h_dec h_pc h_rs1
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ inp.state = cols.state ∧
    (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.AddiChip
