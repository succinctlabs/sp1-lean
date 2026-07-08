import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.AddwChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

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

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `ADDIW` (I-type add-word-immediate). -/
noncomputable def spec_addiw (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ADDIW imm rs1 rd
  pure ()

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for ADDIW: the chip's semantic fact (`h_addw`, with the immediate operand
`op_c_val` bound to `sign_extend imm` via `h_dec`) plus the rs1/PC reads drive `spec_addiw ≡ sp1_addw`. The
Sail `ADDIW` writes `sign_extend (extractLsb (rX rs1 + immext) 31 0)`, which `addw_pure_eq` ties to the
chip's `signExtend 64 (setWidth 32 (op_b + op_c))`. -/
theorem correct_addiw_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_addw : Word.toBitVec64 a_val =
      (BitVec.setWidth 32 (Word.toBitVec64 op_b_val + Word.toBitVec64 op_c_val)).signExtend 64) :
    (spec_addiw imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addw (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 a_val
      = sign_extend (m := 64) (Sail.BitVec.extractLsb
          (Word.toBitVec64 op_b_val + sign_extend (m := 64) imm) 31 0) := by
    rw [h_addw, ← h_dec]
    simp only [sign_extend, Sail.BitVec.signExtend]
    congr 1
  simp [spec_addiw, sp1_addw, execute_ADDIW, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, h_pc, h_rs1, harm]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (ADDIW): from the ADDW chip's verified `Spec` plus the rs1/PC reads and the immediate decode
(`op_c_val = sign_extend imm`), Sail's `ADDIW` agrees with the SP1 chip emulation. -/
theorem addiw_chip_reaches_sail
    (input : AddwChip.Inputs (ZMod p)) (cols : Extracted.AddwCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : AddwChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm) :
    (spec_addiw imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_addw (.Regidx rd_idx) pc (AddwChip.resultWord cols)).run s :=
  correct_addiw_native input.op_b_val input.op_c_val (AddwChip.resultWord cols)
    rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec
    ((h_chip.2.2 h_real).trans
      (AddwChip.rv64_addw_eq (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.AddwSail

namespace SP1Clean.AddwChip

open SP1Clean.AddwSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The ADDIW pure part equals `signExtend 64 (setWidth 32 (x + y))` (the low-32 sum, sign-extended) — the
`.ADDIW` twin of `addw_pure_eq`/`subw_pure_eq`. `extractLsb (x+y) 31 0` is defeq `setWidth 32 (x+y)`, so
`congr 1` closes the `signExtend` congruence. -/
lemma addiw_pure_eq (x y : BitVec 64) :
    execute_ADDIW_pure x y = (BitVec.setWidth 32 (x + y)).signExtend 64 := by
  simp only [execute_ADDIW_pure, sign_extend, Sail.BitVec.signExtend]; congr 1

/-- **Addw's committed bus view** — the chip-agnostic `RowView` (opcode `19`, the `pc+4` straight-line
next-pc, the sign-extended W result as `rdWrite`). Standalone so `AddwChip.advance` can be supplied *as*
`kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.AddwCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, AddwChip.resultWord cols, 19, .regWrite⟩

/-- **`AddwChip.advance`** — the per-Addw-row `try_step` lift (SC Phase 4): a 2-branch adapter over the W-op
paths — ADDW (`imm_c = 0`) via `advance_of_rtypew`, ADDIW (`imm_c = 1`) via `advance_of_addiw` (both commit
opcode `ADDW` = 19, distinguished by `imm_c`). Each branch's write value threads the Spec's gated
`RV64.addw op_c op_b` through `rv64_addw_eq` + the respective `addw_pure_eq` / `addiw_pure_eq` into the Sail
execute pure part. The `advanceReady` bundle carries the pc-limb bound, the `imm_c` binary, the ADDIW immediate
binding `op_c_memory.prev_value = op_c` (the `ALUTypeReader`'s immediate-consistency constraint), and the
`op_a ≠ 0` routing. Stated to match the `ChipKind.advance` obligation exactly, so
`kind.advance := some (PLift.up advance)` type-checks. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.AddwCols (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1)
    (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
      (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
      (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c) ∧
      (rowView inp cols).adapter.op_a ≠ 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hpc0, himmc_bin, himmbind, hnonX0⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = AddwChip.resultWord cols := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  have vopc : r.adapter.op_c = cols.adapter.op_c := rfl
  obtain ⟨-, -, hgated⟩ := hspec
  have harith := hgated hreal'
  simp only [AddwChip.Inputs.op_b_val, AddwChip.Inputs.op_c_val, hlink] at harith
  rcases himmc_bin with h0 | h1
  · have hop : r.opcode = ((ropwToOpcode ropw.ADDW).toNat : ZMod p) := by
      simp [hr, rowView, ropwToOpcode, Opcode.toNat]
    have hval : r.rdWrite.toBitVec64 = execute_RTYPEW_pure r.adapter.op_b_memory.prev_value.toBitVec64
        r.adapter.op_c_memory.prev_value.toBitVec64 ropw.ADDW := by
      rw [vrd, vopbm, vopcm, harith, AddwChip.rv64_addw_eq, addw_pure_eq]
    exact advance_of_rtypew ropw.ADDW hcfg hrom hpcread hvalb hdecrom hop rfl h0 hnonX0 hpc0 rfl hval
  · have hbind := himmbind h1
    have hop : r.opcode = ((Opcode.ADDW).toNat : ZMod p) := by
      simp [hr, rowView, Opcode.toNat]
    have hval : r.rdWrite.toBitVec64 = execute_ADDIW_pure r.adapter.op_b_memory.prev_value.toBitVec64
        r.adapter.op_c.toBitVec64 := by
      rw [vrd, vopbm, vopc, harith, hbind, AddwChip.rv64_addw_eq, addiw_pure_eq]
    exact advance_of_addiw hcfg hrom hpcread hvalb hdecrom hop rfl h1 hnonX0 hpc0 rfl hval

/-- **ADDW's `ChipKind` registration.** Write-word is the sign-extended W result `AddwChip.resultWord`;
adapter is `ALUTypeReader`, projected via `toAdapterView`; Program-bus opcode `19`.
`advance`/`advanceReady` (SC Phase 4) route to `AddwChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Addw"
  Inputs := AddwChip.Inputs
  Cols := Extracted.AddwCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s =>
    (∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
      s.regs.get? Register.PC = some pc →
      s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
      s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
      (spec_addw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
        = (sp1_addw (.Regidx rd) pc (AddwChip.resultWord cols)).run s) ∧
    (∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc : BitVec 64),
      s.regs.get? Register.PC = some pc →
      s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
      Word.toBitVec64 inp.op_c_val = sign_extend (m := 64) imm →
      (spec_addiw imm (.Regidx rs1) (.Regidx rd)).run s
        = (sp1_addw (.Regidx rd) pc (AddwChip.resultWord cols)).run s)
  reaches_sail := fun inp cols data s h_real h_chip =>
    ⟨fun rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
       addw_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2,
     fun rs1 rd imm pc h_pc h_rs1 h_dec =>
       addiw_chip_reaches_sail inp cols data rs1 rd imm pc s h_real h_chip h_pc h_rs1 h_dec⟩
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
    (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
    (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c) ∧
    (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.AddwChip
