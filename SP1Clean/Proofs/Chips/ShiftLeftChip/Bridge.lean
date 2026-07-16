import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for the `ShiftLeft` chip (SLL + SLLW) + `ChipKind`

The SP1 emulation of a shift-left row is opcode-agnostic (`sp1_sl`: write `nextPC = pc + 4` and the
result register `rd`); the RISC-V Sail spec differs by variant — `spec_sll` (`rop.SLL`, the 64-bit
logical left shift) vs `spec_sllw` (`ropw.SLLW`, the low-32 left shift sign-extended to 64).

`correct_sll_native`/`correct_sllw_native` route the chip's RV64 `sll`/`sllw` facts into the Sail
`SLL`/`SLLW` via `execute_RTYPE_pure_sll = RV64.sll` / `execute_RTYPEW_pure_sllw = RV64.sllw`.
`advance` dispatches the SLL/SLLW cases; `shiftleft_chip_reaches_sail` remains the semantic helper. -/

open LeanRV64D.Defs
namespace SP1Clean.ShiftLeftSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLL` (64-bit logical left). -/
noncomputable def spec_sll (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLL
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLLW` (low-32 left, sext). -/
noncomputable def spec_sllw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SLLW
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for SLL/SLLW): write `nextPC = pc + 4` and the result
register `rd` (the shift result word's 64-bit value). -/
def sp1_sl (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
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
  simp only [spec_sll, sp1_sl]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', execute_RTYPE_pure_sll, h_rs1, h_rs2, h_sll]

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
  simp only [spec_sllw, sp1_sl]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW', execute_RTYPEW_pure_sllw,
    h_rs1, h_rs2, h_sllw]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from the chip `Spec`, the SLL/SLLW Sail identities hold. -/
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
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The ShiftLeft RowView (standalone, shared by `kind.view` and `advance`): straight-line `next_pc`,
the ALU adapter, `cols.a` as the shift-result write, opcode `is_sll·6 + is_sllw·21` (SLL = 6, SLLW = 21). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.ShiftLeftCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a, cols.is_sll * 6 + cols.is_sllw * 21, .regWrite⟩

/-- **`ShiftLeftChip.advance`** — the per-ShiftLeft-row `try_step` lift (SC Phase 4). A multi-op R-type chip
(SLL / SLLW), so it `rcases` the `advanceReady` flag partition and routes each branch to the op-generic
straight-line register-write core: `advance_of_rtype rop.SLL` / `advance_of_rtypew ropw.SLLW`. The write
value is `execute_RTYPE_pure`/`execute_RTYPEW_pure` (proved `= RV64.sll`/`RV64.sllw` by
`execute_RTYPE_pure_sll`/`execute_RTYPEW_pure_sllw`), matched against the chip `Spec`'s flag-gated `RV64.sll`
/`RV64.sllw` conjunct. `advanceReady` carries the reader passthrough, the pc-limb bound, `op_a ≠ 0`, `imm_c =
0`, the R-type operand binding `op_c = op_c_memory.prev_value`, and the one-hot flag partition. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.ShiftLeftCols (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : cols.state.pc[0].val < 2 ^ 16 ∧ inp.adapter = cols.adapter ∧
      (rowView inp cols).adapter.op_a ≠ 0 ∧ cols.adapter.imm_c = 0 ∧
      cols.adapter.op_c = cols.adapter.op_c_memory.prev_value ∧
      ((cols.is_sll = 1 ∧ cols.is_sllw = 0) ∨ (cols.is_sllw = 1 ∧ cols.is_sll = 0))) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hpc0, hpass, hnonX0, himmc0, hopc_eq, hflag⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.a := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  have himmc : r.adapter.imm_c = 0 := himmc0
  have hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]] := rfl
  rcases hflag with ⟨h_sll, h_sllw0⟩ | ⟨h_sllw, h_sll0⟩
  · have hop : r.opcode = ((ropToOpcode rop.SLL).toNat : ZMod p) := by
      simp [hr, rowView, h_sll, h_sllw0, ropToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = execute_RTYPE_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) rop.SLL := by
      have hsll_spec := (hspec hreal').1 h_sll
      simp only [ShiftLeftChip.Inputs.op_c_val, ShiftLeftChip.Inputs.op_b_val, hpass] at hsll_spec
      rw [execute_RTYPE_pure_sll, vrd, ← hopc_eq]; exact hsll_spec
    exact advance_of_rtype rop.SLL hcfg hrom hpcread hvalb hdecrom hop himmb himmc hnonX0 hpc0 hstraight hval
  · have hop : r.opcode = ((ropwToOpcode ropw.SLLW).toNat : ZMod p) := by
      simp [hr, rowView, h_sllw, h_sll0, ropwToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = execute_RTYPEW_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) ropw.SLLW := by
      have hsllw_spec := (hspec hreal').2 h_sllw
      simp only [ShiftLeftChip.Inputs.op_c_val, ShiftLeftChip.Inputs.op_b_val, hpass] at hsllw_spec
      rw [execute_RTYPEW_pure_sllw, vrd, ← hopc_eq]; exact hsllw_spec
    exact advance_of_rtypew ropw.SLLW hcfg hrom hpcread hvalb hdecrom hop himmb himmc hnonX0 hpc0 hstraight hval

/-- `ChipKind` registration for ShiftLeft (SLL/SLLW). -/
def kind : Soundness.ChipKind p where
  name := "ShiftLeft"
  Inputs := ShiftLeftChip.Inputs
  Cols := Extracted.ShiftLeftCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => cols.state.pc[0].val < 2 ^ 16 ∧ inp.adapter = cols.adapter ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧ cols.adapter.imm_c = 0 ∧
    cols.adapter.op_c = cols.adapter.op_c_memory.prev_value ∧
    ((cols.is_sll = 1 ∧ cols.is_sllw = 0) ∨ (cols.is_sllw = 1 ∧ cols.is_sll = 0))
  advance := some (PLift.up advance)

end SP1Clean.ShiftLeftChip
