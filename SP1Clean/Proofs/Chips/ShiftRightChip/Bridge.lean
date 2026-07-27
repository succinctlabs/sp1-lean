import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance
import RISCV.ForLean

/-! # Native Sail bridge for the `ShiftRight` chip (SRL/SRA/SRLW/SRAW) + `ChipKind`

The SP1 emulation of a shift-right row is opcode-agnostic (`sp1_sr`: write `nextPC = pc + 4` and the
result register `rd`); the RISC-V Sail spec differs by variant — `spec_srl` (`rop.SRL`, 64-bit logical),
`spec_sra` (`rop.SRA`, 64-bit arithmetic), `spec_srlw` (`ropw.SRLW`, low-32 logical sext), `spec_sraw`
(`ropw.SRAW`, low-32 arithmetic sext).

`correct_{srl,sra,srlw,sraw}_native` routes the chip's RV64 facts into the Sail execution via the
`execute_RTYPE(W)_pure_* = RV64.*` Sail-side identities. The chip `Spec` sources operands from the
**register read-backs** `adapter.op_b_memory.prev_value` (rs1) / `adapter.op_c_memory.prev_value`
(rs2) — SP1's shift chip inlines the register-read decomposition — so `h_rs1`/`h_rs2` read those
adapter columns. `advance` is the four-way flag-dispatched transition. -/

open LeanRV64D.Defs
namespace SP1Clean.ShiftRightSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SRL` (64-bit logical right). -/
noncomputable def spec_srl (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRL
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SRA` (64-bit arithmetic right). -/
noncomputable def spec_sra (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRA
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SRLW` (low-32 logical, sext). -/
noncomputable def spec_srlw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRLW
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SRAW` (low-32 arithmetic, sext). -/
noncomputable def spec_sraw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRAW
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for the four shift-right variants): write `nextPC = pc + 4`
and the result register `rd` (the shift result word's 64-bit value). -/
def sp1_sr (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

/-- The Sail `SRL` pure part is the clean RV64 `srl` (operand order `rs2 rs1`). -/
theorem execute_RTYPE_pure_srl (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SRL = RV64.srl y x := by
  simp only [execute_RTYPE_pure, RV64.srl, Sail.shift_bits_right, Sail.BitVec.extractLsb,
    LeanRV64D.Functions.log2_xlen]
  rfl

set_option linter.unusedSimpArgs false in
/-- The Sail `SRA` pure part is the clean RV64 `sra` (operand order `rs2 rs1`); mirrors the RISCV
package's `rtype_sra_eq` (`execute_RTYPE_pure x y .SRA` is defeq to `SailRV64.rtype rop.SRA y x`). -/
theorem execute_RTYPE_pure_sra (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SRA = RV64.sra y x := by
  simp [execute_RTYPE_pure, RV64.sra, LeanRV64D.Functions.shift_bits_right_arith,
    Sail.BitVec.extractLsb, LeanRV64D.Functions.log2_xlen, Sail.BitVec.toNatInt]
  congr 1

/-- The Sail `SRLW` pure part is the clean RV64 `srlw` (operand order `rs2 rs1`). -/
theorem execute_RTYPEW_pure_srlw (x y : BitVec 64) :
    execute_RTYPEW_pure x y ropw.SRLW = RV64.srlw y x := by
  simp only [execute_RTYPEW_pure, RV64.srlw, sign_extend, Sail.BitVec.signExtend,
    Sail.shift_bits_right, Sail.BitVec.extractLsb]
  rfl

/-- The Sail `SRAW` pure part is the clean RV64 `sraw` (operand order `rs2 rs1`); mirrors the RISCV
package's `rtypew_sraw_eq` (the `BitVec.sshiftRight'` reduction needs `RISCV.ForLean`). -/
theorem execute_RTYPEW_pure_sraw (x y : BitVec 64) :
    execute_RTYPEW_pure x y ropw.SRAW = RV64.sraw y x := by
  simp only [execute_RTYPEW_pure, RV64.sraw, sign_extend, Sail.BitVec.signExtend,
    LeanRV64D.Functions.shift_bits_right_arith, Sail.BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd,
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend,
    Nat.add_one_sub_one, Sail.BitVec.toNatInt]
  rfl

/-- The six-bit Sail `SRLI` pure part agrees with the chip's shared RV64 logical-right shift. -/
theorem execute_SHIFTIOP_pure_srli (x y : BitVec 64) :
    Advance.execute_SHIFTIOP_pure x (y.setWidth 6) sop.SRLI = RV64.srl y x := by
  simp only [Advance.execute_SHIFTIOP_pure, RV64.srl, Sail.shift_bits_right]
  rfl

set_option linter.unusedSimpArgs false in
/-- The six-bit Sail `SRAI` pure part agrees with the chip's shared RV64 arithmetic-right shift. -/
theorem execute_SHIFTIOP_pure_srai (x y : BitVec 64) :
    Advance.execute_SHIFTIOP_pure x (y.setWidth 6) sop.SRAI = RV64.sra y x := by
  simp [Advance.execute_SHIFTIOP_pure, RV64.sra, LeanRV64D.Functions.shift_bits_right_arith,
    Sail.BitVec.extractLsb, Sail.BitVec.toNatInt]
  congr 1

/-- The five-bit Sail `SRLIW` pure part agrees with the chip's shared word logical-right shift. -/
theorem execute_SHIFTIWOP_pure_srliw (x y : BitVec 64) :
    Advance.execute_SHIFTIWOP_pure x (y.setWidth 5) sopw.SRLIW = RV64.srlw y x := by
  simp only [Advance.execute_SHIFTIWOP_pure, RV64.srlw, sign_extend,
    Sail.BitVec.signExtend, Sail.shift_bits_right, Sail.BitVec.extractLsb]
  congr 2
  all_goals bv_decide

/-- The five-bit Sail `SRAIW` pure part agrees with the chip's shared word arithmetic-right shift. -/
theorem execute_SHIFTIWOP_pure_sraiw (x y : BitVec 64) :
    Advance.execute_SHIFTIWOP_pure x (y.setWidth 5) sopw.SRAIW = RV64.sraw y x := by
  simp only [Advance.execute_SHIFTIWOP_pure, RV64.sraw, sign_extend,
    Sail.BitVec.signExtend, LeanRV64D.Functions.shift_bits_right_arith, Sail.BitVec.extractLsb,
    Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow,
    BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend,
    Nat.add_one_sub_one, Sail.BitVec.toNatInt]
  congr 2

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SRL): the chip's RV64 `srl` fact plus the register/PC reads drive
`spec_srl ≡ sp1_sr`. -/
theorem correct_srl_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_srl : Word.toBitVec64 a_val
        = RV64.srl (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_srl (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sr (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_srl, sp1_sr]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', execute_RTYPE_pure_srl,
    h_rs1, h_rs2, h_srl]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SRA): the chip's RV64 `sra` fact plus the register/PC reads drive
`spec_sra ≡ sp1_sr`. -/
theorem correct_sra_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_sra : Word.toBitVec64 a_val
        = RV64.sra (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_sra (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sr (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_sra, sp1_sr]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', execute_RTYPE_pure_sra,
    h_rs1, h_rs2, h_sra]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SRLW): the chip's RV64 `srlw` fact plus the register/PC reads drive
`spec_srlw ≡ sp1_sr`. -/
theorem correct_srlw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_srlw : Word.toBitVec64 a_val
        = RV64.srlw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_srlw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sr (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_srlw, sp1_sr]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW', execute_RTYPEW_pure_srlw,
    h_rs1, h_rs2, h_srlw]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (SRAW): the chip's RV64 `sraw` fact plus the register/PC reads drive
`spec_sraw ≡ sp1_sr`. -/
theorem correct_sraw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_sraw : Word.toBitVec64 a_val
        = RV64.sraw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_sraw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sr (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_sraw, sp1_sr]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW', execute_RTYPEW_pure_sraw,
    h_rs1, h_rs2, h_sraw]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: from the chip `Spec`, the 4-way SRL/SRA/SRLW/SRAW Sail identities hold. -/
theorem shiftright_chip_reaches_sail
    (input : ShiftRightChip.Inputs (ZMod p)) (cols : ShiftRightChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : ShiftRightChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.adapter.op_b_memory.prev_value))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.adapter.op_c_memory.prev_value)) :
    (cols.is_srl = 1 →
        (spec_srl (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sr (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_sra = 1 →
        (spec_sra (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sr (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_srlw = 1 →
        (spec_srlw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sr (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_sraw = 1 →
        (spec_sraw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_sr (.Regidx rd_idx) pc cols.a).run s) := by
  obtain ⟨h_srl, h_sra, h_srlw, h_sraw⟩ := h_chip h_real
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact correct_srl_native input.adapter.op_b_memory.prev_value
      input.adapter.op_c_memory.prev_value cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_srl h)
  · exact correct_sra_native input.adapter.op_b_memory.prev_value
      input.adapter.op_c_memory.prev_value cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_sra h)
  · exact correct_srlw_native input.adapter.op_b_memory.prev_value
      input.adapter.op_c_memory.prev_value cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_srlw h)
  · exact correct_sraw_native input.adapter.op_b_memory.prev_value
      input.adapter.op_c_memory.prev_value cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_sraw h)

end SP1Clean.ShiftRightSail

namespace SP1Clean.ShiftRightChip

open SP1Clean.ShiftRightSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The ShiftRight RowView (standalone, shared by `kind.view` and `advance`): straight-line `next_pc`,
the ALU adapter, `cols.a` as the shift-result write, opcode `is_srl·7 + is_sra·8 + is_srlw·22 + is_sraw·23`
(SRL = 7, SRA = 8, SRLW = 22, SRAW = 23). -/
def rowView (inp : Inputs (ZMod p)) (cols : ShiftRightChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23, .regWrite⟩

/-- **`ShiftRightChip.advance`** — the per-row Sail lift for all eight upstream forms:
SRL/SRLI, SRA/SRAI, SRLW/SRLIW, and SRAW/SRAIW.  The four-way selector chooses the operation and the
committed `imm_c` bit chooses the register or immediate Sail constructor. -/
theorem advance (inp : Inputs (ZMod p)) (cols : ShiftRightChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : cols.state.pc[0].val < 2 ^ 16 ∧ inp.adapter = cols.adapter ∧
      (rowView inp cols).adapter.op_a ≠ 0 ∧
      (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
      (cols.adapter.imm_c = 1 →
        cols.adapter.op_c_memory.prev_value = cols.adapter.op_c) ∧
      ((cols.is_srl = 1 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
       (cols.is_sra = 1 ∧ cols.is_srl = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
       (cols.is_srlw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_sraw = 0) ∨
       (cols.is_sraw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0))) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hpc0, hpass, hnonX0, himmc, himmediate, hflag⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.a := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  have hstraight : r.next_pc = #v[r.state.pc[0] + 4, r.state.pc[1], r.state.pc[2]] := rfl
  obtain ⟨hsrl_spec, hsra_spec, hsrlw_spec, hsraw_spec⟩ := hspec hreal'
  simp only [hpass] at hsrl_spec hsra_spec hsrlw_spec hsraw_spec
  rcases himmc with himmc0 | himmc1
  · rcases hflag with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · have hop : r.opcode = ((ropToOpcode rop.SRL).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, ropToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_RTYPE_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) rop.SRL := by
        rw [execute_RTYPE_pure_srl, vrd]
        exact hsrl_spec h1
      exact advance_of_rtype rop.SRL hcfg hrom hpcread hvalb hdecrom hop himmb himmc0
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((ropToOpcode rop.SRA).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, ropToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_RTYPE_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) rop.SRA := by
        rw [execute_RTYPE_pure_sra, vrd]
        exact hsra_spec h1
      exact advance_of_rtype rop.SRA hcfg hrom hpcread hvalb hdecrom hop himmb himmc0
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((ropwToOpcode ropw.SRLW).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, ropwToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_RTYPEW_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) ropw.SRLW := by
        rw [execute_RTYPEW_pure_srlw, vrd]
        exact hsrlw_spec h1
      exact advance_of_rtypew ropw.SRLW hcfg hrom hpcread hvalb hdecrom hop himmb himmc0
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((ropwToOpcode ropw.SRAW).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, ropwToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_RTYPEW_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              (Word.toBitVec64 cols.adapter.op_c_memory.prev_value) ropw.SRAW := by
        rw [execute_RTYPEW_pure_sraw, vrd]
        exact hsraw_spec h1
      exact advance_of_rtypew ropw.SRAW hcfg hrom hpcread hvalb hdecrom hop himmb himmc0
        hnonX0 hpc0 hstraight hval
  · have hopc_eq := himmediate himmc1
    rcases hflag with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · have hop : r.opcode = ((sopToOpcode sop.SRLI).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, sopToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_SHIFTIOP_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              ((Word.toBitVec64 cols.adapter.op_c).setWidth 6) sop.SRLI := by
        rw [execute_SHIFTIOP_pure_srli, vrd, ← hopc_eq]
        exact hsrl_spec h1
      exact advance_of_shiftitype sop.SRLI hcfg hrom hpcread hvalb hdecrom hop himmb himmc1
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((sopToOpcode sop.SRAI).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, sopToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_SHIFTIOP_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              ((Word.toBitVec64 cols.adapter.op_c).setWidth 6) sop.SRAI := by
        rw [execute_SHIFTIOP_pure_srai, vrd, ← hopc_eq]
        exact hsra_spec h1
      exact advance_of_shiftitype sop.SRAI hcfg hrom hpcread hvalb hdecrom hop himmb himmc1
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((sopwToOpcode sopw.SRLIW).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, sopwToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_SHIFTIWOP_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              ((Word.toBitVec64 cols.adapter.op_c).setWidth 5) sopw.SRLIW := by
        rw [execute_SHIFTIWOP_pure_srliw, vrd, ← hopc_eq]
        exact hsrlw_spec h1
      exact advance_of_shiftiwtype sopw.SRLIW hcfg hrom hpcread hvalb hdecrom hop himmb himmc1
        hnonX0 hpc0 hstraight hval
    · have hop : r.opcode = ((sopwToOpcode sopw.SRAIW).toNat : ZMod p) := by
        simp [hr, rowView, h1, h2, h3, h4, sopwToOpcode, Opcode.toNat]
      have hval : Word.toBitVec64 r.rdWrite
          = execute_SHIFTIWOP_pure (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
              ((Word.toBitVec64 cols.adapter.op_c).setWidth 5) sopw.SRAIW := by
        rw [execute_SHIFTIWOP_pure_sraiw, vrd, ← hopc_eq]
        exact hsraw_spec h1
      exact advance_of_shiftiwtype sopw.SRAIW hcfg hrom hpcread hvalb hdecrom hop himmb himmc1
        hnonX0 hpc0 hstraight hval

/-- `ChipKind` registration for ShiftRight (SRL/SRA/SRLW/SRAW). `rs1`/`rs2` are read from the
adapter register read-backs `op_b_memory.prev_value`/`op_c_memory.prev_value`. -/
def kind : Soundness.ChipKind p where
  name := "ShiftRight"
  Inputs := ShiftRightChip.Inputs
  Cols := ShiftRightChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => cols.state.pc[0].val < 2 ^ 16 ∧ inp.adapter = cols.adapter ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧
    (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
    (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c) ∧
    ((cols.is_srl = 1 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
     (cols.is_sra = 1 ∧ cols.is_srl = 0 ∧ cols.is_srlw = 0 ∧ cols.is_sraw = 0) ∨
     (cols.is_srlw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_sraw = 0) ∨
     (cols.is_sraw = 1 ∧ cols.is_srl = 0 ∧ cols.is_sra = 0 ∧ cols.is_srlw = 0))
  advance := some (PLift.up advance)

end SP1Clean.ShiftRightChip
