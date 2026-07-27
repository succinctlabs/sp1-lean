import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.LtChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for the unified `Lt` chip (SLT + SLTU) + `ChipKind`

`sp1_lt` is opcode-agnostic; the RISC-V Sail specs differ by variant (`spec_slt`/`spec_sltu`).
`correct_sltu_native` and `correct_slt_native` (both proven and axiom-clean) route the chip's
semantic RV64 `sltu`/`slt` facts into the respective Sail executions. `lt_chip_reaches_sail` proves
the flag-dispatched conjunction from the chip `Spec`. -/

open LeanRV64D.Defs
namespace SP1Clean.LtSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLTU`. -/
noncomputable def spec_sltu (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLTU
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLT` (signed). -/
noncomputable def spec_slt (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLT
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for SLT/SLTU): write `nextPC = pc + 4` and the result
register `rd` (the set-less-than result word's 64-bit value). -/
def sp1_lt (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unnecessarySeqFocus false in
/-- The Sail `SLTU` pure part is the clean RV64 `sltu` (operand order `rs2 rs1`): both place the
unsigned-less-than indicator (`rs1 <ᵤ rs2`) zero-extended to 64 bits. -/
theorem execute_RTYPE_pure_sltu (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SLTU = RV64.sltu y x := by
  apply BitVec.eq_of_toNat_eq
  simp only [execute_RTYPE_pure, RV64.sltu, zero_extend, Sail.BitVec.zeroExtend,
    bool_to_bit, bool_bit_forwards, zopz0zI_u, BitVec.toNatInt, BitVec.toNat_setWidth,
    BitVec.toNat_ofBool, BitVec.ult]
  by_cases h : x.toNat < y.toNat <;> simp_all [Nat.cast_lt] <;>
    cases h2 : x.toNat <b y.toNat <;> rfl

set_option linter.unnecessarySeqFocus false in
/-- The Sail `SLT` pure part is the clean RV64 `slt` (operand order `rs2 rs1`): both place the
signed-less-than indicator (`rs1 <ₛ rs2`) zero-extended to 64 bits. -/
theorem execute_RTYPE_pure_slt (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SLT = RV64.slt y x := by
  apply BitVec.eq_of_toNat_eq
  simp only [execute_RTYPE_pure, RV64.slt, zero_extend, Sail.BitVec.zeroExtend,
    bool_to_bit, bool_bit_forwards, zopz0zI_s, BitVec.slt]
  cases h2 : x.toInt <b y.toInt <;> simp_all

/-- The immediate and register signed-less-than pure operations share the same bit-level body. -/
theorem execute_ITYPE_pure_slti (x y : BitVec 64) :
    SP1Clean.Advance.execute_ITYPE_pure x y iop.SLTI = RV64.slt y x := by
  rw [show SP1Clean.Advance.execute_ITYPE_pure x y iop.SLTI =
      execute_RTYPE_pure x y rop.SLT from rfl,
    execute_RTYPE_pure_slt]

/-- The immediate and register unsigned-less-than pure operations share the same bit-level body. -/
theorem execute_ITYPE_pure_sltiu (x y : BitVec 64) :
    SP1Clean.Advance.execute_ITYPE_pure x y iop.SLTIU = RV64.sltu y x := by
  rw [show SP1Clean.Advance.execute_ITYPE_pure x y iop.SLTIU =
      execute_RTYPE_pure x y rop.SLTU from rfl,
    execute_RTYPE_pure_sltu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (unsigned): the chip's semantic RV64 `sltu` fact (`h_sltu`) plus the
register/PC reads drive `spec_sltu ≡ sp1_lt`, with no SP1Chips borrow. -/
theorem correct_sltu_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_sltu : Word.toBitVec64 a_val
        = RV64.sltu (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_sltu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_sltu, sp1_lt]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', execute_RTYPE_pure_sltu,
    h_rs1, h_rs2, h_sltu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (signed): `h_slt` plus register/PC reads drive `spec_slt ≡ sp1_lt`,
via the `execute_RTYPE_pure_slt` Sail-side identity. -/
theorem correct_slt_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_slt : Word.toBitVec64 a_val
        = RV64.slt (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_slt (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_slt, sp1_lt]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', execute_RTYPE_pure_slt,
    h_rs1, h_rs2, h_slt]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLTI` (I-type signed
less-than-immediate). -/
noncomputable def spec_slti (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTI
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLTIU` (unsigned). -/
noncomputable def spec_sltiu (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd iop.SLTIU
  pure ()

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (signed immediate `SLTI`): the chip's RV64 `slt` fact (`h_slt`, with the
immediate operand `op_c_val` bound to `sign_extend imm` via `h_dec`) plus the rs1/PC reads drive
`spec_slti ≡ sp1_lt`. The Sail `SLTI` arm `zero_extend (bool_to_bit (zopz0zI_s (rX rs1) immext))` is the
same body as the `execute_RTYPE_pure .SLT`, so `execute_RTYPE_pure_slt` retires it. -/
theorem correct_slti_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_slt : Word.toBitVec64 a_val
        = RV64.slt (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_slti imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 a_val
      = zero_extend (m := 64) (bool_to_bit (zopz0zI_s (Word.toBitVec64 op_b_val)
          (sign_extend (m := 64) imm))) := by
    rw [h_slt, ← h_dec, ← execute_RTYPE_pure_slt]; simp [execute_RTYPE_pure]
  simp only [spec_slti, sp1_lt]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', SP1Clean.Advance.execute_ITYPE_pure, h_rs1, harm]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (unsigned immediate `SLTIU`): `h_sltu` + rs1/PC reads drive
`spec_sltiu ≡ sp1_lt`, via the `execute_RTYPE_pure_sltu` Sail-side identity. -/
theorem correct_sltiu_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_sltu : Word.toBitVec64 a_val
        = RV64.sltu (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_sltiu imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 a_val
      = zero_extend (m := 64) (bool_to_bit (zopz0zI_u (Word.toBitVec64 op_b_val)
          (sign_extend (m := 64) imm))) := by
    rw [h_sltu, ← h_dec, ← execute_RTYPE_pure_sltu]; simp [execute_RTYPE_pure]
  simp only [spec_sltiu, sp1_lt]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', SP1Clean.Advance.execute_ITYPE_pure, h_rs1, harm]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: a real `Lt` chip row reaches the RISC-V Sail set-less-than, flag-dispatched.
Both SLT and SLTU conjuncts are proven and axiom-clean. -/
theorem lt_chip_reaches_sail
    (input : LtChip.Inputs (ZMod p)) (cols : LtChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : LtChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_slt = 1 →
        (spec_slt (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) ∧
    (cols.is_sltu = 1 →
        (spec_sltu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) := by
  obtain ⟨-, -, h_gated⟩ := h_chip
  refine ⟨fun hslt => ?_, fun hsltu => ?_⟩
  · exact correct_slt_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_gated h_real).1 hslt)
  · exact correct_sltu_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_gated h_real).2 hsltu)

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (immediate forms SLTI/SLTIU): a real `Lt` chip row whose `op_c` operand is the
sign-extended 12-bit immediate (`h_dec`, supplied at the bridge from the program bus) reaches the RISC-V
Sail I-type set-less-than, flag-dispatched. The chip's `Spec` proves the same RV64 `slt`/`sltu` equation for
immediate (`imm_c = 1`) rows as for register rows, so both conjuncts are proven and axiom-clean. -/
theorem lt_chip_reaches_sail_imm
    (input : LtChip.Inputs (ZMod p)) (cols : LtChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : LtChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm) :
    (cols.is_slt = 1 →
        (spec_slti imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) ∧
    (cols.is_sltu = 1 →
        (spec_sltiu imm (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) := by
  obtain ⟨-, -, h_gated⟩ := h_chip
  refine ⟨fun hslt => ?_, fun hsltu => ?_⟩
  · exact correct_slti_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec ((h_gated h_real).1 hslt)
  · exact correct_sltiu_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec ((h_gated h_real).2 hsltu)

end SP1Clean.LtSail

namespace SP1Clean.LtChip

open SP1Clean.LtSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Lt's committed bus view** — the chip-agnostic `RowView` (opcode `is_slt·9 + is_sltu·10`, the `pc+4`
straight-line next-pc, the comparison `resultWord` as `rdWrite`). Standalone so `LtChip.advance` can be
supplied *as* `kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : LtChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, resultWord cols,
    cols.is_slt * 9 + cols.is_sltu * 10, .regWrite⟩

/-- **`LtChip.advance`** — the four-way SLT/SLTU/SLTI/SLTIU lift. The opcode flags choose signedness;
the committed `imm_c` bit chooses register or immediate decoding. The arithmetic always consumes SP1's
`op_c_memory.prev_value`; on immediate rows the retained `ALUTypeReader` constraints bind that word to
the decoded `op_c` immediate before `advance_of_itype` is applied. -/
theorem advance (inp : Inputs (ZMod p)) (cols : LtChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1)
    (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
      (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
      ((cols.is_slt = 1 ∧ cols.is_sltu = 0) ∨ (cols.is_slt = 0 ∧ cols.is_sltu = 1)) ∧
      (rowView inp cols).adapter.op_a ≠ 0 ∧
      (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c)) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hpc0, himmc, hflag, hnonX0, himmbind⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = resultWord cols := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  have vopc : r.adapter.op_c = cols.adapter.op_c := rfl
  obtain ⟨-, -, hgated⟩ := hspec
  have hg := hgated hreal'
  rcases hflag with ⟨h_slt, h_sltu0⟩ | ⟨h_slt0, h_sltu⟩
  · have hslt := hg.1 h_slt
    simp only [LtChip.Inputs.op_c_val, LtChip.Inputs.op_b_val, hlink] at hslt
    rcases himmc with register | immediate
    · have hop : r.opcode = ((ropToOpcode rop.SLT).toNat : ZMod p) := by
        simp [hr, rowView, h_slt, h_sltu0, ropToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_RTYPE_pure
          r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c_memory.prev_value.toBitVec64 rop.SLT := by
        rw [execute_RTYPE_pure_slt, vrd, vopbm, vopcm]
        exact hslt
      exact advance_of_rtype rop.SLT hcfg hrom hpcread hvalb hdecrom hop rfl register
        hnonX0 hpc0 rfl hval
    · have binding := himmbind immediate
      rw [binding] at hslt
      have hop : r.opcode = ((iopToOpcode iop.SLTI).toNat : ZMod p) := by
        simp [hr, rowView, h_slt, h_sltu0, iopToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_ITYPE_pure
          r.adapter.op_b_memory.prev_value.toBitVec64 r.adapter.op_c.toBitVec64 iop.SLTI := by
        rw [execute_ITYPE_pure_slti, vrd, vopbm, vopc]
        exact hslt
      exact advance_of_itype iop.SLTI hcfg hrom hpcread hvalb hdecrom hop rfl immediate
        hnonX0 hpc0 rfl hval
  · have hsltu := hg.2 h_sltu
    simp only [LtChip.Inputs.op_c_val, LtChip.Inputs.op_b_val, hlink] at hsltu
    rcases himmc with register | immediate
    · have hop : r.opcode = ((ropToOpcode rop.SLTU).toNat : ZMod p) := by
        simp [hr, rowView, h_slt0, h_sltu, ropToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_RTYPE_pure
          r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c_memory.prev_value.toBitVec64 rop.SLTU := by
        rw [execute_RTYPE_pure_sltu, vrd, vopbm, vopcm]
        exact hsltu
      exact advance_of_rtype rop.SLTU hcfg hrom hpcread hvalb hdecrom hop rfl register
        hnonX0 hpc0 rfl hval
    · have binding := himmbind immediate
      rw [binding] at hsltu
      have hop : r.opcode = ((iopToOpcode iop.SLTIU).toNat : ZMod p) := by
        simp [hr, rowView, h_slt0, h_sltu, iopToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_ITYPE_pure
          r.adapter.op_b_memory.prev_value.toBitVec64 r.adapter.op_c.toBitVec64 iop.SLTIU := by
        rw [execute_ITYPE_pure_sltiu, vrd, vopbm, vopc]
        exact hsltu
      exact advance_of_itype iop.SLTIU hcfg hrom hpcread hvalb hdecrom hop rfl immediate
        hnonX0 hpc0 rfl hval

/-- **Lt's `ChipKind` registration.** Program-bus opcode `is_slt·9 + is_sltu·10`; `advance` dispatches the
**register** SLT/SLTU and **immediate** SLTI/SLTIU cases, with the latter pinned by the committed Program
decode `op_c_val = sign_extend imm`.
A row is register (`imm_c = 0`) or immediate (`imm_c = 1`); the consumer picks the matching conjunct.
`advance`/`advanceReady` (SC Phase 4) route to `LtChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Lt"
  Inputs := LtChip.Inputs
  Cols := LtChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
    (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
    ((cols.is_slt = 1 ∧ cols.is_sltu = 0) ∨ (cols.is_slt = 0 ∧ cols.is_sltu = 1)) ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧
    (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c)
  advance := some (PLift.up advance)

end SP1Clean.LtChip
