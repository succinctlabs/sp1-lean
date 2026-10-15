import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.SubwChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for SUBW (+ `ChipKind` registration)

`correct_subw_native` proves the RISC-V Sail `SUBW` execution agrees with the SP1 chip emulation
given the chip's semantic fact `a_val = sext32→64 (op_b - op_c)` and the register/PC reads.
`execute_RTYPEW rs2 rs1 rd .SUBW` computes `sext (rX(rs1)[31:0] - rX(rs2)[31:0])`, so
`rs1 ↦ op_b_val`, `rs2 ↦ op_c_val` — the non-commutative order is load-bearing. -/

open LeanRV64D.Defs
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
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SUBW
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`. -/
def sp1_subw (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
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
  simp only [spec_subw, sp1_subw]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by
    rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW', subw_pure_eq, h_rs1, h_rs2, h_subw]

omit [Fact (2 ^ 17 < p)] in
theorem subw_chip_reaches_sail
    (input : SubwChip.Inputs (ZMod p)) (cols : SubwChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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
    ((h_chip.2.2 h_real).trans
      (SubwChip.rv64_subw_eq (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.SubwSail

namespace SP1Clean.SubwChip

open SP1Clean.SubwSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **SUBW's committed bus view** — the chip-agnostic `RowView` (opcode `20`, the `pc+4` straight-line
next-pc, the sign-extended W result `[v0, v1, msb·65535, msb·65535]` as `rdWrite`). Standalone so
`SubwChip.advance` can be supplied *as* `kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real,
    #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
       cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535], 20, .regWrite⟩

/-- **`SubwChip.advance`** — the per-Subw-row `try_step` lift (SC Phase 4, the **first W-op chip**): the
`execute_RTYPEW` twin of `AddChip.advance`, a thin single-op adapter over the generic `advance_of_rtypew`
(register-only, `RTypeReader`). The only per-chip inputs are the opcode `SUBW` (= 20) and the write-value
identity `hval` — the chip `Spec`'s gated `RV64.subw op_c op_b` conjunct, threaded through `SubwChip.rv64_subw_eq`
+ `subw_pure_eq` into `execute_RTYPEW_pure op_b op_c SUBW` (the low-32 subtract sign-extended to 64). Stated to
match the `ChipKind.advance` obligation exactly, so `kind.advance := some (PLift.up advance)` type-checks. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1)
    (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hnonX0⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
      cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535] := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  have hop : r.opcode = ((ropwToOpcode ropw.SUBW).toNat : ZMod p) := by
    simp [hr, rowView, ropwToOpcode, Opcode.toNat]
  have hval : r.rdWrite.toBitVec64 = execute_RTYPEW_pure r.adapter.op_b_memory.prev_value.toBitVec64
      r.adapter.op_c_memory.prev_value.toBitVec64 ropw.SUBW := by
    have ha := harith hreal'
    simp only [SubwChip.Inputs.op_b_val, SubwChip.Inputs.op_c_val, hlink] at ha
    rw [vrd, vopbm, vopcm, ha, subw_pure_eq]; exact SubwChip.rv64_subw_eq _ _
  exact advance_of_rtypew ropw.SUBW hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- **SUBW's `ChipKind` registration.** Write-word is the sign-extended W result
`[v0, v1, msb·65535, msb·65535]`; Program-bus opcode `20`; adapter is `RTypeReader`.
`advance`/`advanceReady` (SC Phase 4) route to `SubwChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Subw"
  Inputs := SubwChip.Inputs
  Cols := SubwChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady :=fun inp cols _ _ => inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.SubwChip
