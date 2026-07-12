import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.MulChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance
import RISCV.Instructions
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # Native Sail bridge for the `Mul` chip (MUL/MULH/MULHU/MULHSU/MULW) + `ChipKind`

The SP1 emulation of a multiply row is opcode-agnostic (`sp1_mul`: write `nextPC = pc + 4` and the
result register `rd`); the RISC-V Sail spec differs by variant — `spec_mul` (low 64 of the signed
product), `spec_mulh` (high 64, signed×signed), `spec_mulhu` (high 64, unsigned×unsigned), `spec_mulhsu`
(high 64, signed×unsigned), `spec_mulw` (low-32 product sign-extended). The five variants are the four
`MUL` `mul_op` records (Low/High × the signedness pair) plus `MULW`.

This bridge uses the **RV64 provider library's** connection lemmas directly:
`_root_.mul_eq`/`_root_.mulw_eq` (`RISCV.SailToRV64`) chained with
`RV64.{mul,mulh,mulhu,mulhsu,mulw}_eq` (`RISCV.SailPureToInstructions`, fully proven incl. the
MULHSU signed×unsigned high half). `correct_mul*_native` is pure monad plumbing — the BitVec
algebra lives in those dep lemmas.

The chip `Spec` sources operands from **inputs** `op_b_val` (rs1) / `op_c_val` (rs2), matching
the RV64 signature `f rs2_val rs1_val`. The `ChipKind`'s `sailEquiv` is the 5-way flag-dispatched
conjunction. `Mul` carries `Fact (2 ^ 24 < p)`; the bridge derives `Fact (2 ^ 17 < p)` locally. -/

open LeanRV64D.Defs
namespace SP1Clean.MulSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- The `MUL` `mul_op`: low 64 bits, signed × signed. -/
def mulOp_mul : mul_op := { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed }
/-- The `MULH` `mul_op`: high 64 bits, signed × signed. -/
def mulOp_mulh : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
/-- The `MULHU` `mul_op`: high 64 bits, unsigned × unsigned. -/
def mulOp_mulhu : mul_op := { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
/-- The `MULHSU` `mul_op`: high 64 bits, signed × unsigned. -/
def mulOp_mulhsu : mul_op := { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MUL` (low 64, signed×signed). -/
noncomputable def spec_mul (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mul
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULH` (high 64, signed×signed). -/
noncomputable def spec_mulh (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulh
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULHU` (high 64, unsigned×unsigned). -/
noncomputable def spec_mulhu (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulhu
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULHSU` (high 64, signed×unsigned). -/
noncomputable def spec_mulhsu (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd mulOp_mulhsu
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `MULW` (low-32 product, sext). -/
noncomputable def spec_mulw (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_MULW rs2 rs1 rd
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for the five multiply variants): write `nextPC = pc + 4`
and the result register `rd` (the multiply result word's 64-bit value). -/
def sp1_mul (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MUL): the chip's RV64 `mul` fact plus the register/PC reads drive
`spec_mul ≡ sp1_mul`, via `_root_.mul_eq` (`execute_MUL = skeleton_binary … SailRV64.mul`) and
`RV64.mul_eq` (`SailRV64.mul {Low,S,S} = RV64.mul`). -/
theorem correct_mul_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mul : Word.toBitVec64 a_val
        = RV64.mul (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mul (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_mul, sp1_mul, mulOp_mul]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.mul_eq, RV64.mul_eq, skeleton_binary, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_mul]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULH): the chip's RV64 `mulh` fact drives `spec_mulh ≡ sp1_mul`. -/
theorem correct_mulh_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulh : Word.toBitVec64 a_val
        = RV64.mulh (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulh (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_mulh, sp1_mul, mulOp_mulh]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.mul_eq, RV64.mulh_eq, skeleton_binary, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_mulh]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULHU): the chip's RV64 `mulhu` fact drives `spec_mulhu ≡ sp1_mul`. -/
theorem correct_mulhu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulhu : Word.toBitVec64 a_val
        = RV64.mulhu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulhu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_mulhu, sp1_mul, mulOp_mulhu]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.mul_eq, RV64.mulhu_eq, skeleton_binary, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_mulhu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULHSU): the chip's RV64 `mulhsu` fact drives `spec_mulhsu ≡ sp1_mul`. -/
theorem correct_mulhsu_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulhsu : Word.toBitVec64 a_val
        = RV64.mulhsu (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulhsu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_mulhsu, sp1_mul, mulOp_mulhsu]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.mul_eq, RV64.mulhsu_eq, skeleton_binary, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_mulhsu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 24 < p)] in
/-- Native Sail equivalence (MULW): the chip's RV64 `mulw` fact drives `spec_mulw ≡ sp1_mul`, via
`_root_.mulw_eq` and `RV64.mulw_eq`. -/
theorem correct_mulw_native
    (rs1_val rs2_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 rs1_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 rs2_val))
    (h_mulw : Word.toBitVec64 a_val
        = RV64.mulw (Word.toBitVec64 rs2_val) (Word.toBitVec64 rs1_val)) :
    (spec_mulw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_mul (.Regidx rd_idx) pc a_val).run s := by
  simp only [spec_mulw, sp1_mul]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun]
  simp [_root_.mulw_eq, RV64.mulw_eq, skeleton_binary, Sail.run_rX_bits, Sail.run_wX_bits,
    run_writeReg_bind, SailState.get_reg?_insert_nextPC, h_rs1, h_rs2, h_mulw]

omit [Fact (2 ^ 24 < p)] in
/-- End-to-end: from the chip `Spec`, the 5-way MUL/MULH/MULHU/MULHSU/MULW Sail identities hold. -/
theorem mul_chip_reaches_sail
    (input : MulChip.Inputs (ZMod p)) (cols : Extracted.MulCols (ZMod p))
    (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : MulChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_mul = 1 →
        (spec_mul (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulh = 1 →
        (spec_mulh (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulhu = 1 →
        (spec_mulhu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulhsu = 1 →
        (spec_mulhsu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) ∧
    (cols.is_mulw = 1 →
        (spec_mulw (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_mul (.Regidx rd_idx) pc cols.a).run s) := by
  -- `MulChip.Spec` is now `RTypeReader.Spec ∧ is_real-binary ∧ (is_real = 1 → 5 flag conjuncts)`;
  -- the arithmetic the bridge needs is the third conjunct.
  obtain ⟨h_mul, h_mulh, h_mulhu, h_mulhsu, h_mulw⟩ := h_chip.2.2 h_real
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact correct_mul_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mul h)
  · exact correct_mulh_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulh h)
  · exact correct_mulhu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulhu h)
  · exact correct_mulhsu_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulhsu h)
  · exact correct_mulw_native input.op_b_val input.op_c_val cols.a
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_mulw h)

end SP1Clean.MulSail

namespace SP1Clean.MulChip

open SP1Clean.MulSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- The Mul RowView (shared by `kind.view` and `advance`): straight-line `pc+4` next-pc, the R-type
adapter, `cols.a` as the multiply write, opcode the flag-weighted R-type discriminant
(MUL 11, MULH 12, MULHU 13, MULHSU 14, MULW 24). Standalone so `MulChip.advance` — the Phase-4
`try_step` obligation referencing the whole view — can be stated *before* `kind` and supplied *as*
`kind.advance`, breaking the `advance ↔ kind.view` reference cycle. -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.MulCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.a,
    cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 + cols.is_mulhsu * 14
      + cols.is_mulw * 24, .regWrite⟩

/-- **`MulChip.advance`** — the per-Mul-row `try_step` lift (SC Phase 4), 5-way flag dispatch.
Each branch pins the R-type opcode (`mulOpToOpcode <op>` for MUL/MULH/MULHU/MULHSU, `Opcode.MULW`
for MULW), converts the chip `Spec`'s flag-gated `RV64.<op>` conjunct to the Sail-pure `SailRV64.<op>`
write value (via `RV64.<op>_eq`, the bridge's explicit-`hb` typed pattern), and routes to the matching
`advance_of_mul <op> (canonical)` / `advance_of_mulw`. `himmb`/`himmc`/`hstraight` are `rfl`
(RTypeReader), and `hpc0` comes from the reader `Spec`'s bounds. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.MulCols (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0 ∧
      ((cols.is_mul = 1 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
       (cols.is_mulh = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
       (cols.is_mulhu = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
       (cols.is_mulhsu = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulw = 0) ∨
       (cols.is_mulw = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0))) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hnonX0, hflag⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.a := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hspec.1
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  have hbr := hspec.2.2 hreal'
  rcases hflag with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · -- is_mul
    have hop : r.opcode = ((mulOpToOpcode mulOp_mul).toNat : ZMod p) := by
      simp [hr, rowView, h1, h2, h3, h4, h5, mulOp_mul, mulOpToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) mulOp_mul := by
      have hs := hbr.1 h1
      simp only [MulChip.Inputs.op_c_val, MulChip.Inputs.op_b_val, hlink] at hs
      have hb : SailRV64.mul (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) mulOp_mul
        = RV64.mul (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.mul_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hs
    exact advance_of_mul mulOp_mul (by decide) hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_mulh
    have hop : r.opcode = ((mulOpToOpcode mulOp_mulh).toNat : ZMod p) := by
      simp [hr, rowView, h1, h2, h3, h4, h5, mulOp_mulh, mulOpToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) mulOp_mulh := by
      have hs := hbr.2.1 h1
      simp only [MulChip.Inputs.op_c_val, MulChip.Inputs.op_b_val, hlink] at hs
      have hb : SailRV64.mul (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) mulOp_mulh
        = RV64.mulh (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.mulh_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hs
    exact advance_of_mul mulOp_mulh (by decide) hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_mulhu
    have hop : r.opcode = ((mulOpToOpcode mulOp_mulhu).toNat : ZMod p) := by
      simp [hr, rowView, h1, h2, h3, h4, h5, mulOp_mulhu, mulOpToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) mulOp_mulhu := by
      have hs := hbr.2.2.1 h1
      simp only [MulChip.Inputs.op_c_val, MulChip.Inputs.op_b_val, hlink] at hs
      have hb : SailRV64.mul (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) mulOp_mulhu
        = RV64.mulhu (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.mulhu_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hs
    exact advance_of_mul mulOp_mulhu (by decide) hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_mulhsu
    have hop : r.opcode = ((mulOpToOpcode mulOp_mulhsu).toNat : ZMod p) := by
      simp [hr, rowView, h1, h2, h3, h4, h5, mulOp_mulhsu, mulOpToOpcode, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.mul (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) mulOp_mulhsu := by
      have hs := hbr.2.2.2.1 h1
      simp only [MulChip.Inputs.op_c_val, MulChip.Inputs.op_b_val, hlink] at hs
      have hb : SailRV64.mul (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) mulOp_mulhsu
        = RV64.mulhsu (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.mulhsu_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hs
    exact advance_of_mul mulOp_mulhsu (by decide) hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval
  · -- is_mulw
    have hop : r.opcode = ((Opcode.MULW).toNat : ZMod p) := by
      simp [hr, rowView, h1, h2, h3, h4, h5, Opcode.toNat]
    have hval : Word.toBitVec64 r.rdWrite
        = SailRV64.mulw (Word.toBitVec64 r.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 r.adapter.op_b_memory.prev_value) := by
      have hs := hbr.2.2.2.2 h1
      simp only [MulChip.Inputs.op_c_val, MulChip.Inputs.op_b_val, hlink] at hs
      have hb : SailRV64.mulw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
          (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)
        = RV64.mulw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
            (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) := RV64.mulw_eq _ _
      rw [vrd, vopbm, vopcm, hb]; exact hs
    exact advance_of_mulw hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- `ChipKind` registration for Mul (MUL/MULH/MULHU/MULHSU/MULW). `rs1`/`rs2` are sourced from
inputs `op_b_val`/`op_c_val`. Carries `Fact (2 ^ 24 < p)`. `advance`/`advanceReady` (SC Phase 4)
route to `MulChip.advance` (the uniform 5-way `try_step` lift). -/
def kind : Soundness.ChipKind p where
  name := "Mul"
  Inputs := MulChip.Inputs
  Cols := Extracted.MulCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_mul = 1 →
        (spec_mul (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulh = 1 →
        (spec_mulh (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulhu = 1 →
        (spec_mulhu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulhsu = 1 →
        (spec_mulhsu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s) ∧
    (cols.is_mulw = 1 →
        (spec_mulw (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_mul (.Regidx rd) pc cols.a).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    mul_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧
    ((cols.is_mul = 1 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
     (cols.is_mulh = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
     (cols.is_mulhu = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhsu = 0 ∧ cols.is_mulw = 0) ∨
     (cols.is_mulhsu = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulw = 0) ∨
     (cols.is_mulw = 1 ∧ cols.is_mul = 0 ∧ cols.is_mulh = 0 ∧ cols.is_mulhu = 0 ∧ cols.is_mulhsu = 0))
  advance := some (PLift.up advance)

end SP1Clean.MulChip
