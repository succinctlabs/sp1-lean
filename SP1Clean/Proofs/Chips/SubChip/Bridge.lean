import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.SubChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for Sub (+ `ChipKind` registration)

`correct_sub_native` proves the RISC-V Sail `SUB` execution agrees with the SP1 chip emulation
given the chip's semantic fact `a_val = op_b - op_c` and the register/PC reads.
`execute_RTYPE rs2 rs1 rd .SUB` computes `rX(rs1) - rX(rs2)`, so `rs1 ↦ op_b_val`,
`rs2 ↦ op_c_val` — the non-commutative order is load-bearing. -/

namespace SP1Clean.SubSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SUB`. -/
noncomputable def spec_sub (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SUB
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`
(x0-uniform via `wX_bits`, exactly as `execute_RTYPE` writes its result). -/
def sp1_sub (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_sub`) plus the register/PC reads
drive `spec_sub ≡ sp1_sub`, with no SP1Chips borrow. -/
theorem correct_sub_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_sub : Word.toBitVec64 a_val = Word.toBitVec64 op_b_val - Word.toBitVec64 op_c_val) :
    (spec_sub (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sub (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_sub, sp1_sub, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    execute_RTYPE_pure, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_sub]

omit [Fact (2 ^ 17 < p)] in
theorem sub_chip_reaches_sail
    (input : SubChip.Inputs (ZMod p)) (cols : Extracted.SubCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : SubChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_sub (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_sub (.Regidx rd_idx) pc cols.sub_operation.value).run s :=
  correct_sub_native input.op_b_val input.op_c_val cols.sub_operation.value
    rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 (h_chip.2.2.2 h_real)

end SP1Clean.SubSail

namespace SP1Clean.SubChip

open SP1Clean.SubSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Sub's committed bus view** — the chip-agnostic `RowView` (opcode `2`, the `pc+4` straight-line next-pc,
`sub_operation` result as `rdWrite`). Standalone so `SubChip.advance` can be supplied *as* `kind.advance`
(see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.SubCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.sub_operation.value, 2⟩

/-- **The SUB execute identity.** The RV64 `SUB` semantics (`RV64.sub rs2 rs1 = rs1 - rs2`) equal the pure
R-type execute value (`execute_RTYPE_pure op1 op2 SUB = op1 - op2`); the bridge tying `SubChip.Spec`'s
result to the value `advance_of_rtype` writes. The SUB twin of `rv64add_eq_execute_RTYPE_pure`. -/
theorem rv64sub_eq_execute_RTYPE_pure (a b : BitVec 64) :
    RV64.sub b a = execute_RTYPE_pure a b rop.SUB := by
  simp [RV64.sub, execute_RTYPE_pure]

/-- **`SubChip.advance`** — the per-Sub-row `try_step` lift (SC Phase 4), the second migrated chip: a thin
adapter over `advance_of_rtype` with opcode `SUB` + the write-value identity `hval` (from `SubChip.Spec`'s
gated `RV64.sub` conjunct via `rv64sub_eq_execute_RTYPE_pure`). Stated to match the `ChipKind.advance`
obligation exactly, so `kind.advance := some (PLift.up advance)` type-checks directly. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.SubCols (ZMod p)) (data : ProverData (ZMod p))
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
  have vrd : r.rdWrite = cols.sub_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨-, hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  have hop : r.opcode = ((ropToOpcode rop.SUB).toNat : ZMod p) := by
    simp [hr, rowView, ropToOpcode, Opcode.toNat]
  have hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) rop.SUB := by
    have hidentity := harith hreal'
    simp only [SubChip.Inputs.op_b_val, SubChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopcm, hidentity, rv64sub_eq_execute_RTYPE_pure]
  exact advance_of_rtype rop.SUB hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- **Sub's `ChipKind` registration.** Program-bus opcode `2`; `reaches_sail` is `sub_chip_reaches_sail`,
`advance`/`advanceReady` (SC Phase 4) route to `SubChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Sub"
  Inputs := SubChip.Inputs
  Cols := Extracted.SubCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (spec_sub (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_sub (.Regidx rd) pc cols.sub_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    sub_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.SubChip
