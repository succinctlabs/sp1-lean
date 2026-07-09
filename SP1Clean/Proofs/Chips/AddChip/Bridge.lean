import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for Add (+ `ChipKind` registration)

`correct_add_native` proves the RISC-V Sail `ADD` execution agrees with the SP1 chip emulation
given the chip's semantic fact `a_val = op_b + op_c` and the register/PC reads.
`add_chip_reaches_sail` composes `AddChip.Spec` into the bridge; `AddChip.kind` registers Add
rows in the heterogeneous trace and soundness capstone. -/

open LeanRV64D.Defs
namespace SP1Clean.AddSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `ADD`. -/
noncomputable def spec_add (rs2 rs1 rd : regidx) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd`
(x0-uniform via `wX_bits`, exactly as `execute_RTYPE` writes its result). -/
def sp1_add (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
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
    execute_RTYPE_pure, PreLeanRV64D.readReg, PreLeanRV64D.writeReg,
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
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Add's committed bus view** — the chip-agnostic `RowView` (shared reader block, the `pc+4` straight-line
next-pc, `is_real`, the `add_operation` result as `rdWrite`, opcode `0`). Standalone (not inlined in `kind`)
so `AddChip.advance` below — the Phase-4 `try_step` obligation, which references the whole view — can be
stated *before* `kind` and supplied *as* `kind.advance`, breaking the `advance ↔ kind.view` reference cycle. -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.AddCols (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value, 0, .regWrite⟩

/-- **`AddChip.advance`** — the per-Add-row `try_step` lift (SC Phase 4), closing `TargetObligations.lift`
for Add rows: from a state `s` refining the row `rowView inp cols` (`SailConfigured` + `RomLoaded` + the
committed pc), the Memory-bus value bound (`ValueOperandsBound`), the Program-bus fetch truth
(`decodedInROM`), the chip `Spec`, a real-row selector, and the `advanceReady` bundle (the reader-passthrough
`inp.adapter = cols.adapter` + the routing fact `op_a ≠ 0`, both discharged by the trace dispatcher), one
real `try_step` takes `s` to the row's committed `RowEffect`. Hands the generic `advance_of_rtype` the ADD
opcode fact and the write-value identity (chip `Spec`'s gated `RV64.add` conjunct +
`rv64add_eq_execute_RTYPE_pure`, threading the passthrough link). This proof **is** `kind.advance` below —
stated to match the `ChipKind.advance` obligation exactly (`view := rowView`, `advanceReady := this bundle`). -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.AddCols (ZMod p)) (data : ProverData (ZMod p))
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
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  obtain ⟨-, hrspec, -, harith⟩ := hspec
  obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
  obtain ⟨-, hpc0, -, -⟩ := hbounds hreal'
  have hop : r.opcode = ((ropToOpcode rop.ADD).toNat : ZMod p) := by
    simp [hr, rowView, ropToOpcode, Opcode.toNat]
  have hval : Word.toBitVec64 r.rdWrite
      = execute_RTYPE_pure (Word.toBitVec64 r.adapter.op_b_memory.prev_value)
          (Word.toBitVec64 r.adapter.op_c_memory.prev_value) rop.ADD := by
    have hidentity := harith hreal'
    simp only [AddChip.Inputs.op_b_val, AddChip.Inputs.op_c_val, hlink] at hidentity
    rw [vrd, vopbm, vopcm, hidentity, rv64add_eq_execute_RTYPE_pure]
  exact advance_of_rtype rop.ADD hcfg hrom hpcread hvalb hdecrom hop rfl rfl hnonX0 hpc0 rfl hval

/-- **Add's `ChipKind` registration** — enters Add rows into the heterogeneous trace and the soundness
capstone. `sailEquiv`/`reaches_sail` route to `add_chip_reaches_sail`; `advance`/`advanceReady` (SC Phase 4)
route to `AddChip.advance` (the uniform `try_step` lift). -/
def kind : Soundness.ChipKind p where
  name := "Add"
  Inputs := AddChip.Inputs
  Cols := Extracted.AddCols
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (spec_add (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_add (.Regidx rd) pc cols.add_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    add_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.AddChip
