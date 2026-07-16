import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.UTypeChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for U-type (`LUI` / `AUIPC`) (+ `ChipKind` registration)

`correct_utype_{lui,auipc}_native` prove `execute_UTYPE ≡ sp1_utype` given the chip's semantic fact (the
committed result is `RV64.lui imm` / `RV64.auipc imm pc`). The Sail `sign_extend (imm ++ 0#12)` is
definitionally `RV64.lui imm`. The 20-bit immediate `imm` is the column-derived `UTypeChip.immOf`. -/

open LeanRV64D.Defs
namespace SP1Clean.UTypeSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `UTYPE` (which writes `RV64.lui imm`
for LUI, `PC + RV64.lui imm` for AUIPC, to `rd`). -/
noncomputable def spec_utype (imm : BitVec 20) (rd : regidx) (op : uop) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_UTYPE imm rd op
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd` (the committed result word's
64-bit value, x0-uniform via `wX_bits`). -/
def sp1_utype (rd : regidx) (pc : BitVec 64) (result : Word (ZMod p)) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 result)

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for LUI: the committed result is `RV64.lui imm` (= the Sail `off`), so the Sail
`LUI` execution agrees with the SP1 chip emulation. LUI reads no PC, so it reduces directly. -/
theorem correct_utype_lui_native
    (result : Word (ZMod p)) (rd : BitVec 5) (imm : BitVec 20) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_result : Word.toBitVec64 result = RV64.lui imm) :
    (spec_utype imm (.Regidx rd) uop.LUI).run s = (sp1_utype (.Regidx rd) pc result).run s := by
  simp [spec_utype, sp1_utype, execute_UTYPE, sign_extend, Sail.BitVec.signExtend, RV64.lui,
    Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, run_readReg _ Register.PC, h_pc, h_result]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for AUIPC: the committed result is `RV64.auipc imm pc` (= `pc + off`, via
`auipc_eq_add_lui`), and AUIPC reads `PC = pc` (the `nextPC` write does not touch `PC`), so the Sail `AUIPC`
execution agrees with the SP1 chip emulation. -/
theorem correct_utype_auipc_native
    (result : Word (ZMod p)) (rd : BitVec 5) (imm : BitVec 20) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_result : Word.toBitVec64 result = RV64.auipc imm pc) :
    (spec_utype imm (.Regidx rd) uop.AUIPC).run s = (sp1_utype (.Regidx rd) pc result).run s := by
  rw [UTypeChip.auipc_eq_add_lui] at h_result
  simp [spec_utype, sp1_utype, execute_UTYPE, get_arch_pc, sign_extend, Sail.BitVec.signExtend, RV64.lui,
    Sail.run_wX_bits, Std.ExtDHashMap.get?_insert, run_readReg _ Register.PC,
    SailState.get_reg?_insert_nextPC, h_pc, h_result]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for U-type to `x0` (`lui x0` / `auipc x0`). When `rd = x0` the result write is a
no-op on both sides (`wX_bits 0` is dropped in RV64) and U-type touches nothing but `nextPC = pc + 4`, so
the row reaches Sail for **either** op with no result fact — which is why the chip leaves
`add_operation.value` unconstrained on `op_a_0 = 1` rows. -/
theorem correct_utype_native_x0
    (result : Word (ZMod p)) (imm : BitVec 20) (pc : BitVec 64) (s : SailState) (op : uop)
    (h_pc : s.regs.get? Register.PC = some pc) :
    (spec_utype imm (.Regidx 0#5) op).run s = (sp1_utype (.Regidx 0#5) pc result).run s := by
  cases op <;>
    simp [spec_utype, sp1_utype, execute_UTYPE, get_arch_pc, sign_extend, Sail.BitVec.signExtend, RV64.lui,
      Sail.run_wX_bits, Std.ExtDHashMap.get?_insert, run_readReg _ Register.PC,
      SailState.get_reg?_insert_nextPC, h_pc]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (LUI): a real U-type chip row with `is_auipc = 0` reaches the Sail `LUI`, for `rd ≠ x0`
(`op_a_0 = 0`, result proven) **or** `lui x0` (`op_a_0 = 1 ∧ rd = x0`, result write a no-op). -/
theorem utype_chip_reaches_sail_lui
    (input : UTypeChip.Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_iaui0 : input.is_auipc = 0)
    (h_op_a : cols.adapter.op_a_0 = 0 ∨ (cols.adapter.op_a_0 = 1 ∧ rd = 0#5))
    (h_chip : UTypeChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc) :
    (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.LUI).run s
      = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s := by
  rcases h_op_a with h_op0 | ⟨_, hrd0⟩
  · exact correct_utype_lui_native cols.add_operation.value rd (UTypeChip.immOf cols.adapter) pc s h_pc
      (h_chip.2.2.2.1 h_real h_op0 h_iaui0)
  · subst hrd0
    exact correct_utype_native_x0 cols.add_operation.value (UTypeChip.immOf cols.adapter) pc s uop.LUI h_pc

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (AUIPC): a real U-type chip row with `is_auipc = 1` reaches the Sail `AUIPC`, for `rd ≠ x0`
(`op_a_0 = 0`, result proven) **or** `auipc x0` (`op_a_0 = 1 ∧ rd = x0`, result write a no-op). -/
theorem utype_chip_reaches_sail_auipc
    (input : UTypeChip.Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_iaui1 : input.is_auipc = 1)
    (h_op_a : cols.adapter.op_a_0 = 0 ∨ (cols.adapter.op_a_0 = 1 ∧ rd = 0#5))
    (h_chip : UTypeChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_pcw : Word.toBitVec64 (UTypeChip.pcWord cols) = pc) :
    (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.AUIPC).run s
      = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s := by
  rcases h_op_a with h_op0 | ⟨_, hrd0⟩
  · have hr := h_chip.2.2.2.2 h_real h_op0 h_iaui1
    rw [h_pcw] at hr
    exact correct_utype_auipc_native cols.add_operation.value rd (UTypeChip.immOf cols.adapter) pc s h_pc hr
  · subst hrd0
    exact correct_utype_native_x0 cols.add_operation.value (UTypeChip.immOf cols.adapter) pc s uop.AUIPC h_pc

end SP1Clean.UTypeSail

namespace SP1Clean.UTypeChip

open SP1Clean.UTypeSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **The `immOf` immediate binding.** `immOf`'s limb extraction (`op_b_imm[0]/4096 + op_b_imm[1]·16`)
recovers the decoded immediate `imm` exactly when `op_b_imm` is the canonical encoding
`bitVecToWord ((imm.signExtend 64) <<< 12)` (which `decodesUType` supplies). Axiom-clean (`omega`, no
`bv_decide`) — the low-4/high-16 limb split inverts the `<< 12` shift. This is the fact the chip's
deliberately-opaque `immOf` finally connects to the Sail decode. -/
lemma immOf_bind (imm : BitVec 20) (adapter : Extracted.JTypeReader (ZMod p))
    (h : adapter.op_b_imm = bitVecToWord ((imm.signExtend 64) <<< 12)) :
    UTypeChip.immOf adapter = imm := by
  unfold UTypeChip.immOf; rw [h]
  simp only [bitVecToWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  have hlt : ∀ w : BitVec 16, (w.toNat : ZMod p).val = w.toNat := fun w => by
    rw [ZMod.val_natCast_of_lt]; exact lt_trans w.isLt (by omega)
  rw [hlt, hlt]
  have himm : imm.toNat < 2 ^ 20 := imm.isLt
  have key : (BitVec.extractLsb' 0 16 (BitVec.signExtend 64 imm <<< 12)).toNat / 4096 +
      (BitVec.extractLsb' 16 16 (BitVec.signExtend 64 imm <<< 12)).toNat * 16 = imm.toNat := by
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    split <;> omega
  rw [key]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega

/-- **U-type's committed bus view** — the chip-agnostic `RowView` (opcode `is_auipc·48 + (1-is_auipc)·49`,
the `pc+4` straight-line next-pc, the `add_operation` result as `rdWrite`). Standalone so `UTypeChip.advance`
can be supplied *as* `kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value,
    inp.is_auipc * 48 + (1 - inp.is_auipc) * 49, .regWrite⟩

/-- **`UTypeChip.advance`** — the per-U-type-row `try_step` lift (SC Phase 4): a 2-branch adapter over
`advance_of_utype` (LUI `is_auipc = 0`, opcode 49; AUIPC `is_auipc = 1`, opcode 48). No register reads
(`imm_b = imm_c = 1`); the write value is the immediate (LUI) or pc-relative (AUIPC, reading the pc via the
shared core's pc-frame). Each branch discharges the `advance_of_utype` write-value obligation from the Spec's
gated `RV64.lui`/`RV64.auipc` conjunct: `immOf_bind` connects the chip's `immOf` to the decoded immediate,
`RV64.lui`/`auipc_eq_add_lui` reduce to the Sail `execute_UTYPE_pure`, and the `pcWord` reassembly ties the
AUIPC pc to `rcvPcOf`. The `advanceReady` bundle is the pc-limb bound, the `is_auipc` binary, `op_a_0 = 0`
(`rd ≠ x0`), and `op_a ≠ 0` — all dispatcher-discharged. Stated to match the `ChipKind.advance` obligation. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (_hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : cols.state.pc[0].val < 2 ^ 16 ∧ (inp.is_auipc = 0 ∨ inp.is_auipc = 1) ∧
      cols.adapter.op_a_0 = 0 ∧ (rowView inp cols).adapter.op_a ≠ 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hpc0, hauipc_bin, hopa0, hnonX0⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  have hlui := hspec.2.2.2.1
  have hauipc := hspec.2.2.2.2
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopb : cols.adapter.op_b_imm = r.adapter.op_b := rfl
  have himmc : r.adapter.imm_c = 1 := rfl
  have reassemble : Word.toBitVec64 (UTypeChip.pcWord cols)
      = pcBitsOfVals (cols.state.pc[0].val) (cols.state.pc[1].val) (cols.state.pc[2].val) := by
    simp only [UTypeChip.pcWord, Word.toBitVec64, pcBitsOfVals]
    congr 1; rw [Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]; ring
  rcases hauipc_bin with h0 | h1
  · have hop : r.opcode = ((uopToOpcode uop.LUI).toNat : ZMod p) := by
      simp [hr, rowView, h0, uopToOpcode, Opcode.toNat]
    refine advance_of_utype uop.LUI hcfg hrom hpcread hdecrom hop himmc hnonX0 hpc0 rfl ?_
    intro imm hopb
    have himmof : UTypeChip.immOf cols.adapter = imm := immOf_bind imm cols.adapter (vopb.trans hopb)
    rw [vrd, hlui hreal' hopa0 h0, himmof]; simp [execute_UTYPE_pure, RV64.lui, sign_extend]
  · have hop : r.opcode = ((uopToOpcode uop.AUIPC).toNat : ZMod p) := by
      simp [hr, rowView, h1, uopToOpcode, Opcode.toNat]
    refine advance_of_utype uop.AUIPC hcfg hrom hpcread hdecrom hop himmc hnonX0 hpc0 rfl ?_
    intro imm hopb
    have himmof : UTypeChip.immOf cols.adapter = imm := immOf_bind imm cols.adapter (vopb.trans hopb)
    have hpcword : Word.toBitVec64 (UTypeChip.pcWord cols) = rcvPcOf (stateAccess r) := reassemble
    rw [vrd, hauipc hreal' hopa0 h1, himmof, hpcword, UTypeChip.auipc_eq_add_lui]
    simp [execute_UTYPE_pure, RV64.lui, sign_extend]

/-- U-type's `ChipKind` registration. `view` threads straight-line `next_pc`, J-type adapter, opcode
`is_auipc·48 + (1-is_auipc)·49`; `advance` dispatches the LUI/AUIPC cases through the corresponding local
Sail bridge helpers. -/
def kind : Soundness.ChipKind p where
  name := "UType"
  Inputs := UTypeChip.Inputs
  Cols := Extracted.UTypeColumns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => cols.state.pc[0].val < 2 ^ 16 ∧
    (inp.is_auipc = 0 ∨ inp.is_auipc = 1) ∧ cols.adapter.op_a_0 = 0 ∧
    (rowView inp cols).adapter.op_a ≠ 0
  advance := some (PLift.up advance)

end SP1Clean.UTypeChip
