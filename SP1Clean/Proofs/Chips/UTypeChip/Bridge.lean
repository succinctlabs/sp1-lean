import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.UTypeChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance
import Clean.Air.FlatComponent

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
    (input : UTypeChip.Inputs (ZMod p)) (cols : UTypeChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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
    (input : UTypeChip.Inputs (ZMod p)) (cols : UTypeChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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
def rowView (inp : Inputs (ZMod p)) (cols : UTypeChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value,
    inp.is_auipc * 48 + (1 - inp.is_auipc) * 49,
    .destination cols.adapter.op_a_0⟩

/-- **`UTypeChip.advance`** — the per-U-type-row `try_step` lift (SC Phase 4): a 2-branch adapter over
`advance_of_utype` (LUI `is_auipc = 0`, opcode 49; AUIPC `is_auipc = 1`, opcode 48). No register reads
(`imm_b = imm_c = 1`); the write value is the immediate (LUI) or pc-relative (AUIPC, reading the pc via the
shared core's pc-frame). Each branch discharges the `advance_of_utype` write-value obligation from the Spec's
gated `RV64.lui`/`RV64.auipc` conjunct: `immOf_bind` connects the chip's `immOf` to the decoded immediate,
`RV64.lui`/`auipc_eq_add_lui` reduce to the Sail `execute_UTYPE_pure`, and the `pcWord` reassembly ties the
AUIPC pc to `rcvPcOf`. The same table also accepts `rd = x0`; that branch reuses the straight-line
architectural no-write core and does not require a result equation. -/
theorem advance (inp : Inputs (ZMod p)) (cols : UTypeChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (_hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : cols.state.pc[0].val < 2 ^ 16 ∧ (inp.is_auipc = 0 ∨ inp.is_auipc = 1)) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hpc0, hauipc_bin⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  have hlui := hspec.2.2.2.1
  have hauipc := hspec.2.2.2.2
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.add_operation.value := rfl
  have vopb : cols.adapter.op_b_imm = r.adapter.op_b := rfl
  have vopa0 : r.adapter.op_a_0 = cols.adapter.op_a_0 := rfl
  have himmc : r.adapter.imm_c = 1 := rfl
  have reassemble : Word.toBitVec64 (UTypeChip.pcWord cols)
      = pcBitsOfVals (cols.state.pc[0].val) (cols.state.pc[1].val) (cols.state.pc[2].val) := by
    simp only [UTypeChip.pcWord, Word.toBitVec64, pcBitsOfVals]
    congr 1; rw [Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]; ring
  have opAFlag : cols.adapter.op_a_0 = 0 ∨ cols.adapter.op_a_0 = 1 :=
    hspec.1.2.1 hreal'
  rcases opAFlag with hopa0 | hopa1
  · have hnonX0 : r.adapter.op_a ≠ 0 := by
      apply hdecrom.op_a_ne_zero_of_op_a_0_eq_zero
      simpa only [programAccess, ProgramAccess.toRow] using vopa0.trans hopa0
    have commitEq : r.commit = Trace.CommitEffect.regWrite := by
      rw [hr]
      simp [rowView, Trace.CommitEffect.destination, hopa0]
    have hwrites : r.commit.writesReg = true := by
      simp only [commitEq, Trace.CommitEffect.regWrite]
    have hnomem : r.commit.memWrite = none := by
      simp only [commitEq, Trace.CommitEffect.regWrite]
    rcases hauipc_bin with h0 | h1
    · have hop : r.opcode = ((uopToOpcode uop.LUI).toNat : ZMod p) := by
        simp [hr, rowView, h0, uopToOpcode, Opcode.toNat]
      refine advance_of_utype uop.LUI hcfg hrom hpcread hdecrom hop himmc hnonX0 hpc0 rfl ?_
        (hwrites := hwrites) (hnomem := hnomem)
      intro imm hopb
      have himmof : UTypeChip.immOf cols.adapter = imm :=
        immOf_bind imm cols.adapter (vopb.trans hopb)
      rw [vrd, hlui hreal' hopa0 h0, himmof]
      simp [execute_UTYPE_pure, RV64.lui, sign_extend]
    · have hop : r.opcode = ((uopToOpcode uop.AUIPC).toNat : ZMod p) := by
        simp [hr, rowView, h1, uopToOpcode, Opcode.toNat]
      refine advance_of_utype uop.AUIPC hcfg hrom hpcread hdecrom hop himmc hnonX0 hpc0 rfl ?_
        (hwrites := hwrites) (hnomem := hnomem)
      intro imm hopb
      have himmof : UTypeChip.immOf cols.adapter = imm :=
        immOf_bind imm cols.adapter (vopb.trans hopb)
      have hpcword : Word.toBitVec64 (UTypeChip.pcWord cols) = rcvPcOf (stateAccess r) :=
        reassemble
      rw [vrd, hauipc hreal' hopa0 h1, himmof, hpcword, UTypeChip.auipc_eq_add_lui]
      simp [execute_UTYPE_pure, RV64.lui, sign_extend]
  · have hopaZero : r.adapter.op_a = 0 := by
      apply hdecrom.op_a_eq_zero_of_op_a_0_eq_one
      simpa only [programAccess, ProgramAccess.toRow] using vopa0.trans hopa1
    have commitEq : r.commit = Trace.CommitEffect.noWrite := by
      rw [hr]
      simp [rowView, Trace.CommitEffect.destination, hopa1]
    have hnowrite : r.commit.writesReg = false := by
      simp only [commitEq, Trace.CommitEffect.noWrite]
    have hnomem : r.commit.memWrite = none := by
      simp only [commitEq, Trace.CommitEffect.noWrite]
    rcases hauipc_bin with h0 | h1
    · have hop : r.opcode = ((uopToOpcode uop.LUI).toNat : ZMod p) := by
        simp [hr, rowView, h0, uopToOpcode, Opcode.toNat]
      exact advance_of_utype_x0 uop.LUI hcfg hrom hpcread hdecrom hop himmc hopaZero
        hpc0 rfl hnowrite hnomem
    · have hop : r.opcode = ((uopToOpcode uop.AUIPC).toNat : ZMod p) := by
        simp [hr, rowView, h1, uopToOpcode, Opcode.toNat]
      exact advance_of_utype_x0 uop.AUIPC hcfg hrom hpcread hdecrom hop himmc hopaZero
        hpc0 rfl hnowrite hnomem

/-- U-type's `ChipKind` registration. `view` threads straight-line `next_pc`, J-type adapter, opcode
`is_auipc·48 + (1-is_auipc)·49`; `advance` dispatches the LUI/AUIPC cases through
`advance_of_utype`/`advance_of_utype_x0` + `immOf_bind` (the `utype_chip_reaches_sail_*` lemmas are
retained as local bridge helpers, not consumed by the `advance` path). -/
def kind : Soundness.ChipKind p where
  name := "UType"
  Inputs := UTypeChip.Inputs
  Cols := UTypeChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => cols.state.pc[0].val < 2 ^ 16 ∧
    (inp.is_auipc = 0 ∨ inp.is_auipc = 1)
  advance := some (PLift.up advance)

/-! ## Physical row view and the ECALL opcode exclusion -/

open Air.Flat Circuit

omit [Fact (2 ^ 17 < p)] in
/-- The `x - y` Equality-gadget constraint is among the gadget's deep constraints (as
`LtChip`'s grounding contracts). -/
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

/-- The `is_auipc` boolean gate is among the physical U-type circuit's deep constraints. -/
private theorem isAuipcGate_mem_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) :
    input.is_auipc * (input.is_auipc - 1) - 0 ∈
      ((UTypeChip.main input).operations offset).constraints := by
  simp only [UTypeChip.main, circuit_norm]
  right; right; right; right; right; right; right; left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_auipc * (input.is_auipc - 1)) (0 : Expression (ZMod p)) _

omit [Fact (2 ^ 17 < p)] in
/-- Evaluation of U-type's committed `is_auipc` selector, exposed without decomposing the row. -/
private theorem eval_isAuipc (env : Environment (ZMod p))
    (input : Inputs (Expression (ZMod p))) :
    (Eval.eval env input).is_auipc = Expression.eval env input.is_auipc := by
  simpa only [CircuitType.eval_expr] using
    congrArg (fun value : Inputs (ZMod p) => value.is_auipc) (UTypeChip.eval_inputs env input)

/-- The physical U-type constraints force the committed `is_auipc` selector binary. -/
theorem isAuipcBinary_of_mainConstraints (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((UTypeChip.main input).operations offset).ConstraintsHold env) :
    Expression.eval env input.is_auipc = 0 ∨ Expression.eval env input.is_auipc = 1 := by
  have gate : Expression.eval env (input.is_auipc * (input.is_auipc - 1) - 0) = 0 :=
    constraints.1 _ (isAuipcGate_mem_constraints input offset)
  simp only [eval_sub, Expression.eval, sub_zero] at gate
  exact bool_of_mul_pred gate

/-- The completed U-type columns at one physical component row. -/
noncomputable def physicalCols (env : Environment (ZMod p)) : Columns (ZMod p) :=
  (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed U-type row view at one physical component row. -/
noncomputable def physicalView (env : Environment (ZMod p)) : Trace.RowView (ZMod p) :=
  rowView ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) (physicalCols env)

/-- Small-literal disequality against the `ECALL` discriminant `50`, via `ZMod.val` injectivity. -/
private theorem utypeOpcodeLiteral_ne_ecall {k : ℕ} (hk : k < 2 ^ 17) (hne : k ≠ 50) :
    ((k : ℕ) : ZMod p) ≠ (50 : ZMod p) := by
  intro h
  have hp := Fact.out (p := 2 ^ 17 < p)
  apply hne
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega),
    show (50 : ZMod p) = ((50 : ℕ) : ZMod p) from by norm_cast,
    ZMod.val_natCast_of_lt (show (50 : ℕ) < p by omega)] at hval

/-- A real physical U-type row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (_real : (physicalView env).is_real = 1) :
    (physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var Inputs (ZMod p) := varFromOffset Inputs 0
  let offset := size Inputs
  have mainConstraints : ((UTypeChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have binary := isAuipcBinary_of_mainConstraints input offset env mainConstraints
  have inputEq : Eval.eval env input =
      (⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset Inputs 0 env
  have viewOpcode : (physicalView env).opcode =
      (Eval.eval env input).is_auipc * 48 + (1 - (Eval.eval env input).is_auipc) * 49 := by
    simpa only [physicalView, rowView] using
      congrArg (fun value : Inputs (ZMod p) =>
        value.is_auipc * 48 + (1 - value.is_auipc) * 49) inputEq.symm
  rw [viewOpcode, eval_isAuipc env input]
  rcases binary with h0 | h1
  · rw [h0]
    simpa using utypeOpcodeLiteral_ne_ecall (k := 49) (by norm_num) (by norm_num)
  · rw [h1]
    simpa using utypeOpcodeLiteral_ne_ecall (k := 48) (by norm_num) (by norm_num)

end SP1Clean.UTypeChip
