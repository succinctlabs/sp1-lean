import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.JalChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for JAL (+ `ChipKind` registration)

`correct_jal_native` proves the RISC-V `execute_JAL` execution agrees with `sp1_jal` given the chip's
jump/link semantic facts and 4-byte alignment. `JalChip.kind.view` threads a **data-dependent**
`next_pc = add_operation.value` — `RowView.next_pc` is computed data, not `pc + 4`. -/

namespace SP1Clean.JalSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: stage `nextPC ← PC + 4`, then execute the Sail `JAL` (which reads that link address,
jumps `PC ← PC + sign_extend imm`, and writes the link to `rd`). -/
noncomputable def spec_jal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_JAL imm rd
  pure ()

/-- The SP1 chip emulation: set `nextPC` to the committed jump target word, and write the committed link
word (`pc + 4`) to `rd` (x0-uniform via `wX_bits`). -/
def sp1_jal (rd : regidx) (_pc : BitVec 64) (next_pc_word op_a_word : Word (ZMod p)) : SailM Unit := do
  set_next_pc (Word.toBitVec64 next_pc_word)
  wX_bits rd (Word.toBitVec64 op_a_word)

omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for JAL. The `jump_to` call retires via `jump_to_of_mod4_eq_zero` (4-byte
alignment ⇒ low-two-bits pass), then `execute_JAL` reads the staged `nextPC = pc + 4`, overwrites it
with the jump target, and writes the link to `rd`, matching `sp1_jal` field-for-field. -/
theorem correct_jal_native
    (_op_b_imm next_pc_word op_a_word : Word (ZMod p))
    (rd : BitVec 5) (imm : BitVec 21) (pc : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_jump : Word.toBitVec64 next_pc_word = pc + sign_extend (m := 64) imm)
    (h_link : Word.toBitVec64 op_a_word = pc + 4#64)
    (h_align : (Word.toBitVec64 next_pc_word).toNat % 4 = 0) :
    (spec_jal imm (.Regidx rd)).run s
      = (sp1_jal (.Regidx rd) pc next_pc_word op_a_word).run s := by
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have key : ∀ (reg : Register) (h : reg ∈ s.regs) (h' : reg ∈ sp.regs),
      reg ≠ Register.nextPC → sp.regs.get reg h' = s.regs.get reg h := by
    intro reg h h' hne
    show (s.regs.insert Register.nextPC (pc + 4#64)).get reg _ = _
    rw [Std.ExtDHashMap.get_insert]; simp [Ne.symm hne]
  have hsp_pc : sp.regs.get Register.PC (hsp_init _) = pc := by
    rw [key Register.PC (hs _) (hsp_init _) (by decide)]; exact hpc_get
  have hsp_npc : sp.regs.get Register.nextPC (hsp_init _) = pc + 4#64 := by
    show (s.regs.insert Register.nextPC (pc + 4#64)).get Register.nextPC _ = _
    rw [Std.ExtDHashMap.get_insert]; simp
  have htgt4 : Word.toBitVec64 next_pc_word % 4#64 = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
  have hjump : EStateM.run (jump_to (pc + sign_extend (m := 64) imm)) sp
      = .ok RETIRE_SUCCESS { sp with regs := sp.regs.insert Register.nextPC (Word.toBitVec64 next_pc_word) } := by
    rw [← h_jump]; exact jump_to_of_mod4_eq_zero _ sp hsp_init htgt4
  simp [spec_jal, sp1_jal, execute_JAL, hsp.symm,
    Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get,
    Sail.run_readReg_bind_of_isInitialized _ _ hsp_init,
    hsp_pc, hjump, RETIRE_SUCCESS, h_jump, h_link]
  simp [hsp]

omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for `jal x0` (the `j` pseudo-instruction). When `rd = x0` the link write is a
no-op on both sides (`wX_bits 0` is dropped in RV64), so only the jump must match — `h_link` is not needed,
which is exactly why the chip leaves `op_a_operation.value` unconstrained on `op_a_0 = 1` rows. -/
theorem correct_jal_native_x0
    (_op_b_imm next_pc_word op_a_word : Word (ZMod p))
    (imm : BitVec 21) (pc : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_jump : Word.toBitVec64 next_pc_word = pc + sign_extend (m := 64) imm)
    (h_align : (Word.toBitVec64 next_pc_word).toNat % 4 = 0) :
    (spec_jal imm (.Regidx 0#5)).run s
      = (sp1_jal (.Regidx 0#5) pc next_pc_word op_a_word).run s := by
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  have key : ∀ (reg : Register) (h : reg ∈ s.regs) (h' : reg ∈ sp.regs),
      reg ≠ Register.nextPC → sp.regs.get reg h' = s.regs.get reg h := by
    intro reg h h' hne
    show (s.regs.insert Register.nextPC (pc + 4#64)).get reg _ = _
    rw [Std.ExtDHashMap.get_insert]; simp [Ne.symm hne]
  have hsp_pc : sp.regs.get Register.PC (hsp_init _) = pc := by
    rw [key Register.PC (hs _) (hsp_init _) (by decide)]; exact hpc_get
  have hsp_npc : sp.regs.get Register.nextPC (hsp_init _) = pc + 4#64 := by
    show (s.regs.insert Register.nextPC (pc + 4#64)).get Register.nextPC _ = _
    rw [Std.ExtDHashMap.get_insert]; simp
  have htgt4 : Word.toBitVec64 next_pc_word % 4#64 = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
  have hjump : EStateM.run (jump_to (pc + sign_extend (m := 64) imm)) sp
      = .ok RETIRE_SUCCESS { sp with regs := sp.regs.insert Register.nextPC (Word.toBitVec64 next_pc_word) } := by
    rw [← h_jump]; exact jump_to_of_mod4_eq_zero _ sp hsp_init htgt4
  simp [spec_jal, sp1_jal, execute_JAL, hsp.symm,
    Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get,
    Sail.run_readReg_bind_of_isInitialized _ _ hsp_init,
    hsp_pc, hjump, RETIRE_SUCCESS, h_jump]
  simp [hsp]
  intro x' hx'
  simp [Std.ExtDHashMap.get?_insert, beq_iff_eq, hx']

/-- `Word.toBitVec64 #v[4,0,0,0] = 4#64`. -/
theorem toBitVec64_four : Word.toBitVec64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) = 4#64 := by
  have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [Word.toBitVec64_toNat (by
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num),
    Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast, ZMod.val_natCast_of_lt h4lt, ZMod.val_zero]
  decide

/-- End-to-end: from the JAL chip's verified `Spec` (on a real row) plus the PC read, the committed-pc ↔
Sail-PC reassembly, and the immediate decode, the RISC-V `JAL` execution agrees with the SP1 chip
emulation. The jump-target 4-byte alignment is **derived** from the `Spec`'s divisibility conjunct (the
in-circuit `÷4` range check), not assumed. Covers **both** `rd ≠ x0` (`op_a_0 = 0`, link write proven) and
`jal x0` (`op_a_0 = 1 ∧ rd = x0`, link write a no-op on both sides) — closing the `j` pseudo-instruction. -/
theorem jal_chip_reaches_sail
    (inp : JalChip.Inputs (ZMod p)) (cols : Extracted.JalColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (imm : BitVec 21) (pc : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s)
    (h_real : inp.is_real = 1)
    (h_chip : JalChip.Spec inp cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_pcw : Word.toBitVec64 (JalChip.pcWord cols) = pc)
    (h_dec : Word.toBitVec64 cols.adapter.op_b_imm = sign_extend (m := 64) imm)
    (h_op_a : cols.adapter.op_a_0 = 0 ∨ (cols.adapter.op_a_0 = 1 ∧ rd = 0#5)) :
    (spec_jal imm (.Regidx rd)).run s
      = (sp1_jal (.Regidx rd) pc cols.add_operation.value cols.op_a_operation.value).run s := by
  have h_jump : Word.toBitVec64 cols.add_operation.value = pc + sign_extend (m := 64) imm := by
    rw [h_chip.2.2.1 h_real, h_pcw, h_dec]
  -- 4-byte alignment is now a verified `Spec` conjunct (the in-circuit `÷4` range check), not an assumed
  -- precondition: lift the jump-target low-limb divisibility to the committed word.
  have h_align : (Word.toBitVec64 cols.add_operation.value).toNat % 4 = 0 := by
    rw [Word.toBitVec64_toNat_mod_four]
    exact h_chip.2.2.2.2 h_real
  rcases h_op_a with h_op_a_0 | ⟨_, hrd0⟩
  · have h_link : Word.toBitVec64 cols.op_a_operation.value = pc + 4#64 := by
      rw [h_chip.2.2.2.1 h_real h_op_a_0, h_pcw, toBitVec64_four]
    exact correct_jal_native cols.adapter.op_b_imm cols.add_operation.value cols.op_a_operation.value
      rd imm pc s hs h_pc h_jump h_link h_align
  · subst hrd0
    exact correct_jal_native_x0 cols.adapter.op_b_imm cols.add_operation.value cols.op_a_operation.value
      imm pc s hs h_pc h_jump h_align

end SP1Clean.JalSail

namespace SP1Clean.JalChip

open SP1Clean.JalSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **JAL's committed bus view** — the chip-agnostic `RowView` (opcode `46`, `next_pc = add_operation.value`
the **data-dependent** jump target, `rdWrite = op_a_operation.value` the link `pc+4`). Standalone so
`JalChip.advance` can be supplied *as* `kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : Extracted.JalColumns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.add_operation.value[0], cols.add_operation.value[1], cols.add_operation.value[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.op_a_operation.value, 46, .regWrite⟩

/-- **`JalChip.advance`** — the per-JAL-row `try_step` lift (SC Phase 4, the **first computed-`next_pc` chip**):
over `advance_of_jal` (the jump ladder core, `advance_jump_core`), whose `execute_JAL` sets `nextPC := target`
and writes the link `pc+4` to `rd`. The per-chip obligations are discharged from the chip `Spec`: the target
relation `hsnd` (`sndPcOf = pc + signExtend imm`, from the Spec's `add_operation.value = pc + op_b_imm` jump
conjunct + the decode's immediate + the `pcWord` reassembly), the link `hlink` (`rdWrite = pc+4`, from the
`op_a_operation` conjunct + `toBitVec64_four`), and the 4-alignment `halign` (from the `Spec`'s `÷4`
range-check conjunct via `Word.toBitVec64_toNat_mod_four`). The `advanceReady` bundle carries the pc-limb
bound, `op_a_0 = 0`, `op_a ≠ 0`, and the **48-bit-target invariant** `add_operation.value[3] = 0` (SP1 pcs are
3-limb, so the committed 3-limb `next_pc` equals the Sail 64-bit target). Stated to match the field. -/
theorem advance (inp : Inputs (ZMod p)) (cols : Extracted.JalColumns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (_hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : cols.state.pc[0].val < 2 ^ 16 ∧ cols.adapter.op_a_0 = 0 ∧
      (rowView inp cols).adapter.op_a ≠ 0 ∧ cols.add_operation.value[3] = 0) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hpc0, hopa0, hnonX0, hv3⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  have reassemble : ∀ (v : Word (ZMod p)), v[3] = 0 →
      pcBitsOfVals v[0].val v[1].val v[2].val = Word.toBitVec64 v := by
    intro v hv; simp only [Word.toBitVec64, pcBitsOfVals]; congr 1
    rw [Word.toNat_def, hv]; simp only [ZMod.val_zero]; ring
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = cols.op_a_operation.value := rfl
  have vopb : cols.adapter.op_b_imm = r.adapter.op_b := rfl
  have himmc : r.adapter.imm_c = 1 := rfl
  have hop : r.opcode = ((Opcode.JAL).toNat : ZMod p) := by simp [hr, rowView, Opcode.toNat]
  have hpcw : Word.toBitVec64 (JalChip.pcWord cols) = rcvPcOf (stateAccess r) := by
    have hp3 : (JalChip.pcWord cols)[3] = 0 := rfl
    rw [← reassemble _ hp3]; rfl
  have hsnd_eq : sndPcOf (stateAccess r) = Word.toBitVec64 cols.add_operation.value :=
    (reassemble cols.add_operation.value hv3).symm ▸ rfl
  refine advance_of_jal hcfg hrom hpcread hdecrom hop himmc hnonX0 ?_ ?_ ?_
  · rw [hsnd_eq, Word.toBitVec64_toNat_mod_four]; exact hspec.2.2.2.2 hreal'
  · intro imm hopb
    have hbind : cols.adapter.op_b_imm = bitVecToWord (imm.signExtend 64) := vopb.trans hopb
    rw [hsnd_eq, hspec.2.2.1 hreal', hpcw]
    congr 1; rw [hbind]; exact toBitVec64_bitVecToWord _
  · rw [vrd, hspec.2.2.2.1 hreal' hopa0, hpcw, toBitVec64_four]

/-- JAL's `ChipKind` registration. `view` threads `next_pc = add_operation.value` (the data-dependent
jump target), J-type adapter, opcode 46. `sailEquiv` quantifies the PC/decode preconditions internally
(JAL reads no source registers); the jump-target alignment is no longer a precondition — `reaches_sail`
derives it from the chip `Spec`. `reaches_sail` is `jal_chip_reaches_sail`; `advance`/`advanceReady` (SC
Phase 4) route to `JalChip.advance`. -/
def kind : Soundness.ChipKind p where
  name := "Jal"
  Inputs := JalChip.Inputs
  Cols := Extracted.JalColumns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rd : BitVec 5) (imm : BitVec 21) (pc : BitVec 64),
    SailState.isInitialized s →
    s.regs.get? Register.PC = some pc →
    Word.toBitVec64 (JalChip.pcWord cols) = pc →
    Word.toBitVec64 cols.adapter.op_b_imm = sign_extend (m := 64) imm →
    (cols.adapter.op_a_0 = 0 ∨ (cols.adapter.op_a_0 = 1 ∧ rd = 0#5)) →
    (spec_jal imm (.Regidx rd)).run s
      = (sp1_jal (.Regidx rd) pc cols.add_operation.value cols.op_a_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rd imm pc hs h_pc h_pcw h_dec h_op_a =>
    jal_chip_reaches_sail inp cols data rd imm pc s hs h_real h_chip h_pc h_pcw h_dec h_op_a
  advanceReady := fun inp cols _ _ => cols.state.pc[0].val < 2 ^ 16 ∧ cols.adapter.op_a_0 = 0 ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧ cols.add_operation.value[3] = 0
  advance := some (PLift.up advance)

end SP1Clean.JalChip
