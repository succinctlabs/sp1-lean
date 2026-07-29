import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.BranchChip.Formal
import SP1Clean.Proofs.Chips.JalChip.Bridge
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for BRANCH (+ `ChipKind` registration)

`correct_branch_native` proves `execute_BTYPE ≡ sp1_branch` given PC/rs1/rs2 reads and the chip-side
condition resolving `next_pc`. The taken arm's `jump_to` retires via `jump_to_of_mod4_eq_zero`; both arms
land `nextPC ← next_pc_word`. `branch_chip_reaches_sail` is the six-way BEQ/BNE/BLT/BGE/BLTU/BGEU
conjunction. The whole chain is axiom-clean. -/

open LeanRV64D.Defs
namespace SP1Clean.BranchSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: stage `nextPC ← PC + 4` (the fall-through), then execute the Sail `BTYPE` (which
reads rs1/rs2, evaluates the condition, and on a taken branch overwrites `nextPC ← PC + sign_extend imm`). -/
noncomputable def spec_btype (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_BTYPE imm rs2 rs1 op
  pure ()

/-- The SP1 chip emulation: set `nextPC` to the committed `next_pc` word. Branches write no register. -/
def sp1_branch (next_pc_word : Word (ZMod p)) : SailM Unit := do
  set_next_pc (Word.toBitVec64 next_pc_word)

/-- The chip-side branch condition per opcode (matching `BranchChip.Spec`'s six decision conjuncts): the
RISC-V taken predicate expressed on the two `BitVec 64` register values via `BitVec.slt`/`ult`. -/
def branchCond (op : bop) (x y : BitVec 64) : Prop :=
  match op with
  | .BEQ => x = y
  | .BNE => x ≠ y
  | .BLT => x.slt y = true
  | .BGE => x.slt y = false
  | .BLTU => x.ult y = true
  | .BGEU => x.ult y = false

/-! ### Sail comparison functions ↔ `BitVec.slt`/`ult` -/

private lemma zopz0zI_s_eq_slt (x y : BitVec 64) : zopz0zI_s x y = x.slt y := by
  simp [zopz0zI_s, BitVec.slt]

private lemma zopz0zI_u_eq_ult (x y : BitVec 64) : zopz0zI_u x y = x.ult y := by
  simp [zopz0zI_u, BitVec.ult, Sail.BitVec.toNatInt]

private lemma zopz0zKzJ_s_true_iff (x y : BitVec 64) :
    zopz0zKzJ_s x y = true ↔ x.slt y = false := by simp [zopz0zKzJ_s, BitVec.slt]

private lemma zopz0zKzJ_u_true_iff (x y : BitVec 64) :
    zopz0zKzJ_u x y = true ↔ x.ult y = false := by
  simp [zopz0zKzJ_u, BitVec.ult, Sail.BitVec.toNatInt]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for a B-type branch. Both arms land `nextPC ← next_pc_word`: taken via
`jump_to_of_mod4_eq_zero` + the per-`bop` comparison identities, not-taken via the staged write. -/
theorem correct_branch_native
    (next_pc_word : Word (ZMod p))
    (rs1 rs2 : BitVec 5) (imm : BitVec 13) (pc rs1_val rs2_val : BitVec 64)
    (op : bop) (s : SailState) (hs : SailState.isInitialized s)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : SailState.get_reg? s rs1 = some rs1_val)
    (h_rs2 : SailState.get_reg? s rs2 = some rs2_val)
    (h_taken : branchCond op rs1_val rs2_val →
        Word.toBitVec64 next_pc_word = pc + sign_extend (m := 64) imm)
    (h_not_taken : ¬ branchCond op rs1_val rs2_val →
        Word.toBitVec64 next_pc_word = pc + 4#64)
    (h_align : (Word.toBitVec64 next_pc_word).toNat % 4 = 0) :
    (spec_btype imm (.Regidx rs2) (.Regidx rs1) op).run s
      = (sp1_branch next_pc_word).run s := by
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc
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
  have hsp_rs1 : SailState.get_reg? sp rs1 = some rs1_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hsp_rs2 : SailState.get_reg? sp rs2 = some rs2_val := by
    rwa [hsp, SailState.get_reg?_insert_nextPC]
  have hexec : EStateM.run (execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) op) sp
      = .ok RETIRE_SUCCESS { s with regs := s.regs.insert Register.nextPC (Word.toBitVec64 next_pc_word) } := by
    rcases em (branchCond op rs1_val rs2_val) with hc | hc
    · have hnpc := h_taken hc
      have htgt4 : (pc + sign_extend (m := 64) imm) % 4#64 = 0 := by
        rw [← hnpc]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
      have hjump := jump_to_of_mod4_eq_zero (pc + sign_extend (m := 64) imm) sp hsp_init htgt4
      cases op <;> simp only [branchCond, not_not, ne_eq] at hc ⊢ <;>
        (simp [execute_BTYPE, run_rX_bits, hsp_rs1, hsp_rs2,
          Sail.run_readReg_bind_of_isInitialized _ _ hsp_init, hsp_pc, hjump, RETIRE_SUCCESS,
          zopz0zI_s_eq_slt, zopz0zI_u_eq_ult, zopz0zKzJ_s_true_iff, zopz0zKzJ_u_true_iff,
          hsp.symm, hc]
         simp [hsp, hnpc]
         try (intro x hx; simp [Std.ExtDHashMap.get?_insert, hx]))
    · have hnpc := h_not_taken hc
      cases op <;> simp only [branchCond, not_not, ne_eq] at hc ⊢ <;>
        (simp [execute_BTYPE, run_rX_bits, hsp_rs1, hsp_rs2, RETIRE_SUCCESS,
          zopz0zI_s_eq_slt, zopz0zI_u_eq_ult, zopz0zKzJ_s_true_iff, zopz0zKzJ_u_true_iff,
          hsp.symm, hc]
         simp [hsp, hnpc])
  simp [spec_btype, sp1_branch, Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get, hsp.symm,
    hexec]

/-- End-to-end: from the BRANCH chip's verified `Spec` (on a real row) plus the PC/rs1/rs2 reads, the
committed rs1/rs2 ↔ Sail reassembly, the immediate decode, and the committed-pc reassembly, the RISC-V
`BTYPE` execution agrees with the SP1 chip emulation — flag-dispatched over the six opcodes. The
branch-target 4-byte alignment is **derived** from the `Spec`'s divisibility conjunct (the in-circuit
`÷4` range check), not assumed. -/
theorem branch_chip_reaches_sail
    (inp : BranchChip.Inputs (ZMod p)) (cols : BranchChip.Columns (ZMod p))
    (data : ProverData (ZMod p))
    (rs1 rs2 : BitVec 5) (imm : BitVec 13) (pc rs1_val rs2_val : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s)
    (h_real : inp.is_real = 1)
    (h_chip : BranchChip.Spec inp cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : SailState.get_reg? s rs1 = some rs1_val)
    (h_rs2 : SailState.get_reg? s rs2 = some rs2_val)
    (h_rs1v : Word.toBitVec64 (BranchChip.rs1Word cols) = rs1_val)
    (h_rs2v : Word.toBitVec64 (BranchChip.rs2Word cols) = rs2_val)
    (h_dec : Word.toBitVec64 cols.adapter.op_c_imm = sign_extend (m := 64) imm)
    (h_pcw : Word.toBitVec64 (BranchChip.pcWord cols) = pc) :
    (cols.is_beq = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BEQ).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) ∧
    (cols.is_bne = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BNE).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) ∧
    (cols.is_blt = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BLT).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) ∧
    (cols.is_bge = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BGE).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) ∧
    (cols.is_bltu = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BLTU).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) ∧
    (cols.is_bgeu = 1 →
        (spec_btype imm (.Regidx rs2) (.Regidx rs1) bop.BGEU).run s
          = (sp1_branch (BranchChip.nextPcWord cols)).run s) := by
  obtain ⟨_, _, h_flags, _, h_taken_gated, h_fall_gated, h_decision, h_div⟩ := h_chip
  -- 4-byte alignment is now a verified `Spec` conjunct (the in-circuit `÷4` range check), not an assumed
  -- precondition: lift the low-limb divisibility to the committed `next_pc` word.
  have h_align : (Word.toBitVec64 (BranchChip.nextPcWord cols)).toNat % 4 = 0 := by
    rw [Word.toBitVec64_toNat_mod_four]
    simpa only [BranchChip.nextPcWord, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using h_div h_real
  have h_brbin : cols.is_branching = 0 ∨ cols.is_branching = 1 := h_flags.2.2.2.2.2.2
  have key : ∀ op : bop, (cols.is_branching = 1 ↔ branchCond op rs1_val rs2_val) →
      (spec_btype imm (.Regidx rs2) (.Regidx rs1) op).run s
        = (sp1_branch (BranchChip.nextPcWord cols)).run s := by
    intro op hbr
    refine correct_branch_native (BranchChip.nextPcWord cols) rs1 rs2 imm pc rs1_val rs2_val op s
      hs h_pc h_rs1 h_rs2 ?_ ?_ h_align
    · intro hcond
      rw [h_taken_gated h_real (hbr.mpr hcond), h_pcw, h_dec]
    · intro hcond
      have hb0 : cols.is_branching = 0 := by
        rcases h_brbin with h | h
        · exact h
        · exact absurd (hbr.mp h) hcond
      rw [h_fall_gated h_real hb0, h_pcw, JalSail.toBitVec64_four]
  obtain ⟨d_beq, d_bne, d_blt, d_bge, d_bltu, d_bgeu⟩ := h_decision h_real
  exact ⟨fun hf => key bop.BEQ (by have := d_beq hf; rwa [h_rs1v, h_rs2v] at this),
    fun hf => key bop.BNE (by have := d_bne hf; rwa [h_rs1v, h_rs2v] at this),
    fun hf => key bop.BLT (by have := d_blt hf; rwa [h_rs1v, h_rs2v] at this),
    fun hf => key bop.BGE (by have := d_bge hf; rwa [h_rs1v, h_rs2v] at this),
    fun hf => key bop.BLTU (by have := d_bltu hf; rwa [h_rs1v, h_rs2v] at this),
    fun hf => key bop.BGEU (by have := d_bgeu hf; rwa [h_rs1v, h_rs2v] at this)⟩

end SP1Clean.BranchSail

namespace SP1Clean.BranchChip

open SP1Clean.BranchSail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **BRANCH's committed bus view** — the chip-agnostic `RowView` (opcode `Σ is_b*·k`, `next_pc =
cols.next_pc` the **data-dependent** branch target, `rdWrite = 0` and `commit = .noWrite` — branches write
no register). Standalone (identical to the former inline `kind.view`) so `BranchChip.advance` can be
supplied *as* `kind.advance`. -/
def rowView (inp : Inputs (ZMod p)) (cols : BranchChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]],
    cols.adapter.toAdapterView, inp.is_real, #v[0, 0, 0, 0], branchOpcode cols, .noWrite⟩

/-- **`BranchChip.advance`** — the per-BRANCH-row `try_step` lift (SC Phase 4, the **first
non-register-writing chip**): over `advance_of_ctrl` (the control-flow ladder core), whose `execute_BTYPE`
commits `nextPC := target` and writes no register (`commit = .noWrite`, `RowEffect.regs` is a pure frame).
6-way flag dispatch (BEQ/BNE/BLT/BGE/BLTU/BGEU); each branch feeds `execute_BTYPE_reaches` with `btypeTaken`
tied to the chip `Spec`'s six-way `is_branching` decision (via the `zopz0z*↔slt/ult` lemmas + `rs1Word`/
`rs2Word` = the `op_a`/`op_b` register read-backs), the taken/fall next-pc conjuncts, and the `÷4` alignment.
`advanceReady` carries the **`op_a` SOURCE read binding** — branches read `rs1` in the `op_a` slot, which
`ValueOperandsBound` (op_b/op_c only) does not supply — plus the 6-way one-hot flag partition. -/
theorem advance (inp : Inputs (ZMod p)) (cols : BranchChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1) (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : ∀ idx : BitVec 5, (idx.toNat : ZMod p) = cols.adapter.op_a →
      s.get_reg? idx = some (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  have hopa_bind := hready
  obtain ⟨_, _, h_flags, h_oneHot, h_taken_gated, h_fall_gated, h_decision, h_div⟩ := hspec
  have hflag := h_oneHot hreal
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have himmc : r.adapter.imm_c = 1 := rfl
  have himmb : r.adapter.imm_b = 0 := rfl
  have hr1w : BranchChip.rs1Word cols = cols.adapter.op_a_memory.prev_value := by
    apply Vector.ext; intro i hi; simp only [BranchChip.rs1Word]; interval_cases i <;> rfl
  have hr2w : BranchChip.rs2Word cols = cols.adapter.op_b_memory.prev_value := by
    apply Vector.ext; intro i hi; simp only [BranchChip.rs2Word]; interval_cases i <;> rfl
  have reassemble : ∀ (v : Word (ZMod p)), v[3] = 0 →
      pcBitsOfVals v[0].val v[1].val v[2].val = Word.toBitVec64 v := by
    intro v hv; simp only [Word.toBitVec64, pcBitsOfVals]; congr 1
    rw [Word.toNat_def, hv]; simp only [ZMod.val_zero]; ring
  have hpcw : Word.toBitVec64 (BranchChip.pcWord cols) = rcvPcOf (stateAccess r) := by
    have hp3 : (BranchChip.pcWord cols)[3] = 0 := rfl
    rw [← reassemble _ hp3]; rfl
  have hsnd_eq : sndPcOf (stateAccess r) = Word.toBitVec64 (BranchChip.nextPcWord cols) :=
    (reassemble (BranchChip.nextPcWord cols) rfl).symm ▸ rfl
  have key : ∀ (op : bop),
      r.opcode = ((bopToOpcode op).toNat : ZMod p) →
      (cols.is_branching = 1 ↔ btypeTaken op (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)
                                              (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) = true) →
      ∃ s', SailStep s s' ∧ RowEffect prog r s s' := by
    intro op hop hdec_iff
    obtain ⟨w, imm, rs2, rs1, hfetch, hdecw, hopa, hopb, hopc⟩ := decodesBType op hdecrom hop himmc
    have hfetch' : prog.fetchWord (rcvPcOf (stateAccess r)) = some w := hfetch
    have hfetchReady := fetchReady_of_romLoaded prog s (rcvPcOf (stateAccess r)) w hrom hfetch' hpcread
    have hidxb : (rs2.toNat : ZMod p) = r.adapter.op_b[0] := by
      have h : r.adapter.op_b = #v[(rs2.toNat : ZMod p), 0, 0, 0] := hopb; rw [h]; rfl
    have hrs2 := hvalb.1 rs2 himmb hidxb
    have hidxa : (rs1.toNat : ZMod p) = cols.adapter.op_a := hopa.symm
    have hrs1 := hopa_bind rs1 hidxa
    have himm_dec : Word.toBitVec64 cols.adapter.op_c_imm = sign_extend (m := 64) imm := by
      have h : cols.adapter.op_c_imm = bitVecToWord (imm.signExtend 64) := hopc
      rw [h]; exact toBitVec64_bitVecToWord _
    have halign : (Word.toBitVec64 (BranchChip.nextPcWord cols)).toNat % 4 = 0 := by
      rw [Word.toBitVec64_toNat_mod_four]
      simpa only [BranchChip.nextPcWord, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero] using h_div hreal'
    refine advance_of_ctrl (instruction.BTYPE (imm, .Regidx rs2, .Regidx rs1, op))
      (Word.toBitVec64 (BranchChip.nextPcWord cols)) (rcvPcOf (stateAccess r))
      (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
      hcfg hpcread hfetchReady
      (fun sc hsc => by rw [word_reassemble w]; exact hdecw sc hsc)
      (fun t hframe hpcf hnpc_t hinit hcfgt => ?_)
      hsnd_eq rfl
    apply execute_BTYPE_reaches imm rs1 rs2 op (rcvPcOf (stateAccess r))
      (Word.toBitVec64 (BranchChip.nextPcWord cols))
      (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)
      (Word.toBitVec64 cols.adapter.op_b_memory.prev_value) t hinit
      (hpcf.trans hpcread) hnpc_t ((hframe rs1).trans hrs1) ((hframe rs2).trans hrs2) ?_ ?_ halign
    · intro hbt
      rw [h_taken_gated hreal' (hdec_iff.mpr hbt), hpcw, himm_dec]
    · intro hbf
      have hbranch0 : cols.is_branching = 0 := by
        have hne1 : cols.is_branching ≠ 1 := fun h1 => by
          have hh := hdec_iff.mp h1; rw [hh] at hbf; exact absurd hbf (by decide)
        rcases h_flags.2.2.2.2.2.2 with h0 | h1
        · exact h0
        · exact absurd h1 hne1
      rw [h_fall_gated hreal' hbranch0, hpcw, JalSail.toBitVec64_four]
  rcases hflag with ⟨hb, h0a, h0b, h0c, h0d, h0e⟩ | ⟨hb, h0a, h0b, h0c, h0d, h0e⟩ |
    ⟨hb, h0a, h0b, h0c, h0d, h0e⟩ | ⟨hb, h0a, h0b, h0c, h0d, h0e⟩ |
    ⟨hb, h0a, h0b, h0c, h0d, h0e⟩ | ⟨hb, h0a, h0b, h0c, h0d, h0e⟩
  · exact key bop.BEQ (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken]; rw [beq_iff_eq, ← hr1w, ← hr2w]; exact (h_decision hreal').1 hb)
  · exact key bop.BNE (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken]; rw [bne_iff_ne, ← hr1w, ← hr2w]; exact (h_decision hreal').2.1 hb)
  · exact key bop.BLT (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken, zopz0zI_s_eq_slt]; rw [← hr1w, ← hr2w]; exact (h_decision hreal').2.2.1 hb)
  · exact key bop.BGE (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken]; rw [zopz0zKzJ_s_true_iff, ← hr1w, ← hr2w]; exact (h_decision hreal').2.2.2.1 hb)
  · exact key bop.BLTU (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken, zopz0zI_u_eq_ult]; rw [← hr1w, ← hr2w]; exact (h_decision hreal').2.2.2.2.1 hb)
  · exact key bop.BGEU (by simp [hr, rowView, branchOpcode, hb, h0a, h0b, h0c, h0d, h0e, bopToOpcode, Opcode.toNat])
      (by simp only [btypeTaken]; rw [zopz0zKzJ_u_true_iff, ← hr1w, ← hr2w]; exact (h_decision hreal').2.2.2.2.2 hb)

/-- BRANCH's `ChipKind` registration. `view := rowView` threads `next_pc = cols.next_pc`, I-type adapter,
opcode `Σ is_b*·k`; `commit = .noWrite` (no destination write). `advance` is the six-way flag-dispatched
`try_step` lift over the no-register-write `advance_of_ctrl` core. -/
def kind : Soundness.ChipKind p where
  name := "Branch"
  Inputs := BranchChip.Inputs
  Cols := BranchChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun _inp cols _ s =>
    ∀ idx : BitVec 5, (idx.toNat : ZMod p) = cols.adapter.op_a →
      s.get_reg? idx = some (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)
  advance := some (PLift.up advance)

end SP1Clean.BranchChip
