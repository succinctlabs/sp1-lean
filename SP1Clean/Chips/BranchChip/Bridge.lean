import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.BranchChip.Formal
import SP1Clean.Chips.JalChip.Bridge
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for BRANCH (+ `ChipKind` registration) — conditional control flow

`correct_branch_native` proves the RISC-V Sail execution of a B-type branch (`spec_btype`, calling
LeanRV64D's `execute_BTYPE`) agrees with the SP1 chip's emulation (`sp1_branch`: set `nextPC` to the
committed `next_pc` word; branches write no register), given the register/PC reads and the chip-side
condition that resolves the committed `next_pc` (`pc + sign_extend imm` when the branch is taken, else
`pc + 4`).

`branch_chip_reaches_sail` composes the verified `BranchChip.Spec` into the bridge, flag-dispatched over
the six opcodes (BEQ/BNE/BLT/BGE/BLTU/BGEU); `BranchChip.kind` enters BRANCH rows into the heterogeneous
trace + soundness capstone, its `sailEquiv` quantifying the row's PC/rs1/rs2 reads, the committed-word
reassembly, the immediate decode, and the committed-pc reassembly internally.

**Control-flow novelty.** Unlike the unconditional jumps the committed `next_pc` is chosen by a *comparison*
of the two source registers; the chip's `Spec` exposes the choice (the `is_branching`-gated target) and the
per-opcode decision (`is_branching ↔ condition`), and the bridge dispatches the matching Sail `bop`.

`correct_branch_native` proves the deep `execute_BTYPE` monad equivalence outright, given the Sail state is
initialized and the committed `next_pc` is 4-byte aligned: the per-`bop` comparison (`==`/`!=`/`zopz0z*`)
computing `taken` is related to `branchCond op` by the Sail-comparison ↔ `BitVec.slt`/`ult` identities, the
taken arm's `jump_to (PC + sign_extend imm)` retires via `jump_to_of_mod4_eq_zero`, and both arms land
`nextPC ← next_pc_word`. The whole chain — chip, `Spec` composition, `kind` — is axiom-clean (modulo the
chip's own skeletal `LtOperationSigned`). -/

namespace SP1Clean.BranchSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: stage `nextPC ← PC + 4` (the fall-through), then execute the Sail `BTYPE` (which
reads rs1/rs2, evaluates the condition, and on a taken branch overwrites `nextPC ← PC + sign_extend imm`). -/
noncomputable def spec_btype (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
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

/-! ### Sail comparison functions ↔ `BitVec.slt`/`ult` (relating the `execute_BTYPE` `taken` to `branchCond`) -/

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
/-- Native Sail equivalence for a B-type branch. From the PC and the two source-register reads, the
committed-`next_pc` resolution (`= pc + sign_extend imm` when the branch condition holds, else `= pc + 4`),
the 4-byte alignment of the committed `next_pc`, and the state being initialized, the RISC-V `BTYPE`
execution agrees with the SP1 chip emulation.

The proof: `execute_BTYPE` reads rs1/rs2 and computes `taken` via the per-`bop` comparison
(`==`/`!=`/`zopz0z*`, related to `branchCond op` by the identities above). On `taken` it does
`jump_to (PC + sign_extend imm)`, retire-success under 4-byte alignment (`jump_to_of_mod4_eq_zero`), the
committed `next_pc` being `pc + sign_extend imm`; on `¬taken` it retires with the staged `nextPC = pc + 4`,
the committed `next_pc` being `pc + 4`. Both arms land `nextPC ← next_pc_word`, matching `sp1_branch`. -/
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
  have hsp_rs1 : SailState.get_reg? sp rs1 = some rs1_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  have hsp_rs2 : SailState.get_reg? sp rs2 = some rs2_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs2
  -- `execute_BTYPE` lands `nextPC ← next_pc_word` (jump target on taken, staged `pc+4` on fall-through).
  have hexec : EStateM.run (execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) op) sp
      = .ok RETIRE_SUCCESS { s with regs := s.regs.insert Register.nextPC (Word.toBitVec64 next_pc_word) } := by
    rcases em (branchCond op rs1_val rs2_val) with hc | hc
    · -- taken: `next_pc = pc + sign_extend imm`, 4-aligned ⇒ `jump_to` retires.
      have hnpc := h_taken hc
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
    · -- not taken: `next_pc = pc + 4`, the staged write already holds.
      have hnpc := h_not_taken hc
      cases op <;> simp only [branchCond, not_not, ne_eq] at hc ⊢ <;>
        (simp [execute_BTYPE, run_rX_bits, hsp_rs1, hsp_rs2, RETIRE_SUCCESS,
          zopz0zI_s_eq_slt, zopz0zI_u_eq_ult, zopz0zKzJ_s_true_iff, zopz0zKzJ_u_true_iff,
          hsp.symm, hc]
         simp [hsp, hnpc])
  simp [spec_btype, sp1_branch, Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get, hsp.symm,
    hexec]

/-- End-to-end: from the BRANCH chip's verified `Spec` (on a real row) plus the PC/rs1/rs2 reads, the
committed rs1/rs2 ↔ Sail reassembly, the immediate decode, and the committed-pc reassembly, the RISC-V
`BTYPE` execution agrees with the SP1 chip emulation — flag-dispatched over the six opcodes. -/
theorem branch_chip_reaches_sail
    (inp : BranchChip.Inputs (ZMod p)) (cols : Extracted.BranchColumns (ZMod p))
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
    (h_pcw : Word.toBitVec64 (BranchChip.pcWord cols) = pc)
    (h_align : (Word.toBitVec64 (BranchChip.nextPcWord cols)).toNat % 4 = 0) :
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
  obtain ⟨_, _, h_flags, h_taken_gated, h_fall_gated, h_decision⟩ := h_chip
  have h_brbin : cols.is_branching = 0 ∨ cols.is_branching = 1 := h_flags.2.2.2.2.2.2
  -- the common derivation: from `is_branching = 1 ↔ branchCond op`, reach the Sail equivalence.
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
  refine ⟨fun hf => key bop.BEQ ?_, fun hf => key bop.BNE ?_, fun hf => key bop.BLT ?_,
    fun hf => key bop.BGE ?_, fun hf => key bop.BLTU ?_, fun hf => key bop.BGEU ?_⟩
  · have := d_beq hf; rw [h_rs1v, h_rs2v] at this; exact this
  · have := d_bne hf; rw [h_rs1v, h_rs2v] at this; exact this
  · have := d_blt hf; rw [h_rs1v, h_rs2v] at this; exact this
  · have := d_bge hf; rw [h_rs1v, h_rs2v] at this; exact this
  · have := d_bltu hf; rw [h_rs1v, h_rs2v] at this; exact this
  · have := d_bgeu hf; rw [h_rs1v, h_rs2v] at this; exact this

end SP1Clean.BranchSail

namespace SP1Clean.BranchChip

open SP1Clean.BranchSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **BRANCH's `ChipKind` registration** — enters BRANCH rows into the heterogeneous trace and the
soundness capstone. `view` threads the **data-dependent** committed `next_pc` (`cols.next_pc`, the chosen
target) and the immutable I-type adapter (`ITypeReader.toAdapterView`), opcode `Σ is_b*·k`; there is no
destination write. `sailEquiv` quantifies the PC/rs1/rs2 reads, the committed-word reassembly, the
immediate decode, and the committed-pc reassembly internally, flag-dispatched over the six opcodes;
`reaches_sail` is `branch_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Branch"
  Inputs := BranchChip.Inputs
  Cols := Extracted.BranchColumns
  view := fun inp cols => ⟨cols.state,
    #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]],
    cols.adapter.toAdapterView, inp.is_real, #v[0, 0, 0, 0], branchOpcode cols⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s =>
    ∀ (rs1 rs2 : BitVec 5) (imm : BitVec 13) (pc rs1_val rs2_val : BitVec 64),
      SailState.isInitialized s →
      s.regs.get? Register.PC = some pc →
      SailState.get_reg? s rs1 = some rs1_val →
      SailState.get_reg? s rs2 = some rs2_val →
      Word.toBitVec64 (BranchChip.rs1Word cols) = rs1_val →
      Word.toBitVec64 (BranchChip.rs2Word cols) = rs2_val →
      Word.toBitVec64 cols.adapter.op_c_imm = sign_extend (m := 64) imm →
      Word.toBitVec64 (BranchChip.pcWord cols) = pc →
      (Word.toBitVec64 (BranchChip.nextPcWord cols)).toNat % 4 = 0 →
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
            = (sp1_branch (BranchChip.nextPcWord cols)).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 imm pc rs1_val rs2_val
      hs h_pc h_rs1 h_rs2 h_rs1v h_rs2v h_dec h_pcw h_align =>
    branch_chip_reaches_sail inp cols data rs1 rs2 imm pc rs1_val rs2_val s hs h_real h_chip
      h_pc h_rs1 h_rs2 h_rs1v h_rs2v h_dec h_pcw h_align

end SP1Clean.BranchChip
