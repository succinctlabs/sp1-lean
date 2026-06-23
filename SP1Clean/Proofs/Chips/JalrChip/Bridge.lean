import SP1Clean.Model.SailWrap
import SP1Clean.Model.SailMemory
import SP1Clean.Math.Word
import SP1Clean.Proofs.Chips.JalrChip.Formal
import SP1Clean.Proofs.Chips.JalChip.Bridge
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for JALR (+ `ChipKind` registration)

`correct_jalr_native` proves `execute_JALR` agrees with `sp1_jalr` given the chip's jump/link facts and
LSB-clearing. Key non-obvious moves: `update_elp_state` is a no-op (`update_elp_state_of_isInitialized`);
`jump_to (BitVec.update target 0 0#1)` retires via `jump_to_of_mod4_eq_zero` (LSB-clearing guarantees
4-byte alignment). `JalrChip.kind.view` threads `next_pc = add_operation.value[0] - lsb` (LSB-cleared). -/

namespace SP1Clean.JalrSail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: stage `nextPC ← PC + 4`, then execute the Sail `JALR` (which reads that link address,
reads rs1, jumps `PC ← (rs1 + sign_extend imm) & ~1`, and writes the link to `rd`). -/
noncomputable def spec_jalr (imm : BitVec 12) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_JALR imm rs1 rd
  pure ()

/-- The SP1 chip emulation: set `nextPC` to the committed LSB-cleared jump target word, and write the
committed link word (`pc + 4`) to `rd` (x0-uniform via `wX_bits`). -/
def sp1_jalr (rd : regidx) (next_pc_word op_a_word : Word (ZMod p)) : SailM Unit := do
  set_next_pc (Word.toBitVec64 next_pc_word)
  wX_bits rd (Word.toBitVec64 op_a_word)

omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence for JALR: given the committed LSB-cleared jump target, link address, 4-byte
alignment, PC read, and initialized state with valid mem config, `execute_JALR ≡ sp1_jalr`. -/
theorem correct_jalr_native
    (_op_c_imm next_pc_word op_a_word : Word (ZMod p))
    (rd rs1 : BitVec 5) (imm : BitVec 12) (pc rs1_val : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : SailState.get_reg? s rs1 = some rs1_val)
    (h_lsbclear : Word.toBitVec64 next_pc_word
        = BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1)
    (h_link : Word.toBitVec64 op_a_word = pc + 4#64)
    (h_align : (Word.toBitVec64 next_pc_word).toNat % 4 = 0) :
    (spec_jalr imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_jalr (.Regidx rd) next_pc_word op_a_word).run s := by
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
  have hsp_config : SailState.isValidMemConfig sp hsp_init :=
    { h_cur_privilege := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hconfig.h_cur_privilege
      h_mprv_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hconfig.h_mprv_disabled
      h_mseccfg_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hconfig.h_mseccfg_disabled
      h_htif_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hconfig.h_htif_disabled
      h_pma_regions := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hconfig.h_pma_regions }
  have hupd : EStateM.run (update_elp_state (.Regidx rs1)) sp = .ok () sp :=
    update_elp_state_of_isInitialized _ sp hsp_init hsp_config
  have hsp_rs1 : SailState.get_reg? sp rs1 = some rs1_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  have htgt4 : BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1 % 4#64 = 0 := by
    rw [← h_lsbclear]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
  have hjump : EStateM.run (jump_to (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1)) sp
      = .ok RETIRE_SUCCESS { sp with regs := sp.regs.insert Register.nextPC (Word.toBitVec64 next_pc_word) } := by
    rw [jump_to_of_mod4_eq_zero _ sp hsp_init htgt4, ← h_lsbclear]
  simp [spec_jalr, sp1_jalr, execute_JALR, hsp.symm,
    Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get, hupd, hsp_rs1,
    Sail.run_readReg_bind_of_isInitialized _ _ hsp_init, hjump,
    RETIRE_SUCCESS, h_link]
  simp [hsp]

/-- End-to-end: from the JALR chip's verified `Spec` (on a real row) plus the PC read, the rs1 register
read, the committed rs1 ↔ Sail reassembly, the immediate decode, `op_a_0 = 0` (rd ≠ x0), and the
committed-pc reassembly, the RISC-V `JALR` execution agrees with the SP1 chip emulation. Both the
LSB-clearing relation and the cleared-target 4-byte alignment are **derived** from the chip `Spec` (the
in-circuit binary `lsb` gate + `÷4` range check), not assumed. -/
theorem jalr_chip_reaches_sail
    (inp : JalrChip.Inputs (ZMod p)) (cols : Extracted.JalrColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd rs1 : BitVec 5) (imm : BitVec 12) (pc rs1_val : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_real : inp.is_real = 1)
    (h_chip : JalrChip.Spec inp cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : SailState.get_reg? s rs1 = some rs1_val)
    (h_rs1v : Word.toBitVec64 (JalrChip.rs1Word cols) = rs1_val)
    (h_dec : Word.toBitVec64 cols.adapter.op_c_imm = sign_extend (m := 64) imm)
    (h_op_a_0 : cols.adapter.op_a_0 = 0)
    (h_pcw : Word.toBitVec64 (JalrChip.pcWord cols) = pc) :
    (spec_jalr imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_jalr (.Regidx rd) (JalrChip.nextPcWord cols) cols.op_a_operation.value).run s := by
  have h_jump : Word.toBitVec64 cols.add_operation.value = rs1_val + sign_extend (m := 64) imm := by
    rw [h_chip.2.2.2.1 h_real, h_rs1v, h_dec]
  have h_link : Word.toBitVec64 cols.op_a_operation.value = pc + 4#64 := by
    rw [h_chip.2.2.2.2.1 h_real h_op_a_0, h_pcw, JalSail.toBitVec64_four]
  -- The LSB-clearing relation is now a verified `Spec` conjunct (the in-circuit binary `lsb` gate + the
  -- `÷4` byte-range), not an assumed precondition; unfold the Sail `BitVec.update` to its `~~~1#64 &&&` form.
  have h_lsbclear' : Word.toBitVec64 (JalrChip.nextPcWord cols)
      = BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1 := by
    rw [h_chip.2.2.2.2.2.2 h_real, h_jump]
    simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
  -- 4-byte alignment is now a verified `Spec` conjunct (the in-circuit `÷4` range check), not an
  -- assumed precondition: lift the cleared low-limb divisibility to the committed `next_pc` word.
  have h_align : (Word.toBitVec64 (JalrChip.nextPcWord cols)).toNat % 4 = 0 := by
    rw [Word.toBitVec64_toNat_mod_four]
    exact h_chip.2.2.2.2.2.1 h_real
  exact correct_jalr_native cols.adapter.op_c_imm (JalrChip.nextPcWord cols) cols.op_a_operation.value
    rd rs1 imm pc rs1_val s hs hconfig h_pc h_rs1 h_lsbclear' h_link h_align

end SP1Clean.JalrSail

namespace SP1Clean.JalrChip

open SP1Clean.JalrSail
open SP1Clean.SailMem
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- JALR's `ChipKind` registration. `view` threads the LSB-cleared `next_pc`, I-type adapter, opcode 47.
`sailEquiv` quantifies the PC/rs1 read and decode preconditions internally; neither the LSB-clearing
relation nor the cleared-target 4-byte alignment is a precondition — `reaches_sail` derives both from the
chip `Spec`. `reaches_sail` is `jalr_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Jalr"
  Inputs := JalrChip.Inputs
  Cols := Extracted.JalrColumns
  view := fun inp cols => ⟨cols.state,
    #v[cols.add_operation.value[0] - cols.lsb, cols.add_operation.value[1], cols.add_operation.value[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.op_a_operation.value, 47⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rd rs1 : BitVec 5) (imm : BitVec 12) (pc rs1_val : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    s.regs.get? Register.PC = some pc →
    SailState.get_reg? s rs1 = some rs1_val →
    Word.toBitVec64 (JalrChip.rs1Word cols) = rs1_val →
    Word.toBitVec64 cols.adapter.op_c_imm = sign_extend (m := 64) imm →
    cols.adapter.op_a_0 = 0 →
    Word.toBitVec64 (JalrChip.pcWord cols) = pc →
    (spec_jalr imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_jalr (.Regidx rd) (JalrChip.nextPcWord cols) cols.op_a_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rd rs1 imm pc rs1_val hs hconfig h_pc h_rs1 h_rs1v h_dec
      h_op_a_0 h_pcw =>
    jalr_chip_reaches_sail inp cols data rd rs1 imm pc rs1_val s hs hconfig h_real h_chip h_pc h_rs1 h_rs1v h_dec
      h_op_a_0 h_pcw

end SP1Clean.JalrChip
