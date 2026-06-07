import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.SailMemory
import SP1Clean.Foundations.Word
import SP1Clean.Chips.JalrChip.Formal
import SP1Clean.Chips.JalChip.Bridge
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for JALR (+ `ChipKind` registration) — register-indirect control flow

`correct_jalr_native` proves the RISC-V Sail execution of `JALR` (`spec_jalr`, calling LeanRV64D's
`execute_JALR`) agrees with the SP1 chip's emulation (`sp1_jalr`: set `nextPC` to the committed,
LSB-cleared jump target and write the link address `pc + 4` to `rd`), given the chip's **semantic** facts
(the jump/link identities = `JalrChip.circuit`'s `Spec`) plus the register/PC + decode + LSB-clearing
received facts.

`jalr_chip_reaches_sail` composes the verified `JalrChip.Spec` into the bridge; `JalrChip.kind` enters
JALR rows into the heterogeneous trace (the generalized `Soundness.ChipKind`, whose `sailEquiv` quantifies
the row's PC read, the rs1 register read, the immediate decode, the LSB-clearing relation, and the cleared
target's alignment internally).

**Control-flow novelty.** `JalrChip.kind.view` threads a **data-dependent, LSB-cleared**
`next_pc = #v[add_operation.value[0] - lsb, …]` (RISC-V's `(rs1 + imm) & ~1`), the jump base being a
**source register** (rs1) rather than the program counter.

`correct_jalr_native` proves the deep `execute_JALR` monad equivalence outright, given the Sail state is
initialized with a valid mem config: `update_elp_state` is a no-op (`update_elp_state_of_isInitialized`),
the `rX_bits` rs1 read survives the staged `nextPC` write, and `jump_to (BitVec.update target 0 0#1)`
retires under 4-byte alignment (`jump_to_of_mod4_eq_zero`), then `get_next_pc`/`set_next_pc`/`wX_bits`
reduce to match `sp1_jalr`. The whole chain — chip, `Spec` composition, `kind` — is axiom-clean. -/

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
/-- Native Sail equivalence for JALR. From the rs1 register read (`rs1_val`), the committed LSB-cleared
jump target (`= (rs1_val + sign_extend imm) & ~1`), the committed link address (`= pc + 4`), the 4-byte
alignment of the cleared target, the PC read, and the state being initialized + a valid mem config, the
RISC-V `JALR` execution agrees with the SP1 chip emulation.

The proof: `update_elp_state` (Zicfilp landing-pad bookkeeping) is state-preserving
(`update_elp_state_of_isInitialized`); `execute_JALR` reads rs1 (`rs1_val`), forms `target = rs1_val +
sign_extend imm`, and `jump_to (BitVec.update target 0 0#1)` retires successfully because the cleared target
is 4-byte aligned (`jump_to_of_mod4_eq_zero`); it then reads the staged `nextPC = pc + 4` as the link,
overwrites `nextPC ← BitVec.update target 0 0#1` via `set_next_pc`, and writes the link to `rd` — matching
`sp1_jalr` field-for-field (the staged write collapses via `ExtDHashMap_insert_insert_self`). -/
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
  -- the Zicfilp prefix is a no-op; the rs1 read survives the staged `nextPC` write.
  have hupd : EStateM.run (update_elp_state (.Regidx rs1)) sp = .ok () sp :=
    update_elp_state_of_isInitialized _ sp hsp_init hsp_config
  have hsp_rs1 : SailState.get_reg? sp rs1 = some rs1_val := by
    rw [hsp, SailState.get_reg?_insert_nextPC]; exact h_rs1
  -- the cleared jump target is `next_pc_word`, 4-aligned ⇒ `jump_to` retires.
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
read, the committed rs1 ↔ Sail reassembly, the immediate decode, `op_a_0 = 0` (rd ≠ x0), the committed-pc
reassembly, the LSB-clearing relation, and the cleared-target alignment, the RISC-V `JALR` execution agrees
with the SP1 chip emulation. -/
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
    (h_pcw : Word.toBitVec64 (JalrChip.pcWord cols) = pc)
    (h_lsbclear : Word.toBitVec64 (JalrChip.nextPcWord cols)
        = BitVec.update (Word.toBitVec64 cols.add_operation.value) 0 0#1)
    (h_align : (Word.toBitVec64 (JalrChip.nextPcWord cols)).toNat % 4 = 0) :
    (spec_jalr imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_jalr (.Regidx rd) (JalrChip.nextPcWord cols) cols.op_a_operation.value).run s := by
  have h_jump : Word.toBitVec64 cols.add_operation.value = rs1_val + sign_extend (m := 64) imm := by
    rw [h_chip.2.2.2.1 h_real, h_rs1v, h_dec]
  have h_link : Word.toBitVec64 cols.op_a_operation.value = pc + 4#64 := by
    rw [h_chip.2.2.2.2 h_real h_op_a_0, h_pcw, JalSail.toBitVec64_four]
  have h_lsbclear' : Word.toBitVec64 (JalrChip.nextPcWord cols)
      = BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1 := by rw [h_lsbclear, h_jump]
  exact correct_jalr_native cols.adapter.op_c_imm (JalrChip.nextPcWord cols) cols.op_a_operation.value
    rd rs1 imm pc rs1_val s hs hconfig h_pc h_rs1 h_lsbclear' h_link h_align

end SP1Clean.JalrSail

namespace SP1Clean.JalrChip

open SP1Clean.JalrSail
open SP1Clean.SailMem
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **JALR's `ChipKind` registration** — enters JALR rows into the heterogeneous trace and the soundness
capstone. `view` threads the **data-dependent, LSB-cleared** `next_pc = #v[add_operation.value[0] - lsb, …]`
and the I-type adapter (`ITypeReader.toAdapterView`, `imm_b = 0` rs1 register read, `imm_c = 1` immediate),
opcode 47. `sailEquiv` quantifies the row's PC read, the rs1 read, the committed-rs1/decode/`op_a_0`/pc/
LSB-clearing/alignment preconditions internally, and `reaches_sail` is `jalr_chip_reaches_sail`. -/
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
    Word.toBitVec64 (JalrChip.nextPcWord cols)
      = BitVec.update (Word.toBitVec64 cols.add_operation.value) 0 0#1 →
    (Word.toBitVec64 (JalrChip.nextPcWord cols)).toNat % 4 = 0 →
    (spec_jalr imm (.Regidx rs1) (.Regidx rd)).run s
      = (sp1_jalr (.Regidx rd) (JalrChip.nextPcWord cols) cols.op_a_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rd rs1 imm pc rs1_val hs hconfig h_pc h_rs1 h_rs1v h_dec
      h_op_a_0 h_pcw h_lsbclear h_align =>
    jalr_chip_reaches_sail inp cols data rd rs1 imm pc rs1_val s hs hconfig h_real h_chip h_pc h_rs1 h_rs1v h_dec
      h_op_a_0 h_pcw h_lsbclear h_align

end SP1Clean.JalrChip
