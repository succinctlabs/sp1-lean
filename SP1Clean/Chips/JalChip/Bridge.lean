import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.JalChip.Formal
import SP1Clean.Soundness.ChipRow

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
Sail-PC reassembly, the immediate decode, `op_a_0 = 0` (rd ≠ x0), and the jump-target alignment, the
RISC-V `JAL` execution agrees with the SP1 chip emulation. -/
theorem jal_chip_reaches_sail
    (inp : JalChip.Inputs (ZMod p)) (cols : Extracted.JalColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (imm : BitVec 21) (pc : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s)
    (h_real : inp.is_real = 1)
    (h_chip : JalChip.Spec inp cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_pcw : Word.toBitVec64 (JalChip.pcWord cols) = pc)
    (h_dec : Word.toBitVec64 cols.adapter.op_b_imm = sign_extend (m := 64) imm)
    (h_op_a_0 : cols.adapter.op_a_0 = 0)
    (h_align : (Word.toBitVec64 cols.add_operation.value).toNat % 4 = 0) :
    (spec_jal imm (.Regidx rd)).run s
      = (sp1_jal (.Regidx rd) pc cols.add_operation.value cols.op_a_operation.value).run s := by
  have h_jump : Word.toBitVec64 cols.add_operation.value = pc + sign_extend (m := 64) imm := by
    rw [h_chip.2.2.1 h_real, h_pcw, h_dec]
  have h_link : Word.toBitVec64 cols.op_a_operation.value = pc + 4#64 := by
    rw [h_chip.2.2.2 h_real h_op_a_0, h_pcw, toBitVec64_four]
  exact correct_jal_native cols.adapter.op_b_imm cols.add_operation.value cols.op_a_operation.value
    rd imm pc s hs h_pc h_jump h_link h_align

end SP1Clean.JalSail

namespace SP1Clean.JalChip

open SP1Clean.JalSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- JAL's `ChipKind` registration. `view` threads `next_pc = add_operation.value` (the data-dependent
jump target), J-type adapter, opcode 46. `sailEquiv` quantifies the PC/decode/alignment preconditions
internally (JAL reads no source registers); `reaches_sail` is `jal_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Jal"
  Inputs := JalChip.Inputs
  Cols := Extracted.JalColumns
  view := fun inp cols => ⟨cols.state,
    #v[cols.add_operation.value[0], cols.add_operation.value[1], cols.add_operation.value[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.op_a_operation.value, 46⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rd : BitVec 5) (imm : BitVec 21) (pc : BitVec 64),
    SailState.isInitialized s →
    s.regs.get? Register.PC = some pc →
    Word.toBitVec64 (JalChip.pcWord cols) = pc →
    Word.toBitVec64 cols.adapter.op_b_imm = sign_extend (m := 64) imm →
    cols.adapter.op_a_0 = 0 →
    (Word.toBitVec64 cols.add_operation.value).toNat % 4 = 0 →
    (spec_jal imm (.Regidx rd)).run s
      = (sp1_jal (.Regidx rd) pc cols.add_operation.value cols.op_a_operation.value).run s
  reaches_sail := fun inp cols data s h_real h_chip rd imm pc hs h_pc h_pcw h_dec h_op_a_0 h_align =>
    jal_chip_reaches_sail inp cols data rd imm pc s hs h_real h_chip h_pc h_pcw h_dec h_op_a_0 h_align

end SP1Clean.JalChip
