import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.JalChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for JAL (+ `ChipKind` registration) — control-flow proof of concept

`correct_jal_native` proves the RISC-V Sail execution of `JAL` (`spec_jal`, calling LeanRV64D's
`execute_JAL`) agrees with the SP1 chip's emulation (`sp1_jal`: set `nextPC` to the committed jump target
and write the link address `pc + 4` to `rd`), given the chip's **semantic** facts (the jump/link
identities = `JalChip.circuit`'s `Spec`) and the register/PC + decode received facts.

`jal_chip_reaches_sail` composes the verified `JalChip.Spec` into the bridge; `JalChip.kind` enters JAL
rows into the heterogeneous trace (the generalized `Soundness.ChipKind`, whose `sailEquiv` quantifies
the row's PC read + immediate-decode preconditions internally — JAL reads no source registers).

**Control-flow novelty.** `JalChip.kind.view` threads a **data-dependent** `next_pc = add_operation.value`
(the jump target), the first chip whose `RowView.next_pc` is computed data rather than `pc + 4`.

`correct_jal_native` proves the deep `execute_JAL` monad equivalence outright (the `jump_to` retire-success
under 4-byte alignment via `jump_to_of_mod4_eq_zero`, plus the `get_next_pc`/`set_next_pc`/`wX_bits`
reduction), given the Sail state is initialized. The whole chain — chip, `Spec` composition, `kind` — is
axiom-clean. -/

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
/-- Native Sail equivalence for JAL. From the committed jump target (`= PC + sign_extend imm`), the
committed link address (`= PC + 4`), the 4-byte alignment of the jump target, the PC read, and the
state being initialized, the RISC-V `JAL` execution agrees with the SP1 chip emulation.

The proof: `jump_to (pc + sign_extend imm)` retires successfully because the target is 4-byte aligned
(`jump_to_of_mod4_eq_zero`: low two bits `0`, so neither the `bit 0` assert nor the `bit 1`/`Zca`
misalignment branch fires), then `execute_JAL` reads the staged `nextPC = pc + 4` as the link, overwrites
`nextPC ← pc + sign_extend imm` via `set_next_pc`, and writes the link to `rd` — matching `sp1_jal`
field-for-field (the staged write collapses via `ExtDHashMap_insert_insert_self`). -/
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
  -- the jump target reduces: `pc + sign_extend imm = next_pc_word`, 4-aligned ⇒ `jump_to` retires.
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

/-- **JAL's `ChipKind` registration** — enters JAL rows into the heterogeneous trace and the soundness
capstone. `view` threads the **data-dependent** `next_pc = add_operation.value` (the jump target) and the
J-type adapter (`JTypeReader.toAdapterView`, `imm_b = imm_c = 1`), opcode 46. `sailEquiv` quantifies the
row's PC read + the committed-pc/decode/`op_a_0`/alignment preconditions internally (JAL reads no source
registers), and `reaches_sail` is `jal_chip_reaches_sail`. -/
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
