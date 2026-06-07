import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.UTypeChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for U-type (`LUI` / `AUIPC`) (+ `ChipKind` registration)

`correct_utype_{lui,auipc}_native` prove the RISC-V Sail execution of a U-type op (`spec_utype`, calling
LeanRV64D's `execute_UTYPE`) agrees with the SP1 chip emulation (`sp1_utype`: write `nextPC = pc + 4` and the
result register `rd`), given the chip's **semantic** fact — the committed result word's 64-bit value is
`RV64.lui imm` (LUI) or `RV64.auipc imm pc` (AUIPC), i.e. exactly the Sail `off` / `pc + off` (the Sail
`sign_extend (imm ++ 0#12)` is definitionally `RV64.lui imm`). Unlike JAL/JALR there is **no**
`jump_to`/alignment, so both are fully `sorry`-free.

`utype_chip_reaches_sail_{lui,auipc}` compose the verified `UTypeChip.Spec`'s flag-gated `RV64.lui`/`RV64.auipc`
conjuncts straight into the bridge; `UTypeChip.kind` enters U-type rows into the heterogeneous trace
(`Soundness/ChipRow.lean`). The 20-bit immediate `imm` is the column-derived `UTypeChip.immOf`, so `sailEquiv`
needs only the PC read, the committed-pc reassembly, and `op_a_0 = 0` (`rd ≠ x0`). -/

namespace SP1Clean.UTypeSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `UTYPE` (which writes `RV64.lui imm`
for LUI, `PC + RV64.lui imm` for AUIPC, to `rd`). -/
noncomputable def spec_utype (imm : BitVec 20) (rd : regidx) (op : uop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_UTYPE imm rd op
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd` (the committed result word's
64-bit value, x0-uniform via `wX_bits`). -/
def sp1_utype (rd : regidx) (pc : BitVec 64) (result : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
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
    PreSail.readReg, PreSail.writeReg, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, h_pc, h_result]

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
    PreSail.readReg, PreSail.writeReg, Sail.run_wX_bits, Std.ExtDHashMap.get?_insert,
    SailState.get_reg?_insert_nextPC, h_pc, h_result]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (LUI): a real U-type chip row with `is_auipc = 0` and `rd ≠ x0` reaches the Sail `LUI`. -/
theorem utype_chip_reaches_sail_lui
    (input : UTypeChip.Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_iaui0 : input.is_auipc = 0) (h_op0 : cols.adapter.op_a_0 = 0)
    (h_chip : UTypeChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc) :
    (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.LUI).run s
      = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s :=
  correct_utype_lui_native cols.add_operation.value rd (UTypeChip.immOf cols.adapter) pc s h_pc
    (h_chip.2.2.2.1 h_real h_op0 h_iaui0)

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (AUIPC): a real U-type chip row with `is_auipc = 1` and `rd ≠ x0` reaches the Sail `AUIPC`. -/
theorem utype_chip_reaches_sail_auipc
    (input : UTypeChip.Inputs (ZMod p)) (cols : Extracted.UTypeColumns (ZMod p)) (data : ProverData (ZMod p))
    (rd : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_iaui1 : input.is_auipc = 1) (h_op0 : cols.adapter.op_a_0 = 0)
    (h_chip : UTypeChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_pcw : Word.toBitVec64 (UTypeChip.pcWord cols) = pc) :
    (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.AUIPC).run s
      = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s := by
  have hr := h_chip.2.2.2.2 h_real h_op0 h_iaui1
  rw [h_pcw] at hr
  exact correct_utype_auipc_native cols.add_operation.value rd (UTypeChip.immOf cols.adapter) pc s h_pc hr

end SP1Clean.UTypeSail

namespace SP1Clean.UTypeChip

open SP1Clean.UTypeSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **U-type's `ChipKind` registration** — enters LUI/AUIPC rows into the heterogeneous trace and the
soundness capstone. `view` threads the straight-line `next_pc = pc + 4`, the J-type adapter
(`JTypeReader.toAdapterView`, `imm_b = imm_c = 1`), and the flag-selected Program-bus opcode
`is_auipc·48 + (1-is_auipc)·49`. U-type is multi-variant, so `sailEquiv` is the `is_auipc`-dispatched
LUI/AUIPC conjunction (the 20-bit immediate is the column-derived `immOf`) and `reaches_sail` dispatches to
`utype_chip_reaches_sail_{lui,auipc}`. Every bridge lemma is sorry-free, so this `kind` is axiom-clean. -/
def kind : Soundness.ChipKind p where
  name := "UType"
  Inputs := UTypeChip.Inputs
  Cols := Extracted.UTypeColumns
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, cols.add_operation.value,
    inp.is_auipc * 48 + (1 - inp.is_auipc) * 49⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    Word.toBitVec64 (UTypeChip.pcWord cols) = pc →
    cols.adapter.op_a_0 = 0 →
    (inp.is_auipc = 0 →
        (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.LUI).run s
          = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s) ∧
    (inp.is_auipc = 1 →
        (spec_utype (UTypeChip.immOf cols.adapter) (.Regidx rd) uop.AUIPC).run s
          = (sp1_utype (.Regidx rd) pc cols.add_operation.value).run s)
  reaches_sail := fun inp cols data s h_real h_chip rd pc h_pc h_pcw h_op0 =>
    ⟨fun h0 => utype_chip_reaches_sail_lui inp cols data rd pc s h_real h0 h_op0 h_chip h_pc,
     fun h1 => utype_chip_reaches_sail_auipc inp cols data rd pc s h_real h1 h_op0 h_chip h_pc h_pcw⟩

end SP1Clean.UTypeChip
