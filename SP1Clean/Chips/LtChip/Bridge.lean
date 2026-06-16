import SP1Clean.Model.SailWrap
import SP1Clean.Math.Word
import SP1Clean.Chips.LtChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for the unified `Lt` chip (SLT + SLTU) + `ChipKind`

`sp1_lt` is opcode-agnostic; the RISC-V Sail specs differ by variant (`spec_slt`/`spec_sltu`).
`correct_sltu_native` and `correct_slt_native` (both proven and axiom-clean) route the chip's
semantic RV64 `sltu`/`slt` facts into the respective Sail executions. `lt_chip_reaches_sail` proves
the flag-dispatched conjunction from the chip `Spec`. -/

namespace SP1Clean.LtSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLTU`. -/
noncomputable def spec_sltu (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLTU
  pure ()

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail `SLT` (signed). -/
noncomputable def spec_slt (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLT
  pure ()

/-- The SP1 chip emulation (opcode-agnostic for SLT/SLTU): write `nextPC = pc + 4` and the result
register `rd` (the set-less-than result word's 64-bit value). -/
def sp1_lt (rd : regidx) (pc : BitVec 64) (a_val : Word (ZMod p)) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 a_val)

set_option linter.unnecessarySeqFocus false in
/-- The Sail `SLTU` pure part is the clean RV64 `sltu` (operand order `rs2 rs1`): both place the
unsigned-less-than indicator (`rs1 <ᵤ rs2`) zero-extended to 64 bits. -/
theorem execute_RTYPE_pure_sltu (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SLTU = RV64.sltu y x := by
  apply BitVec.eq_of_toNat_eq
  simp only [execute_RTYPE_pure, RV64.sltu, zero_extend, Sail.BitVec.zeroExtend,
    bool_to_bit, bool_bit_forwards, zopz0zI_u, BitVec.toNatInt, BitVec.toNat_setWidth,
    BitVec.toNat_ofBool, BitVec.ult]
  by_cases h : x.toNat < y.toNat <;> simp_all [Nat.cast_lt] <;>
    cases h2 : x.toNat <b y.toNat <;> rfl

set_option linter.unnecessarySeqFocus false in
/-- The Sail `SLT` pure part is the clean RV64 `slt` (operand order `rs2 rs1`): both place the
signed-less-than indicator (`rs1 <ₛ rs2`) zero-extended to 64 bits. -/
theorem execute_RTYPE_pure_slt (x y : BitVec 64) :
    execute_RTYPE_pure x y rop.SLT = RV64.slt y x := by
  apply BitVec.eq_of_toNat_eq
  simp only [execute_RTYPE_pure, RV64.slt, zero_extend, Sail.BitVec.zeroExtend,
    bool_to_bit, bool_bit_forwards, zopz0zI_s, BitVec.slt]
  cases h2 : x.toInt <b y.toInt <;> simp_all

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (unsigned): the chip's semantic RV64 `sltu` fact (`h_sltu`) plus the
register/PC reads drive `spec_sltu ≡ sp1_lt`, with no SP1Chips borrow. -/
theorem correct_sltu_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_sltu : Word.toBitVec64 a_val
        = RV64.sltu (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_sltu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_sltu, sp1_lt, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    execute_RTYPE_pure_sltu, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_sltu]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (signed): `h_slt` plus register/PC reads drive `spec_slt ≡ sp1_lt`,
via the `execute_RTYPE_pure_slt` Sail-side identity. -/
theorem correct_slt_native
    (op_b_val op_c_val a_val : Word (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_slt : Word.toBitVec64 a_val
        = RV64.slt (Word.toBitVec64 op_c_val) (Word.toBitVec64 op_b_val)) :
    (spec_slt (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
      = (sp1_lt (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_slt, sp1_lt, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    execute_RTYPE_pure_slt, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC,
    h_pc, h_rs1, h_rs2, h_slt]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end: a real `Lt` chip row reaches the RISC-V Sail set-less-than, flag-dispatched.
Both SLT and SLTU conjuncts are proven and axiom-clean. -/
theorem lt_chip_reaches_sail
    (input : LtChip.Inputs (ZMod p)) (cols : Extracted.LtCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1)
    (h_chip : LtChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (cols.is_slt = 1 →
        (spec_slt (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) ∧
    (cols.is_sltu = 1 →
        (spec_sltu (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)).run s
          = (sp1_lt (.Regidx rd_idx) pc (LtChip.resultWord cols)).run s) := by
  obtain ⟨-, -, h_gated⟩ := h_chip
  refine ⟨fun hslt => ?_, fun hsltu => ?_⟩
  · exact correct_slt_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_gated h_real).1 hslt)
  · exact correct_sltu_native input.op_b_val input.op_c_val (LtChip.resultWord cols)
      rs1_idx rs2_idx rd_idx pc s h_pc h_rs1 h_rs2 ((h_gated h_real).2 hsltu)

end SP1Clean.LtSail

namespace SP1Clean.LtChip

open SP1Clean.LtSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Lt's `ChipKind` registration.** Program-bus opcode `is_slt·9 + is_sltu·10`; `sailEquiv` is the
flag-dispatched SLT/SLTU conjunction; `reaches_sail` is `lt_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "Lt"
  Inputs := LtChip.Inputs
  Cols := Extracted.LtCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real, resultWord cols,
    cols.is_slt * 9 + cols.is_sltu * 10⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_slt = 1 →
        (spec_slt (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_lt (.Regidx rd) pc (resultWord cols)).run s) ∧
    (cols.is_sltu = 1 →
        (spec_sltu (.Regidx rs2) (.Regidx rs1) (.Regidx rd)).run s
          = (sp1_lt (.Regidx rd) pc (resultWord cols)).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    lt_chip_reaches_sail inp cols data rs1 rs2 rd pc s h_real h_chip h_pc h_rs1 h_rs2

end SP1Clean.LtChip
