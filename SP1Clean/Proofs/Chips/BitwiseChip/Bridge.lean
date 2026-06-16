import SP1Clean.Model.SailWrap
import SP1Clean.Native.Operations.BitwiseU16Operation
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for Bitwise (+ `ChipKind` registration)

`correct_bitwise_native` proves the RISC-V Sail R-type bitwise execution agrees with the SP1 chip
emulation given the semantic fact and register/PC reads. `SailWrap.execute_RTYPE_pure` already
maps `.AND/.OR/.XOR → &&&/|||/^^^`. Three `bitwise_chip_reaches_sail_*` end-to-end lemmas
compose `BitwiseChip.Spec`'s opcode-gated conjuncts into the bridge. -/

namespace SP1Clean.BitwiseSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail R-type op. -/
noncomputable def spec_bitwise (rs2 rs1 rd : regidx) (op : rop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd op
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd` (the
reassembled result word's 64-bit value). -/
def sp1_bitwise (rd : regidx) (pc : BitVec 64) (a_val : Vector (ZMod p) 8) : SailM Unit := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 (BitwiseU16Operation.resultWord a_val))

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence: the chip's semantic `Spec` (`h_op`) plus the register/PC
reads drive `spec_bitwise ≡ sp1_bitwise`, with no SP1Chips borrow. -/
theorem correct_bitwise_native
    (op_b_val op_c_val : Word (ZMod p)) (a_val : Vector (ZMod p) 8)
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState) (op : rop)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 op_c_val))
    (h_op : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
        = execute_RTYPE_pure (Word.toBitVec64 op_b_val) (Word.toBitVec64 op_c_val) op) :
    (spec_bitwise (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) op).run s
      = (sp1_bitwise (.Regidx rd_idx) pc a_val).run s := by
  simp [spec_bitwise, sp1_bitwise, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE',
    PreSail.readReg, PreSail.writeReg, Sail.run_rX_bits, Sail.run_wX_bits,
    SailState.get_reg?_insert_nextPC, h_pc, h_rs1, h_rs2, h_op]

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (AND): a real Bitwise chip row with `is_and = 1` reaches the Sail `AND`. -/
theorem bitwise_chip_reaches_sail_and
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_and : cols.is_and = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_bitwise (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) rop.AND).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_bitwise_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result rs1_idx rs2_idx rd_idx pc s
    rop.AND h_pc h_rs1 h_rs2 ?_
  exact (h_chip.2 h_real).1 h_and

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (OR): a real Bitwise chip row with `is_or = 1` reaches the Sail `OR`. -/
theorem bitwise_chip_reaches_sail_or
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_or : cols.is_or = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_bitwise (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) rop.OR).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_bitwise_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result rs1_idx rs2_idx rd_idx pc s
    rop.OR h_pc h_rs1 h_rs2 ?_
  exact (h_chip.2 h_real).2.1 h_or

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (XOR): a real Bitwise chip row with `is_xor = 1` reaches the Sail `XOR`. -/
theorem bitwise_chip_reaches_sail_xor
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rs2_idx rd_idx : BitVec 5) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_xor : cols.is_xor = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_rs2 : s.get_reg? rs2_idx = some (Word.toBitVec64 input.op_c_val)) :
    (spec_bitwise (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) rop.XOR).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_bitwise_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result rs1_idx rs2_idx rd_idx pc s
    rop.XOR h_pc h_rs1 h_rs2 ?_
  exact (h_chip.2 h_real).2.2 h_xor

end SP1Clean.BitwiseSail

namespace SP1Clean.BitwiseChip

open SP1Clean.BitwiseSail
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Bitwise's `ChipKind` registration.** Program-bus opcode `is_xor·3 + is_or·4 + is_and·5`;
`sailEquiv` is the selector-dispatched AND/OR/XOR conjunction; `reaches_sail` dispatches to
`bitwise_chip_reaches_sail_{and,or,xor}`. All bridge lemmas are axiom-clean. -/
def kind : Soundness.ChipKind p where
  name := "Bitwise"
  Inputs := BitwiseChip.Inputs
  Cols := Extracted.BitwiseCols
  view := fun inp cols => ⟨cols.state,
    #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real,
    BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result,
    cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5⟩
  chipSpec := fun inp cols data => Spec inp cols data
  sailEquiv := fun inp cols s => ∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
    s.regs.get? Register.PC = some pc →
    s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
    s.get_reg? rs2 = some (Word.toBitVec64 inp.op_c_val) →
    (cols.is_and = 1 →
        (spec_bitwise (.Regidx rs2) (.Regidx rs1) (.Regidx rd) rop.AND).run s
          = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s) ∧
    (cols.is_or = 1 →
        (spec_bitwise (.Regidx rs2) (.Regidx rs1) (.Regidx rd) rop.OR).run s
          = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s) ∧
    (cols.is_xor = 1 →
        (spec_bitwise (.Regidx rs2) (.Regidx rs1) (.Regidx rd) rop.XOR).run s
          = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s)
  reaches_sail := fun inp cols data s h_real h_chip rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
    ⟨fun ha => bitwise_chip_reaches_sail_and inp cols data rs1 rs2 rd pc s h_real ha h_chip h_pc h_rs1 h_rs2,
     fun ho => bitwise_chip_reaches_sail_or  inp cols data rs1 rs2 rd pc s h_real ho h_chip h_pc h_rs1 h_rs2,
     fun hx => bitwise_chip_reaches_sail_xor inp cols data rs1 rs2 rd pc s h_real hx h_chip h_pc h_rs1 h_rs2⟩

end SP1Clean.BitwiseChip
