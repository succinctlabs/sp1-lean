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

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail I-type op (ANDI/ORI/XORI). -/
noncomputable def spec_bitwise_imm (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd op
  pure ()

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (ANDI): the chip's bitwise fact (`h_op`, with the immediate operand `op_c_val`
bound to `sign_extend imm` via `h_dec`) drives `spec_bitwise_imm … ANDI ≡ sp1_bitwise`. The Sail `ANDI` arm
`rX rs1 &&& immext` is the same body as `execute_RTYPE_pure … .AND`. -/
theorem correct_andi_native
    (op_b_val op_c_val : Word (ZMod p)) (a_val : Vector (ZMod p) 8)
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_op : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
        = execute_RTYPE_pure (Word.toBitVec64 op_b_val) (Word.toBitVec64 op_c_val) rop.AND) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.ANDI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
      = (Word.toBitVec64 op_b_val) &&& (sign_extend (m := 64) imm) := by
    rw [h_op, ← h_dec]; simp [execute_RTYPE_pure]
  simp [spec_bitwise_imm, sp1_bitwise, execute_ITYPE, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, h_pc, h_rs1, harm]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (ORI): `h_op` + reads drive `spec_bitwise_imm … ORI ≡ sp1_bitwise`. -/
theorem correct_ori_native
    (op_b_val op_c_val : Word (ZMod p)) (a_val : Vector (ZMod p) 8)
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_op : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
        = execute_RTYPE_pure (Word.toBitVec64 op_b_val) (Word.toBitVec64 op_c_val) rop.OR) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.ORI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
      = (Word.toBitVec64 op_b_val) ||| (sign_extend (m := 64) imm) := by
    rw [h_op, ← h_dec]; simp [execute_RTYPE_pure]
  simp [spec_bitwise_imm, sp1_bitwise, execute_ITYPE, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, h_pc, h_rs1, harm]

set_option linter.unusedSimpArgs false in
omit [Fact (2 ^ 17 < p)] in
/-- Native Sail equivalence (XORI): `h_op` + reads drive `spec_bitwise_imm … XORI ≡ sp1_bitwise`. -/
theorem correct_xori_native
    (op_b_val op_c_val : Word (ZMod p)) (a_val : Vector (ZMod p) 8)
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 op_b_val))
    (h_dec : Word.toBitVec64 op_c_val = sign_extend (m := 64) imm)
    (h_op : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
        = execute_RTYPE_pure (Word.toBitVec64 op_b_val) (Word.toBitVec64 op_c_val) rop.XOR) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.XORI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc a_val).run s := by
  have harm : Word.toBitVec64 (BitwiseU16Operation.resultWord a_val)
      = (Word.toBitVec64 op_b_val) ^^^ (sign_extend (m := 64) imm) := by
    rw [h_op, ← h_dec]; simp [execute_RTYPE_pure]
  simp [spec_bitwise_imm, sp1_bitwise, execute_ITYPE, PreSail.readReg, PreSail.writeReg,
    Sail.run_rX_bits, Sail.run_wX_bits, SailState.get_reg?_insert_nextPC, h_pc, h_rs1, harm]

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
  exact (h_chip.2.1 h_real).1 h_and

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
  exact (h_chip.2.1 h_real).2.1 h_or

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
  exact (h_chip.2.1 h_real).2.2 h_xor

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (ANDI): a real Bitwise chip row with `is_and = 1` whose `op_c` is the sign-extended
immediate (`h_dec`) reaches the Sail `ANDI`. -/
theorem bitwise_chip_reaches_sail_andi
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_and : cols.is_and = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.ANDI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_andi_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result
    rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec ?_
  exact (h_chip.2.1 h_real).1 h_and

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (ORI): a real Bitwise chip row with `is_or = 1` and immediate `op_c` reaches the Sail `ORI`. -/
theorem bitwise_chip_reaches_sail_ori
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_or : cols.is_or = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.ORI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_ori_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result
    rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec ?_
  exact (h_chip.2.1 h_real).2.1 h_or

omit [Fact (2 ^ 17 < p)] in
/-- End-to-end (XORI): a real Bitwise chip row with `is_xor = 1` and immediate `op_c` reaches the Sail `XORI`. -/
theorem bitwise_chip_reaches_sail_xori
    (input : BitwiseChip.Inputs (ZMod p)) (cols : Extracted.BitwiseCols (ZMod p)) (data : ProverData (ZMod p))
    (rs1_idx rd_idx : BitVec 5) (imm : BitVec 12) (pc : BitVec 64) (s : SailState)
    (h_real : input.is_real = 1) (h_xor : cols.is_xor = 1)
    (h_chip : BitwiseChip.Spec input cols data)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some (Word.toBitVec64 input.op_b_val))
    (h_dec : Word.toBitVec64 input.op_c_val = sign_extend (m := 64) imm) :
    (spec_bitwise_imm imm (.Regidx rs1_idx) (.Regidx rd_idx) iop.XORI).run s
      = (sp1_bitwise (.Regidx rd_idx) pc cols.bitwise_operation.bitwise_operation.result).run s := by
  refine correct_xori_native input.op_b_val input.op_c_val cols.bitwise_operation.bitwise_operation.result
    rs1_idx rd_idx imm pc s h_pc h_rs1 h_dec ?_
  exact (h_chip.2.1 h_real).2.2 h_xor

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
  sailEquiv := fun inp cols s =>
    (∀ (rs1 rs2 rd : BitVec 5) (pc : BitVec 64),
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
            = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s)) ∧
    (∀ (rs1 rd : BitVec 5) (imm : BitVec 12) (pc : BitVec 64),
      s.regs.get? Register.PC = some pc →
      s.get_reg? rs1 = some (Word.toBitVec64 inp.op_b_val) →
      Word.toBitVec64 inp.op_c_val = sign_extend (m := 64) imm →
      (cols.is_and = 1 →
          (spec_bitwise_imm imm (.Regidx rs1) (.Regidx rd) iop.ANDI).run s
            = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s) ∧
      (cols.is_or = 1 →
          (spec_bitwise_imm imm (.Regidx rs1) (.Regidx rd) iop.ORI).run s
            = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s) ∧
      (cols.is_xor = 1 →
          (spec_bitwise_imm imm (.Regidx rs1) (.Regidx rd) iop.XORI).run s
            = (sp1_bitwise (.Regidx rd) pc cols.bitwise_operation.bitwise_operation.result).run s))
  reaches_sail := fun inp cols data s h_real h_chip =>
    ⟨fun rs1 rs2 rd pc h_pc h_rs1 h_rs2 =>
      ⟨fun ha => bitwise_chip_reaches_sail_and inp cols data rs1 rs2 rd pc s h_real ha h_chip h_pc h_rs1 h_rs2,
       fun ho => bitwise_chip_reaches_sail_or  inp cols data rs1 rs2 rd pc s h_real ho h_chip h_pc h_rs1 h_rs2,
       fun hx => bitwise_chip_reaches_sail_xor inp cols data rs1 rs2 rd pc s h_real hx h_chip h_pc h_rs1 h_rs2⟩,
     fun rs1 rd imm pc h_pc h_rs1 h_dec =>
      ⟨fun ha => bitwise_chip_reaches_sail_andi inp cols data rs1 rd imm pc s h_real ha h_chip h_pc h_rs1 h_dec,
       fun ho => bitwise_chip_reaches_sail_ori  inp cols data rs1 rd imm pc s h_real ho h_chip h_pc h_rs1 h_dec,
       fun hx => bitwise_chip_reaches_sail_xori inp cols data rs1 rd imm pc s h_real hx h_chip h_pc h_rs1 h_dec⟩⟩

end SP1Clean.BitwiseChip
