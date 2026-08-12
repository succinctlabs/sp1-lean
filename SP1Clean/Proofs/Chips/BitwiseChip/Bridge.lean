import SP1Clean.Model.SailWrap
import SP1Clean.Native.Operations.BitwiseU16Operation
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import SP1Clean.Soundness.ChipRow
import SP1Clean.Proofs.Sail.Advance

/-! # Native Sail bridge for Bitwise (+ `ChipKind` registration)

`correct_bitwise_native` proves the RISC-V Sail R-type bitwise execution agrees with the SP1 chip
emulation given the semantic fact and register/PC reads. `SailWrap.execute_RTYPE_pure` already
maps `.AND/.OR/.XOR → &&&/|||/^^^`. Six `bitwise_chip_reaches_sail_*` end-to-end lemmas
(register + immediate forms) compose `BitwiseChip.Spec`'s opcode-gated conjuncts into the bridge. -/

open LeanRV64D.Defs
namespace SP1Clean.BitwiseSail

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail R-type op. -/
noncomputable def spec_bitwise (rs2 rs1 rd : regidx) (op : rop) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd op
  pure ()

/-- The SP1 chip emulation: write `nextPC = pc + 4` and the result register `rd` (the
reassembled result word's 64-bit value). -/
def sp1_bitwise (rd : regidx) (pc : BitVec 64) (a_val : Vector (ZMod p) 8) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC (pc + 4#64)
  wX_bits rd (Word.toBitVec64 (BitwiseU16Operation.resultWord a_val))

set_option linter.unusedSimpArgs false in
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
  simp only [spec_bitwise, sp1_bitwise]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [execute_RTYPE_eq_execute_RTYPE', execute_RTYPE', h_rs1, h_rs2, h_op]

/-- The RISC-V spec: advance `nextPC ← PC + 4`, then execute the Sail I-type op (ANDI/ORI/XORI). -/
noncomputable def spec_bitwise_imm (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : SailM Unit := do
  LeanRV64D.writeReg Register.nextPC ((← LeanRV64D.readReg Register.PC) + 4#64)
  _ ← execute_ITYPE imm rs1 rd op
  pure ()

set_option linter.unusedSimpArgs false in
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
  simp only [spec_bitwise_imm, sp1_bitwise]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', SP1Clean.Advance.execute_ITYPE_pure, h_rs1, harm]

set_option linter.unusedSimpArgs false in
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
  simp only [spec_bitwise_imm, sp1_bitwise]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', SP1Clean.Advance.execute_ITYPE_pure, h_rs1, harm]

set_option linter.unusedSimpArgs false in
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
  simp only [spec_bitwise_imm, sp1_bitwise]
  have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]
  rw [SP1Clean.TryStepReduction.run_bind_of_run s _ pc hpcrun,
    SP1Clean.TryStepReduction.run_bind_of_run' s _ _ () run_writeReg]
  simp [SP1Clean.Advance.execute_ITYPE', SP1Clean.Advance.execute_ITYPE_pure, h_rs1, harm]

/-- End-to-end (AND): a real Bitwise chip row with `is_and = 1` reaches the Sail `AND`. -/
theorem bitwise_chip_reaches_sail_and
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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

/-- End-to-end (OR): a real Bitwise chip row with `is_or = 1` reaches the Sail `OR`. -/
theorem bitwise_chip_reaches_sail_or
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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

/-- End-to-end (XOR): a real Bitwise chip row with `is_xor = 1` reaches the Sail `XOR`. -/
theorem bitwise_chip_reaches_sail_xor
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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

/-- End-to-end (ANDI): a real Bitwise chip row with `is_and = 1` whose `op_c` is the sign-extended
immediate (`h_dec`) reaches the Sail `ANDI`. -/
theorem bitwise_chip_reaches_sail_andi
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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

/-- End-to-end (ORI): a real Bitwise chip row with `is_or = 1` and immediate `op_c` reaches the Sail `ORI`. -/
theorem bitwise_chip_reaches_sail_ori
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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

/-- End-to-end (XORI): a real Bitwise chip row with `is_xor = 1` and immediate `op_c` reaches the Sail `XORI`. -/
theorem bitwise_chip_reaches_sail_xori
    (input : BitwiseChip.Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
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
open SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Trace SP1Clean.Advance

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Bitwise's committed bus view** — the chip-agnostic `RowView` (opcode `is_xor·3 + is_or·4 + is_and·5`,
the `pc+4` straight-line next-pc, the reassembled result word as `rdWrite`). Standalone so `BitwiseChip.advance`
can be supplied *as* `kind.advance` (see `AddChip.rowView`). -/
def rowView (inp : Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) : Trace.RowView (ZMod p) :=
  ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
    cols.adapter.toAdapterView, inp.is_real,
    BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result,
    cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5, .regWrite⟩

/-- **`BitwiseChip.advance`** — the per-Bitwise-row `try_step` lift (SC Phase 4, the **first multi-op chip**):
a 6-way adapter (`imm_c ∈ {0,1}` register/immediate × the 3 one-hot flags AND/OR/XOR) over the generic
`advance_of_rtype`/`advance_of_itype`. Each flag branch reads its opcode off the committed
`is_xor·3+is_or·4+is_and·5` selector (the Spec's one-hot mutual exclusion zeros the other two → the single op),
and its write-value identity from the Spec's gated `RV64.and`/`or`/`xor` conjunct (`RV64.<op> op_c op_b` is
defeq `execute_RTYPE_pure op_b op_c <OP>` / `execute_ITYPE_pure … <OP>I`). The `advanceReady` bundle carries
the four dispatcher-discharged facts the chip `Spec` does not (`ALUTypeReader` lives in the chip *Assumptions*,
not the `Spec`): the pc-limb bound, the `imm_c` binary, the **at-least-one-flag** routing (the op is pinned by
the program-bus decode, not the chip — see the op-determination note), and the immediate binding
`imm_c=1 → op_c_memory.prev_value = op_c` (the `ALUTypeReader`'s immediate-consistency constraint). Stated to
match the `ChipKind.advance` obligation exactly, so `kind.advance := some (PLift.up advance)` type-checks. -/
theorem advance (inp : Inputs (ZMod p)) (cols : BitwiseChip.Columns (ZMod p)) (data : ProverData (ZMod p))
    (prog : GuestProgram) (s : SailState)
    (hreal : (rowView inp cols).is_real = 1)
    (hspec : Spec inp cols data)
    (hcfg : SailConfigured s) (hrom : RomLoaded prog s)
    (hpcread : s.regs.get? Register.PC = some (rcvPcOf (stateAccess (rowView inp cols))))
    (hvalb : ValueOperandsBound (rowView inp cols) s)
    (hdecrom : decodedInROM prog (programAccess (rowView inp cols)).toRow)
    (hready : inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
      (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
      (cols.is_and = 1 ∨ cols.is_or = 1 ∨ cols.is_xor = 1) ∧
      (rowView inp cols).adapter.op_a ≠ 0 ∧
      (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c)) :
    ∃ s', SailStep s s' ∧ RowEffect prog (rowView inp cols) s s' := by
  obtain ⟨hlink, hpc0, himmc_bin, hflag, hnonX0, himmbind⟩ := hready
  have hreal' : inp.is_real = 1 := hreal
  set r := rowView inp cols with hr
  have vrd : r.rdWrite = BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result := rfl
  have vopbm : r.adapter.op_b_memory = cols.adapter.op_b_memory := rfl
  have vopcm : r.adapter.op_c_memory = cols.adapter.op_c_memory := rfl
  have vopc : r.adapter.op_c = cols.adapter.op_c := rfl
  obtain ⟨-, hgated, -, -, -, hmx_and, hmx_or, hmx_xor⟩ := hspec
  have hg := hgated hreal'
  rcases hflag with h_and | h_or | h_xor
  · -- AND / ANDI
    obtain ⟨hxor0, hor0⟩ := hmx_and h_and
    rcases himmc_bin with h0 | h1
    · have hop : r.opcode = ((ropToOpcode rop.AND).toNat : ZMod p) := by
        simp [hr, rowView, hxor0, hor0, h_and, ropToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_RTYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c_memory.prev_value.toBitVec64 rop.AND := by
        have hand := hg.1 h_and
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hand
        rw [vrd, vopbm, vopcm]; exact hand
      exact advance_of_rtype rop.AND hcfg hrom hpcread hvalb hdecrom hop rfl h0 hnonX0 hpc0 rfl hval
    · have hop : r.opcode = ((iopToOpcode iop.ANDI).toNat : ZMod p) := by
        simp [hr, rowView, hxor0, hor0, h_and, iopToOpcode, Opcode.toNat]
      have hbind := himmbind h1
      have hval : r.rdWrite.toBitVec64 = execute_ITYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c.toBitVec64 iop.ANDI := by
        have hand := hg.1 h_and
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hand
        rw [hbind] at hand; rw [vrd, vopbm, vopc]; exact hand
      exact advance_of_itype iop.ANDI hcfg hrom hpcread hvalb hdecrom hop rfl h1 hnonX0 hpc0 rfl hval
  · -- OR / ORI
    obtain ⟨hxor0, hand0⟩ := hmx_or h_or
    rcases himmc_bin with h0 | h1
    · have hop : r.opcode = ((ropToOpcode rop.OR).toNat : ZMod p) := by
        simp [hr, rowView, hxor0, hand0, h_or, ropToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_RTYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c_memory.prev_value.toBitVec64 rop.OR := by
        have hor := hg.2.1 h_or
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hor
        rw [vrd, vopbm, vopcm]; exact hor
      exact advance_of_rtype rop.OR hcfg hrom hpcread hvalb hdecrom hop rfl h0 hnonX0 hpc0 rfl hval
    · have hop : r.opcode = ((iopToOpcode iop.ORI).toNat : ZMod p) := by
        simp [hr, rowView, hxor0, hand0, h_or, iopToOpcode, Opcode.toNat]
      have hbind := himmbind h1
      have hval : r.rdWrite.toBitVec64 = execute_ITYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c.toBitVec64 iop.ORI := by
        have hor := hg.2.1 h_or
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hor
        rw [hbind] at hor; rw [vrd, vopbm, vopc]; exact hor
      exact advance_of_itype iop.ORI hcfg hrom hpcread hvalb hdecrom hop rfl h1 hnonX0 hpc0 rfl hval
  · -- XOR / XORI
    obtain ⟨hor0, hand0⟩ := hmx_xor h_xor
    rcases himmc_bin with h0 | h1
    · have hop : r.opcode = ((ropToOpcode rop.XOR).toNat : ZMod p) := by
        simp [hr, rowView, hor0, hand0, h_xor, ropToOpcode, Opcode.toNat]
      have hval : r.rdWrite.toBitVec64 = execute_RTYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c_memory.prev_value.toBitVec64 rop.XOR := by
        have hxor := hg.2.2 h_xor
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hxor
        rw [vrd, vopbm, vopcm]; exact hxor
      exact advance_of_rtype rop.XOR hcfg hrom hpcread hvalb hdecrom hop rfl h0 hnonX0 hpc0 rfl hval
    · have hop : r.opcode = ((iopToOpcode iop.XORI).toNat : ZMod p) := by
        simp [hr, rowView, hor0, hand0, h_xor, iopToOpcode, Opcode.toNat]
      have hbind := himmbind h1
      have hval : r.rdWrite.toBitVec64 = execute_ITYPE_pure r.adapter.op_b_memory.prev_value.toBitVec64
          r.adapter.op_c.toBitVec64 iop.XORI := by
        have hxor := hg.2.2 h_xor
        simp only [BitwiseChip.Inputs.op_c_val, BitwiseChip.Inputs.op_b_val, hlink] at hxor
        rw [hbind] at hxor; rw [vrd, vopbm, vopc]; exact hxor
      exact advance_of_itype iop.XORI hcfg hrom hpcread hvalb hdecrom hop rfl h1 hnonX0 hpc0 rfl hval

/-- **Bitwise's `ChipKind` registration.** Program-bus opcode `is_xor·3 + is_or·4 + is_and·5`;
`advance`/`advanceReady` route to `BitwiseChip.advance`, the six-way register/immediate lift. The
`bitwise_chip_reaches_sail_*` declarations remain local semantic helpers. -/
def kind : Soundness.ChipKind p where
  name := "Bitwise"
  Inputs := BitwiseChip.Inputs
  Cols := BitwiseChip.Columns
  view := rowView
  chipSpec := fun inp cols data => Spec inp cols data
  advanceReady := fun inp cols _ _ => inp.adapter = cols.adapter ∧ cols.state.pc[0].val < 2 ^ 16 ∧
    (cols.adapter.imm_c = 0 ∨ cols.adapter.imm_c = 1) ∧
    (cols.is_and = 1 ∨ cols.is_or = 1 ∨ cols.is_xor = 1) ∧
    (rowView inp cols).adapter.op_a ≠ 0 ∧
    (cols.adapter.imm_c = 1 → cols.adapter.op_c_memory.prev_value = cols.adapter.op_c)
  advance := some (PLift.up advance)

end SP1Clean.BitwiseChip
