import SP1Clean.Model.Core.InstructionWrite
import SP1Clean.Soundness.RomWriteProtection
import SP1Clean.Alignment.Chips.StoreByteChip.Bridge
import SP1Clean.Alignment.Chips.StoreHalfChip.Bridge
import SP1Clean.Alignment.Chips.StoreWordChip.Bridge
import SP1Clean.Alignment.Chips.StoreDoubleChip.Bridge

/-! # Store permissions at the decoded Sail operands

The native byte-permission ledger constrains a chip's committed write. These adapters identify
that interval with the independently computed instruction footprint, using the committed decode,
live base-register observation and address arithmetic. No target-memory difference is inspected,
so a same-value write cannot disappear from the permission obligation.
-/

namespace SP1Clean.Soundness.Target

open Model.Core Semantics LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Canonical address limbs represent the same wrapped RV64 effective address as Sail. -/
private theorem address_spec_value (input : AddressOperation.Inputs (ZMod p))
    (cols : Circuits.Types.AddressOperation (ZMod p))
    (spec : AddressOperation.Spec input cols)
    (base : Word.isU64 input.b) (immediate : Word.isU64 input.cc) :
    Address.toNat cols.addr_operation.value = (AddressOperation.effectiveAddress input).toNat := by
  rw [← AddressOperation.addressMod48_eq_effectiveAddress_toNat base immediate
    (AddressOperation.validAddress_of_spec spec), ← spec.1]
  unfold Address.toNat
  ring

/-- Reconcile the exact committed store interval with its official decoded operands. -/
theorem store_permittedAt {image : ProgramImage} {program : GuestProgram}
    {row : Trace.RowView (ZMod p)} {source : SailState}
    (width : LeanRV64D.Defs.word_width) (validWidth : storeWidthOK width = true)
    (decoded : decodedInROM program (programAccess row).toRow)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess row).toRow))
    (opcode : row.opcode = ((storeOpcode width).toNat : ZMod p))
    (baseReg : row.adapter.imm_b = 0) (immediate : row.adapter.imm_c = 1)
    (operands : ValueOperandsBound row source)
    (write : Trace.MemWrite (ZMod p)) (written : row.commit.memWrite = some write)
    (size : write.width = width.toNat)
    (address : write.addrNat =
      (Word.toBitVec64 row.adapter.op_b_memory.prev_value + Word.toBitVec64 row.adapter.op_c).toNat)
    (permitted : RowWritePermitted image row) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  obtain ⟨word, offset, rs2, rs1, fetch, decode, _, baseIndex, immediateWord⟩ :=
    decodesStore' width validWidth decoded opcode immediate
  change row.adapter.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] at baseIndex
  change row.adapter.op_c = bitVecToWord (offset.signExtend 64) at immediateWord
  have observed := operands.1 rs1 baseReg (by rw [baseIndex]; rfl)
  refine ⟨_, word, .STORE (offset, .Regidx rs2, .Regidx rs1, width), pc, fetch, decode, ?_⟩
  apply (InstructionWrite.check_store_iff _ _ _ _ _ _ validWidth).mpr
  refine ⟨_, observed, ?_⟩
  have effective : write.addrNat =
      (memoryEffectiveAddress (Word.toBitVec64 row.adapter.op_b_memory.prev_value) offset).toNat := by
    rw [address, immediateWord, toBitVec64_bitVecToWord]
    rfl
  intro index bound
  apply permitted write written
  unfold Trace.MemWrite.covers
  rw [effective, size]
  omega

end SP1Clean.Soundness.Target

namespace SP1Clean.StoreByteChip

open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Model.Core LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The protected store's byte permissions authorize its actual decoded Sail write. -/
theorem write_permittedAt (input : Inputs (ZMod p)) (cols : Columns (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState)
    (real : input.is_real = 1) (spec : Spec input cols data)
    (base : Word.isU64 input.op_b_val) (immediate : Word.isU64 input.op_c_imm)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (rowView input cols)).toRow))
    (operands : ValueOperandsBound (rowView input cols) source)
    (decoded : decodedInROM program (programAccess (rowView input cols)).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (rowView input cols)) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  apply store_permittedAt 1 (by decide) decoded pc (by norm_num [rowView, storeOpcode, Opcode.toNat])
    rfl rfl operands
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 1⟩
    rfl rfl ?_ permitted
  exact address_spec_value
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1], input.offset_bit[2], input.is_real⟩
    cols.address_operation (spec.1.2.2.2 real) base immediate

end SP1Clean.StoreByteChip


namespace SP1Clean.StoreHalfChip

open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Model.Core LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The protected store's byte permissions authorize its actual decoded Sail write. -/
theorem write_permittedAt (input : Inputs (ZMod p)) (cols : Columns (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState)
    (real : input.is_real = 1) (spec : Spec input cols data)
    (base : Word.isU64 input.op_b_val) (immediate : Word.isU64 input.op_c_imm)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (rowView input cols)).toRow))
    (operands : ValueOperandsBound (rowView input cols) source)
    (decoded : decodedInROM program (programAccess (rowView input cols)).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (rowView input cols)) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  apply store_permittedAt 2 (by decide) decoded pc (by norm_num [rowView, storeOpcode, Opcode.toNat])
    rfl rfl operands
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 2⟩
    rfl rfl ?_ permitted
  exact address_spec_value
    ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0], input.offset_bit[1], input.is_real⟩
    cols.address_operation (spec.1.2.2.2 real) base immediate

end SP1Clean.StoreHalfChip


namespace SP1Clean.StoreWordChip

open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Model.Core LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The protected store's byte permissions authorize its actual decoded Sail write. -/
theorem write_permittedAt (input : Inputs (ZMod p)) (cols : Columns (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState)
    (real : input.is_real = 1) (spec : Spec input cols data)
    (base : Word.isU64 input.op_b_val) (immediate : Word.isU64 input.op_c_imm)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (rowView input cols)).toRow))
    (operands : ValueOperandsBound (rowView input cols) source)
    (decoded : decodedInROM program (programAccess (rowView input cols)).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (rowView input cols)) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  apply store_permittedAt 4 (by decide) decoded pc (by norm_num [rowView, storeOpcode, Opcode.toNat])
    rfl rfl operands
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 4⟩
    rfl rfl ?_ permitted
  exact address_spec_value
    ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit, input.is_real⟩
    cols.address_operation (spec.1.2.2.2 real) base immediate

end SP1Clean.StoreWordChip


namespace SP1Clean.StoreDoubleChip

open SP1Clean.Soundness SP1Clean.Soundness.Target SP1Clean.Model.Core LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The protected store's byte permissions authorize its actual decoded Sail write. -/
theorem write_permittedAt (input : Inputs (ZMod p)) (cols : Columns (ZMod p))
    (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState)
    (real : input.is_real = 1) (spec : Spec input cols data)
    (base : Word.isU64 input.op_b_val) (immediate : Word.isU64 input.op_c_imm)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (rowView input cols)).toRow))
    (operands : ValueOperandsBound (rowView input cols) source)
    (decoded : decodedInROM program (programAccess (rowView input cols)).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (rowView input cols)) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  apply store_permittedAt 8 (by decide) decoded pc (by norm_num [rowView, storeOpcode, Opcode.toNat])
    rfl rfl operands
    ⟨cols.address_operation.addr_operation.value, input.adapter.op_a_memory.prev_value, 8⟩
    rfl rfl ?_ permitted
  exact address_spec_value
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
    cols.address_operation (spec.1.2.2.2 real) base immediate

end SP1Clean.StoreDoubleChip
