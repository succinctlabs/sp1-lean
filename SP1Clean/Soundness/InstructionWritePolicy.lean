import SP1Clean.Soundness.StoreWritePolicy
import SP1Clean.Soundness.WitnessDecode

/-! # Write permission for the supported instruction registry

Committed decoding rules out stores for every non-store opcode. The four store families identify
their exact decoded byte intervals with the intervals authorized by the native permission ledger.
The result concerns incoming Sail operands, including stores that leave memory unchanged.
-/

namespace SP1Clean.Soundness

open Model.Core Target Semantics LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Committed non-store opcodes require no memory-write permission. -/
theorem Target.decodedInROM.permittedAt_of_nonstore {program : GuestProgram}
    {row : ProgramChip.ProgramRow (ZMod p)} (decoded : decodedInROM program row)
    {source : SailState} (pc : source.regs.get? Register.PC = some (pcBitsOfRow row))
    (readOnly : ℕ → Bool)
    (nonstore : ∀ width, row.opcode ≠ ((storeOpcode width).toNat : ZMod p)) :
    InstructionWrite.PermittedAt readOnly program source := by
  obtain ⟨word, instruction, fetched, decode, projected⟩ := decoded
  obtain ⟨_, chip, _, routed⟩ := instrToProgramRow'_route_exists projected
  refine ⟨_, word, instruction, pc, fetched, decode,
    InstructionWrite.check_of_nonstore _ _ _ (instructionImageOK_of_instrToProgramRow'_some projected)
      (by simp only [routed, Option.isSome_some]) ?_⟩
  intro offset rs2 rs1 width equal
  subst instruction
  have projected' := instrToProgramRow'_some projected
  have opcode := congrArg (fun value => value.map ProgramChip.ProgramRow.opcode) projected'
  simp only [instrToProgramRow, Option.map_some, Option.some.injEq] at opcode
  exact nonstore width opcode.symm

private theorem nonstore_of_nat {opcode : ZMod p} {value : ℕ}
    (equal : opcode = (value : ZMod p)) (bound : value < 2 ^ 17)
    (outside : value < 36 ∨ 39 < value) :
    ∀ width, opcode ≠ ((storeOpcode width).toNat : ZMod p) := by
  intro width same
  rw [equal] at same
  have valueEq := congrArg ZMod.val same
  rw [ZMod.val_natCast_of_lt (lt_trans bound Fact.out)] at valueEq
  have storeBound : (storeOpcode width).toNat < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    unfold storeOpcode
    split_ifs <;> simp only [Opcode.toNat] <;> omega
  rw [ZMod.val_natCast_of_lt storeBound] at valueEq
  unfold storeOpcode at valueEq
  split_ifs at valueEq <;> simp only [Opcode.toNat] at valueEq <;> omega

private theorem nonstore_of_range {opcode : ZMod p}
    (outside : opcode.val < 36 ∨ 39 < opcode.val) :
    ∀ width, opcode ≠ ((storeOpcode width).toNat : ZMod p) := by
  intro width same
  have storeBound : (storeOpcode width).toNat < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    unfold storeOpcode
    split_ifs <;> simp only [Opcode.toNat] <;> omega
  rw [same, ZMod.val_natCast_of_lt storeBound] at outside
  unfold storeOpcode at outside
  split_ifs at outside <;> simp only [Opcode.toNat] at outside <;> omega

variable [Fact (2 ^ 24 < p)]

/-- Every registered chip authorizes the decoded instruction's complete write footprint from
its proved row contract, grounded readiness, and native byte-permission ledger. -/
theorem supportedChipFor_write_permittedAt (id : InstructionChipId) :
    ∀ (input : (supportedChipFor (p := p) id).kind.Inputs (ZMod p))
      (cols : (supportedChipFor (p := p) id).kind.Cols (ZMod p))
      (data : ProverData (ZMod p)) (program : GuestProgram) (source : SailState),
      ((supportedChipFor id).kind.view input cols).is_real = 1 →
      (supportedChipFor id).kind.chipSpec input cols data →
      (supportedChipFor id).kind.advanceReady input cols program source →
      source.regs.get? Register.PC =
        some (pcBitsOfRow (programAccess ((supportedChipFor id).kind.view input cols)).toRow) →
      ValueOperandsBound ((supportedChipFor id).kind.view input cols) source →
      decodedInROM program (programAccess ((supportedChipFor id).kind.view input cols)).toRow →
      ∀ image : ProgramImage, RowWritePermitted image ((supportedChipFor id).kind.view input cols) →
        InstructionWrite.PermittedAt image.readOnly program source := by
  cases id <;> intro input cols data program source real spec ready pc operands decoded image permitted

  case add =>
    change decodedInROM program (programAccess (AddChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 0) (by change (0 : ZMod p) = (0 : ℕ); norm_num) (by decide) (by decide))
  case addi =>
    change decodedInROM program (programAccess (AddiChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 1) (by change (1 : ZMod p) = (1 : ℕ); norm_num) (by decide) (by decide))
  case addw =>
    change decodedInROM program (programAccess (AddwChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 19) rfl (by decide) (by decide))
  case sub =>
    change decodedInROM program (programAccess (SubChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 2) rfl (by decide) (by decide))
  case subw =>
    change decodedInROM program (programAccess (SubwChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 20) rfl (by decide) (by decide))
  case jal =>
    change decodedInROM program (programAccess (JalChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 46) rfl (by decide) (by decide))
  case jalr =>
    change decodedInROM program (programAccess (JalrChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 47) rfl (by decide) (by decide))
  case loadDouble =>
    change decodedInROM program (programAccess (LoadDoubleChip.rowView input cols)).toRow at decoded
    exact decoded.permittedAt_of_nonstore pc image.readOnly
      (nonstore_of_nat (value := 35) rfl (by decide) (by decide))
  case storeByte =>
    change decodedInROM program (programAccess (StoreByteChip.rowView input cols)).toRow at decoded
    exact StoreByteChip.write_permittedAt input cols data program source real spec
      ready.2.1 ready.2.2.1 pc operands decoded permitted
  case storeHalf =>
    change decodedInROM program (programAccess (StoreHalfChip.rowView input cols)).toRow at decoded
    exact StoreHalfChip.write_permittedAt input cols data program source real spec
      ready.2.1 ready.2.2.1 pc operands decoded permitted
  case storeWord =>
    change decodedInROM program (programAccess (StoreWordChip.rowView input cols)).toRow at decoded
    exact StoreWordChip.write_permittedAt input cols data program source real spec
      ready.2.1 ready.2.2.1 pc operands decoded permitted
  case storeDouble =>
    change decodedInROM program (programAccess (StoreDoubleChip.rowView input cols)).toRow at decoded
    exact StoreDoubleChip.write_permittedAt input cols data program source real spec
      ready.2.1 ready.2.2.1 pc operands decoded permitted
  case bitwise =>
    change decodedInROM program (programAccess (BitwiseChip.rowView input cols)).toRow at decoded
    have flags := ready.2.2.2.1
    rcases flags with active | active | active
    · have others := spec.2.2.2.2.2.1 active
      apply decoded.permittedAt_of_nonstore pc image.readOnly
      exact nonstore_of_nat (value := 5) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide) (by decide)
    · have others := spec.2.2.2.2.2.2.1 active
      apply decoded.permittedAt_of_nonstore pc image.readOnly
      exact nonstore_of_nat (value := 4) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide) (by decide)
    · have others := spec.2.2.2.2.2.2.2 active
      apply decoded.permittedAt_of_nonstore pc image.readOnly
      exact nonstore_of_nat (value := 3) (by simp [programAccess, ProgramAccess.toRow, BitwiseChip.rowView, active, others.1, others.2])
        (by decide) (by decide)
  case lt =>
    change decodedInROM program (programAccess (LtChip.rowView input cols)).toRow at decoded
    rcases ready.2.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 9) (by simp [programAccess, ProgramAccess.toRow, LtChip.rowView, a, b]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 10) (by simp [programAccess, ProgramAccess.toRow, LtChip.rowView, a, b]) (by decide) (by decide))
  case shiftLeft =>
    change decodedInROM program (programAccess (ShiftLeftChip.rowView input cols)).toRow at decoded
    rcases ready.2.2.2.2.2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 6) (by simp [programAccess, ProgramAccess.toRow, ShiftLeftChip.rowView, a, b]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 21) (by simp [programAccess, ProgramAccess.toRow, ShiftLeftChip.rowView, a, b]) (by decide) (by decide))
  case loadByte =>
    change decodedInROM program (programAccess (LoadByteChip.rowView input cols)).toRow at decoded
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 29) (by simp [programAccess, ProgramAccess.toRow, LoadByteChip.rowView, a, b]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 32) (by simp [programAccess, ProgramAccess.toRow, LoadByteChip.rowView, a, b]) (by decide) (by decide))
  case loadHalf =>
    change decodedInROM program (programAccess (LoadHalfChip.rowView input cols)).toRow at decoded
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 30) (by simp [programAccess, ProgramAccess.toRow, LoadHalfChip.rowView, a, b]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 33) (by simp [programAccess, ProgramAccess.toRow, LoadHalfChip.rowView, a, b]) (by decide) (by decide))
  case loadWord =>
    change decodedInROM program (programAccess (LoadWordChip.rowView input cols)).toRow at decoded
    rcases ready.2.2.1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 31) (by simp [programAccess, ProgramAccess.toRow, LoadWordChip.rowView, a, b]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 34) (by simp [programAccess, ProgramAccess.toRow, LoadWordChip.rowView, a, b]) (by decide) (by decide))
  case shiftRight =>
    change decodedInROM program (programAccess (ShiftRightChip.rowView input cols)).toRow at decoded
    have flags := ready.2.2.2.2.2
    rcases flags with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 7) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 8) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 22) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 23) (by simp [programAccess, ProgramAccess.toRow, ShiftRightChip.rowView, h0, h1, h2, h3])
          (by decide) (by decide))
  case mul =>
    change decodedInROM program (programAccess (MulChip.rowView input cols)).toRow at decoded
    have flags := ready.2.2
    simp only [MulChip.SelectorOneHot, MulChip.selectors] at flags
    rcases flags with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 11) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 12) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 13) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 14) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 24) (by simp [programAccess, ProgramAccess.toRow, MulChip.rowView, h0, h1, h2, h3, h4])
          (by decide) (by decide))
  case branch =>
    change decodedInROM program (programAccess (BranchChip.rowView input cols)).toRow at decoded
    have flags := spec.2.2.2.1 real
    simp only [BranchChip.flagsOneHot] at flags
    rcases flags with ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 40) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 41) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 42) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 43) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 44) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 45) (by simp [programAccess, ProgramAccess.toRow, BranchChip.rowView, BranchChip.branchOpcode, h0, h1, h2, h3, h4, h5])
          (by decide) (by decide))
  case uType =>
    change decodedInROM program (programAccess (UTypeChip.rowView input cols)).toRow at decoded
    rcases ready.2 with flag | flag
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 49) (by simp [programAccess, ProgramAccess.toRow, UTypeChip.rowView, flag]) (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 48) (by simp [programAccess, ProgramAccess.toRow, UTypeChip.rowView, flag]) (by decide) (by decide))
  case divRem =>
    change decodedInROM program (programAccess (DivRemChip.rowView input cols)).toRow at decoded
    obtain ⟨selected, selection⟩ := spec.2.selection real
    apply decoded.permittedAt_of_nonstore pc image.readOnly
    exact nonstore_of_nat selection.encodedOpcode
      (by cases selected <;> decide) (by cases selected <;> decide)
  case aluX0 =>
    change decodedInROM program (programAccess (AluX0Chip.rowView input cols)).toRow at decoded
    apply decoded.permittedAt_of_nonstore pc image.readOnly
    exact nonstore_of_range (Or.inl (lt_trans ready.2.2 (by decide)))
  case loadX0 =>
    change decodedInROM program (programAccess (LoadX0Chip.rowView input cols)).toRow at decoded
    rcases ready.2.2 with ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩ |
      ⟨opcode, _⟩ | ⟨opcode, _⟩ | ⟨opcode, _⟩
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 29) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 32) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 30) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 33) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 31) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 34) opcode (by decide) (by decide))
    · exact decoded.permittedAt_of_nonstore pc image.readOnly
        (nonstore_of_nat (value := 35) opcode (by decide) (by decide))

/-- The registry result at an actual decoded physical row. Static soundness and grounded
readiness are supplied by the existing chip contracts, without a new permission assumption. -/
theorem DecodedInstructionRow.write_permittedAt (row : DecodedInstructionRow p)
    (registered : row.chip ∈ supportedChips (p := p)) (data : ProverData (ZMod p))
    (program : GuestProgram) (source : SailState)
    (real : (row.toChipRow data).is_real = 1)
    (spec : (row.toChipRow data).chipSpec data)
    (ready : (row.toChipRow data).kind.advanceReady
      (row.toChipRow data).inputs (row.toChipRow data).cols program source)
    (pc : source.regs.get? Register.PC = some (pcBitsOfRow (programAccess (row.toChipRow data).view).toRow))
    (operands : ValueOperandsBound (row.toChipRow data).view source)
    (decoded : decodedInROM program (programAccess (row.toChipRow data).view).toRow)
    {image : ProgramImage} (permitted : RowWritePermitted image (row.toChipRow data).view) :
    InstructionWrite.PermittedAt image.readOnly program source := by
  obtain ⟨chip, physical⟩ := row
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp registered
  exact supportedChipFor_write_permittedAt id _ _ data program source real spec ready
    pc operands decoded image permitted

end SP1Clean.Soundness
