import ToClean.Gadgets.LookupProjection
import SP1CleanTest.Alignment.Support.BranchEnsembleFixture
import ToClean.Air.EnsembleCheck

/-! # Complete static lookup meanings of the branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

/-- Full finite lookup meanings, including installed tables with no physical rows in this fixture. -/
def fixed (_target : MemorySnapshot) : List (FiniteLookup Fp) :=
  [FiniteLookup.ofStatic (image.programTable (p := SP1Prime)),
    FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime)),
    FiniteLookup.ofStatic (image.writePermissionTable (p := SP1Prime)),
    FiniteLookup.ofStatic (HintQueue.sourceTable (p := SP1Prime) []),
    FiniteLookup.ofStatic (HintQueue.sourceWordTable (p := SP1Prime) [])]


/-- Static lookup indices for every installed component, including all currently empty providers. -/
def componentLookupIndices : List (List (Fin 5)) :=
  [[], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1], [], [], [2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3], [4], [], [], [], [], [], []]

/-- Component selection ranges over all 93 installed physical slots. -/
abbrev componentAt (target : MemorySnapshot) (index : Fin 93) : Component Fp :=
  (assembly target).tables[index.val]'(by change index.val < 93; exact index.isLt)

/-- The lookup rows promised for one installed component. -/
def fixedFor (target : MemorySnapshot) (index : Fin 93) : List (RawTable Fp) :=
  (componentLookupIndices[index.val]'(by change index.val < 93; exact index.isLt)).map fun table =>
    ((fixed target)[table.val]'(by change table.val < 5; exact table.isLt)).table

attribute [local circuit_norm]
  Gadgets.BitwiseByte.circuit
  Gadgets.Conditional.circuit
  Gadgets.Conditional.main
  Gadgets.Equality.circuit
  Gadgets.Equality.main
  Gadgets.IsEqual.circuit
  Gadgets.IsEqual.main
  Gadgets.IsZero.circuit
  Gadgets.IsZero.main
  Gadgets.IsZeroField.circuit
  SP1Clean.AddChip.circuit
  SP1Clean.AddChip.main
  SP1Clean.AddOperation.circuit
  SP1Clean.AddOperation.main
  SP1Clean.AddiChip.circuit
  SP1Clean.AddiChip.main
  SP1Clean.AddrAddOperation.circuit
  SP1Clean.AddrAddOperation.main
  SP1Clean.AddressDiv8.circuit
  SP1Clean.AddressDiv8.main
  SP1Clean.AddressOperation.circuit
  SP1Clean.AddressOperation.main
  SP1Clean.AddressOrder.circuit
  SP1Clean.AddressOrder.main
  SP1Clean.AddwChip.circuit
  SP1Clean.AddwChip.main
  SP1Clean.AddwOperation.circuit
  SP1Clean.AddwOperation.main
  SP1Clean.AluX0Chip.circuit
  SP1Clean.AluX0Chip.main
  SP1Clean.BitwiseChip.circuit
  SP1Clean.BitwiseChip.main
  SP1Clean.BitwiseOperation.circuit
  SP1Clean.BitwiseOperation.main
  SP1Clean.BitwiseU16Operation.circuit
  SP1Clean.BitwiseU16Operation.main
  SP1Clean.BoundedWord.circuit
  SP1Clean.BoundedWord.main
  SP1Clean.BranchChip.circuit
  SP1Clean.BranchChip.main
  SP1Clean.ByteChip.AndByte.circuit
  SP1Clean.ByteChip.AndByte.main
  SP1Clean.ByteChip.Ltu.circuit
  SP1Clean.ByteChip.Ltu.main
  SP1Clean.ByteChip.MSB.circuit
  SP1Clean.ByteChip.MSB.main
  SP1Clean.ByteChip.OrByte.circuit
  SP1Clean.ByteChip.OrByte.main
  SP1Clean.ByteChip.U8Range.circuit
  SP1Clean.ByteChip.U8Range.main
  SP1Clean.ByteChip.XorByte.circuit
  SP1Clean.ByteChip.XorByte.main
  SP1Clean.ClockOrder.circuit
  SP1Clean.ClockOrder.main
  SP1Clean.CoreSyscallChip.circuit
  SP1Clean.CoreSyscallChip.main
  SP1Clean.DecodedProgramProvider.circuit
  SP1Clean.DivRemChip.circuit
  SP1Clean.DivRemChip.main
  SP1Clean.DivRemCompare.circuit
  SP1Clean.DivRemCompare.main
  SP1Clean.DivRemCore.circuit
  SP1Clean.DivRemCore.main
  SP1Clean.FinalMemoryChange.circuit
  SP1Clean.FinalMemoryChange.main
  SP1Clean.FinalMemoryChangeBoundary.circuit
  SP1Clean.FinalMemoryChangeBoundary.main
  SP1Clean.FinalMemoryReceipt.circuit
  SP1Clean.FinalRamCheck.circuit
  SP1Clean.FinalRamCheck.main
  SP1Clean.FinalRamProvider.circuit
  SP1Clean.FinalRamProvider.main
  SP1Clean.FinalRamValue.circuit
  SP1Clean.FinalRamValue.main
  SP1Clean.FinalRegisterCheck.circuit
  SP1Clean.FinalRegisterCheck.main
  SP1Clean.FinalRegisterProvider.circuit
  SP1Clean.FinalRegisterProvider.main
  SP1Clean.FinalRegisterValue.circuit
  SP1Clean.FinalRegisterValue.main
  SP1Clean.FixedProgramProvider.circuit
  SP1Clean.HaltChip.circuit
  SP1Clean.HaltChip.main
  SP1Clean.HaltPaddingChip.circuit
  SP1Clean.HaltPaddingChip.main
  SP1Clean.HintReadSpan.circuit
  SP1Clean.HintReadSpan.main
  SP1Clean.HintReadStep.circuit
  SP1Clean.HintReadStep.main
  SP1Clean.HintReadWordChip.circuit
  SP1Clean.HintReadWordChip.main
  SP1Clean.HostBoundary.circuit
  SP1Clean.HostBoundary.main
  SP1Clean.HostCallChip.circuit
  SP1Clean.HostCallChip.main
  SP1Clean.HostCommitChip.circuit
  SP1Clean.HostCommitChip.main
  SP1Clean.HostCommitEndpoint.circuit
  SP1Clean.HostCommitEndpoint.main
  SP1Clean.HostEnterChip.circuit
  SP1Clean.HostEnterChip.main
  SP1Clean.HostExitBoundary.circuit
  SP1Clean.HostExitBoundary.main
  SP1Clean.HostHaltChip.circuit
  SP1Clean.HostHaltChip.main
  SP1Clean.HostHintLengthChip.circuit
  SP1Clean.HostHintLengthChip.main
  SP1Clean.HostHintQueueBoundary.circuit
  SP1Clean.HostHintQueueBoundary.main
  SP1Clean.HostHintReadChip.circuit
  SP1Clean.HostHintReadChip.main
  SP1Clean.HostRamAccessChip.circuit
  SP1Clean.HostRamAccessChip.main
  SP1Clean.InitialMemoryLookup.circuit
  SP1Clean.InitialMemoryLookup.main
  SP1Clean.InitialMemoryRead.circuit
  SP1Clean.InitialMemoryRead.main
  SP1Clean.InitialRamProvider.circuit
  SP1Clean.InitialRamProvider.main
  SP1Clean.InitialRegisterProvider.circuit
  SP1Clean.InitialRegisterProvider.main
  SP1Clean.IsEqualWordOperation.circuit
  SP1Clean.IsEqualWordOperation.main
  SP1Clean.IsZeroOperation.circuit
  SP1Clean.IsZeroOperation.main
  SP1Clean.IsZeroWordOperation.circuit
  SP1Clean.IsZeroWordOperation.main
  SP1Clean.JalChip.circuit
  SP1Clean.JalChip.main
  SP1Clean.JalrChip.circuit
  SP1Clean.JalrChip.main
  SP1Clean.LoadByteChip.circuit
  SP1Clean.LoadByteChip.main
  SP1Clean.LoadDoubleChip.circuit
  SP1Clean.LoadDoubleChip.main
  SP1Clean.LoadHalfChip.circuit
  SP1Clean.LoadHalfChip.main
  SP1Clean.LoadWordChip.circuit
  SP1Clean.LoadWordChip.main
  SP1Clean.LoadX0Chip.circuit
  SP1Clean.LoadX0Chip.main
  SP1Clean.LtChip.circuit
  SP1Clean.LtChip.main
  SP1Clean.LtOperationSigned.circuit
  SP1Clean.LtOperationSigned.main
  SP1Clean.LtOperationUnsigned.circuit
  SP1Clean.LtOperationUnsigned.main
  SP1Clean.MemoryBumpChip.circuit
  SP1Clean.MemoryBumpChip.main
  SP1Clean.MemoryFinalizeChip.circuit
  SP1Clean.MemoryFinalizeChip.main
  SP1Clean.MemoryProviderChip.circuit
  SP1Clean.MemoryProviderChip.main
  SP1Clean.MulChip.circuit
  SP1Clean.MulChip.main
  SP1Clean.MulOperation.circuit
  SP1Clean.MulOperation.main
  SP1Clean.OrderedBoundary.circuit
  SP1Clean.OrderedBoundary.main
  SP1Clean.OrderedBoundaryEnd.circuit
  SP1Clean.OrderedBoundaryEnd.main
  SP1Clean.OrderedBoundaryVerifier.circuit
  SP1Clean.OrderedBoundaryVerifier.main
  SP1Clean.OrderedInitialProvider.circuit
  SP1Clean.OrderedInitialProvider.main
  SP1Clean.OrderedMemoryProvider.circuit
  SP1Clean.OrderedMemoryProvider.main
  SP1Clean.OrderedSnapshotProvider.circuit
  SP1Clean.ProgramProviderChip.circuit
  SP1Clean.ProgramProviderChip.main
  SP1Clean.RangeChip.circuit
  SP1Clean.RangeChip.main
  SP1Clean.Readers.ALUTypeReader.circuit
  SP1Clean.Readers.ALUTypeReader.main
  SP1Clean.Readers.ALUTypeReaderImmutable.circuit
  SP1Clean.Readers.ALUTypeReaderImmutable.main
  SP1Clean.Readers.CPUState.circuit
  SP1Clean.Readers.CPUState.main
  SP1Clean.Readers.ITypeReader.circuit
  SP1Clean.Readers.ITypeReader.main
  SP1Clean.Readers.ITypeReaderImmutable.circuit
  SP1Clean.Readers.ITypeReaderImmutable.main
  SP1Clean.Readers.JTypeReader.circuit
  SP1Clean.Readers.JTypeReader.main
  SP1Clean.Readers.MemoryAccess.circuit
  SP1Clean.Readers.MemoryAccess.main
  SP1Clean.Readers.RTypeReader.circuit
  SP1Clean.Readers.RTypeReader.main
  SP1Clean.Readers.RegisterAccessCols.circuit
  SP1Clean.Readers.RegisterAccessCols.main
  SP1Clean.Readers.RegisterAccessTimestamp.circuit
  SP1Clean.Readers.RegisterAccessTimestamp.main
  SP1Clean.Readers.RegisterRead.circuit
  SP1Clean.Readers.RegisterRead.main
  SP1Clean.Readers.RegisterWrite.circuit
  SP1Clean.Readers.RegisterWrite.main
  SP1Clean.ShiftLeftChip.circuit
  SP1Clean.ShiftLeftChip.main
  SP1Clean.ShiftLeftCore.circuit
  SP1Clean.ShiftLeftCore.main
  SP1Clean.ShiftRightChip.circuit
  SP1Clean.ShiftRightChip.main
  SP1Clean.ShiftRightCore.circuit
  SP1Clean.ShiftRightCore.main
  SP1Clean.SnapshotRamProvider.circuit
  SP1Clean.SnapshotRamProvider.main
  SP1Clean.SnapshotRegisterProvider.circuit
  SP1Clean.SnapshotRegisterProvider.main
  SP1Clean.Soundness.SupportedChip.circuit
  SP1Clean.StateBumpChip.circuit
  SP1Clean.StateBumpChip.main
  SP1Clean.StoreByteChip.circuit
  SP1Clean.StoreByteChip.main
  SP1Clean.StoreDoubleChip.circuit
  SP1Clean.StoreDoubleChip.main
  SP1Clean.StoreHalfChip.circuit
  SP1Clean.StoreHalfChip.main
  SP1Clean.StoreWordChip.circuit
  SP1Clean.StoreWordChip.main
  SP1Clean.SubChip.circuit
  SP1Clean.SubChip.main
  SP1Clean.SubOperation.circuit
  SP1Clean.SubOperation.main
  SP1Clean.SubwChip.circuit
  SP1Clean.SubwChip.main
  SP1Clean.SubwOperation.circuit
  SP1Clean.SubwOperation.main
  SP1Clean.SyscallCodeGuard.circuit
  SP1Clean.SyscallCodeGuard.main
  SP1Clean.SyscallInstrsChip.CommitArm.circuit
  SP1Clean.SyscallInstrsChip.CommitArm.main
  SP1Clean.SyscallInstrsChip.DispatchArm.circuit
  SP1Clean.SyscallInstrsChip.DispatchArm.main
  SP1Clean.SyscallInstrsChip.FieldBoundArm.circuit
  SP1Clean.SyscallInstrsChip.FieldBoundArm.main
  SP1Clean.SyscallInstrsChip.PcArm.circuit
  SP1Clean.SyscallInstrsChip.PcArm.main
  SP1Clean.SyscallInstrsChip.WriteArm.circuit
  SP1Clean.SyscallInstrsChip.WriteArm.main
  SP1Clean.SyscallInstrsChip.circuit
  SP1Clean.SyscallInstrsChip.main
  SP1Clean.U16CompareOperation.circuit
  SP1Clean.U16CompareOperation.main
  SP1Clean.U16MSBOperation.circuit
  SP1Clean.U16MSBOperation.main
  SP1Clean.U16toU8OperationSafe.circuit
  SP1Clean.U16toU8OperationSafe.main
  SP1Clean.UTypeChip.circuit
  SP1Clean.UTypeChip.main
  SP1Clean.WordRangeCheck.circuit
  SP1Clean.WordRangeCheck.main
  SP1Clean.WritePermissionProvider.circuit
  SP1Clean.WritePermissionProvider.main


attribute [local circuit_norm] supportedChipFor RangeChip.circuitFor
  ProtectedStore.byte ProtectedStore.half ProtectedStore.word ProtectedStore.double
  DivRemChip.populateRow DivRemChip.constrainRow DivRemChip.assertZeros
  HostHintQueue.source HostHintQueue.sourceMain HostHintQueue.sourceWord HostHintQueue.sourceWordMain
  HostCommitBoundary.terminal HostCommitBoundary.terminalMain

-- Normalize proof-bearing wrappers only through their operation projection lemmas.
attribute [local circuit_norm] List.append_eq Component.rowOperations
  GeneralFormalCircuit.toSubcircuit_lookups FormalAssertion.toSubcircuit_toFlat
  GeneralFormalCircuit.WithHint.toSubcircuit_lookups FormalCircuit.toSubcircuit_lookups
  Operations.lookups_toFlat Operations.lookups Operations.toNested_toFlat FlatOperation.lookups
  Gadgets.ToBits.rangeCheck Gadgets.ToBits.toBits
  fixedFor componentLookupIndices fixed FiniteLookup.ofStatic
  InitialMemoryLookup.circuitNamed InitialMemoryRead.circuitNamed
  OrderedFinalProvider.registerCircuit OrderedFinalProvider.ramCircuit

/-- Raw lookup identities at physical component 0. -/
private theorem lookup_slot_0 (target : MemorySnapshot) :
    (componentAt target 0).rowOperations.lookups.map (·.table) = fixedFor target 0 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 1. -/
private theorem lookup_slot_1 (target : MemorySnapshot) :
    (componentAt target 1).rowOperations.lookups.map (·.table) = fixedFor target 1 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 2. -/
private theorem lookup_slot_2 (target : MemorySnapshot) :
    (componentAt target 2).rowOperations.lookups.map (·.table) = fixedFor target 2 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 3. -/
private theorem lookup_slot_3 (target : MemorySnapshot) :
    (componentAt target 3).rowOperations.lookups.map (·.table) = fixedFor target 3 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 4. -/
private theorem lookup_slot_4 (target : MemorySnapshot) :
    (componentAt target 4).rowOperations.lookups.map (·.table) = fixedFor target 4 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 5. -/
private theorem lookup_slot_5 (target : MemorySnapshot) :
    (componentAt target 5).rowOperations.lookups.map (·.table) = fixedFor target 5 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 6. -/
private theorem lookup_slot_6 (target : MemorySnapshot) :
    (componentAt target 6).rowOperations.lookups.map (·.table) = fixedFor target 6 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 7. -/
private theorem lookup_slot_7 (target : MemorySnapshot) :
    (componentAt target 7).rowOperations.lookups.map (·.table) = fixedFor target 7 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 8. -/
private theorem lookup_slot_8 (target : MemorySnapshot) :
    (componentAt target 8).rowOperations.lookups.map (·.table) = fixedFor target 8 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 9. -/
private theorem lookup_slot_9 (target : MemorySnapshot) :
    (componentAt target 9).rowOperations.lookups.map (·.table) = fixedFor target 9 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 10. -/
private theorem lookup_slot_10 (target : MemorySnapshot) :
    (componentAt target 10).rowOperations.lookups.map (·.table) = fixedFor target 10 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 11. -/
private theorem lookup_slot_11 (target : MemorySnapshot) :
    (componentAt target 11).rowOperations.lookups.map (·.table) = fixedFor target 11 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 12. -/
private theorem lookup_slot_12 (target : MemorySnapshot) :
    (componentAt target 12).rowOperations.lookups.map (·.table) = fixedFor target 12 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 13. -/
private theorem lookup_slot_13 (target : MemorySnapshot) :
    (componentAt target 13).rowOperations.lookups.map (·.table) = fixedFor target 13 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 14. -/
private theorem lookup_slot_14 (target : MemorySnapshot) :
    (componentAt target 14).rowOperations.lookups.map (·.table) = fixedFor target 14 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 15. -/
private theorem lookup_slot_15 (target : MemorySnapshot) :
    (componentAt target 15).rowOperations.lookups.map (·.table) = fixedFor target 15 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 16. -/
private theorem lookup_slot_16 (target : MemorySnapshot) :
    (componentAt target 16).rowOperations.lookups.map (·.table) = fixedFor target 16 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 17. -/
private theorem lookup_slot_17 (target : MemorySnapshot) :
    (componentAt target 17).rowOperations.lookups.map (·.table) = fixedFor target 17 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 18. -/
private theorem lookup_slot_18 (target : MemorySnapshot) :
    (componentAt target 18).rowOperations.lookups.map (·.table) = fixedFor target 18 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 19. -/
private theorem lookup_slot_19 (target : MemorySnapshot) :
    (componentAt target 19).rowOperations.lookups.map (·.table) = fixedFor target 19 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 20. -/
private theorem lookup_slot_20 (target : MemorySnapshot) :
    (componentAt target 20).rowOperations.lookups.map (·.table) = fixedFor target 20 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 21. -/
private theorem lookup_slot_21 (target : MemorySnapshot) :
    (componentAt target 21).rowOperations.lookups.map (·.table) = fixedFor target 21 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 22. -/
private theorem lookup_slot_22 (target : MemorySnapshot) :
    (componentAt target 22).rowOperations.lookups.map (·.table) = fixedFor target 22 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 23. -/
private theorem lookup_slot_23 (target : MemorySnapshot) :
    (componentAt target 23).rowOperations.lookups.map (·.table) = fixedFor target 23 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 24. -/
private theorem lookup_slot_24 (target : MemorySnapshot) :
    (componentAt target 24).rowOperations.lookups.map (·.table) = fixedFor target 24 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 25. -/
private theorem lookup_slot_25 (target : MemorySnapshot) :
    (componentAt target 25).rowOperations.lookups.map (·.table) = fixedFor target 25 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 26. -/
private theorem lookup_slot_26 (target : MemorySnapshot) :
    (componentAt target 26).rowOperations.lookups.map (·.table) = fixedFor target 26 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 27. -/
private theorem lookup_slot_27 (target : MemorySnapshot) :
    (componentAt target 27).rowOperations.lookups.map (·.table) = fixedFor target 27 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 28. -/
private theorem lookup_slot_28 (target : MemorySnapshot) :
    (componentAt target 28).rowOperations.lookups.map (·.table) = fixedFor target 28 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 29. -/
private theorem lookup_slot_29 (target : MemorySnapshot) :
    (componentAt target 29).rowOperations.lookups.map (·.table) = fixedFor target 29 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 30. -/
private theorem lookup_slot_30 (target : MemorySnapshot) :
    (componentAt target 30).rowOperations.lookups.map (·.table) = fixedFor target 30 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 31. -/
private theorem lookup_slot_31 (target : MemorySnapshot) :
    (componentAt target 31).rowOperations.lookups.map (·.table) = fixedFor target 31 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 32. -/
private theorem lookup_slot_32 (target : MemorySnapshot) :
    (componentAt target 32).rowOperations.lookups.map (·.table) = fixedFor target 32 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 33. -/
private theorem lookup_slot_33 (target : MemorySnapshot) :
    (componentAt target 33).rowOperations.lookups.map (·.table) = fixedFor target 33 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 34. -/
private theorem lookup_slot_34 (target : MemorySnapshot) :
    (componentAt target 34).rowOperations.lookups.map (·.table) = fixedFor target 34 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 35. -/
private theorem lookup_slot_35 (target : MemorySnapshot) :
    (componentAt target 35).rowOperations.lookups.map (·.table) = fixedFor target 35 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 36. -/
private theorem lookup_slot_36 (target : MemorySnapshot) :
    (componentAt target 36).rowOperations.lookups.map (·.table) = fixedFor target 36 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 37. -/
private theorem lookup_slot_37 (target : MemorySnapshot) :
    (componentAt target 37).rowOperations.lookups.map (·.table) = fixedFor target 37 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 38. -/
private theorem lookup_slot_38 (target : MemorySnapshot) :
    (componentAt target 38).rowOperations.lookups.map (·.table) = fixedFor target 38 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 39. -/
private theorem lookup_slot_39 (target : MemorySnapshot) :
    (componentAt target 39).rowOperations.lookups.map (·.table) = fixedFor target 39 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 40. -/
private theorem lookup_slot_40 (target : MemorySnapshot) :
    (componentAt target 40).rowOperations.lookups.map (·.table) = fixedFor target 40 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 41. -/
private theorem lookup_slot_41 (target : MemorySnapshot) :
    (componentAt target 41).rowOperations.lookups.map (·.table) = fixedFor target 41 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 42. -/
private theorem lookup_slot_42 (target : MemorySnapshot) :
    (componentAt target 42).rowOperations.lookups.map (·.table) = fixedFor target 42 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 43. -/
private theorem lookup_slot_43 (target : MemorySnapshot) :
    (componentAt target 43).rowOperations.lookups.map (·.table) = fixedFor target 43 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 44. -/
private theorem lookup_slot_44 (target : MemorySnapshot) :
    (componentAt target 44).rowOperations.lookups.map (·.table) = fixedFor target 44 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 45. -/
private theorem lookup_slot_45 (target : MemorySnapshot) :
    (componentAt target 45).rowOperations.lookups.map (·.table) = fixedFor target 45 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 46. -/
private theorem lookup_slot_46 (target : MemorySnapshot) :
    (componentAt target 46).rowOperations.lookups.map (·.table) = fixedFor target 46 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 47. -/
private theorem lookup_slot_47 (target : MemorySnapshot) :
    (componentAt target 47).rowOperations.lookups.map (·.table) = fixedFor target 47 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 48. -/
private theorem lookup_slot_48 (target : MemorySnapshot) :
    (componentAt target 48).rowOperations.lookups.map (·.table) = fixedFor target 48 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 49. -/
private theorem lookup_slot_49 (target : MemorySnapshot) :
    (componentAt target 49).rowOperations.lookups.map (·.table) = fixedFor target 49 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 50. -/
private theorem lookup_slot_50 (target : MemorySnapshot) :
    (componentAt target 50).rowOperations.lookups.map (·.table) = fixedFor target 50 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 51. -/
private theorem lookup_slot_51 (target : MemorySnapshot) :
    (componentAt target 51).rowOperations.lookups.map (·.table) = fixedFor target 51 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 52. -/
private theorem lookup_slot_52 (target : MemorySnapshot) :
    (componentAt target 52).rowOperations.lookups.map (·.table) = fixedFor target 52 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 53. -/
private theorem lookup_slot_53 (target : MemorySnapshot) :
    (componentAt target 53).rowOperations.lookups.map (·.table) = fixedFor target 53 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 54. -/
private theorem lookup_slot_54 (target : MemorySnapshot) :
    (componentAt target 54).rowOperations.lookups.map (·.table) = fixedFor target 54 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 55. -/
private theorem lookup_slot_55 (target : MemorySnapshot) :
    (componentAt target 55).rowOperations.lookups.map (·.table) = fixedFor target 55 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 56. -/
private theorem lookup_slot_56 (target : MemorySnapshot) :
    (componentAt target 56).rowOperations.lookups.map (·.table) = fixedFor target 56 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 57. -/
private theorem lookup_slot_57 (target : MemorySnapshot) :
    (componentAt target 57).rowOperations.lookups.map (·.table) = fixedFor target 57 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 58. -/
private theorem lookup_slot_58 (target : MemorySnapshot) :
    (componentAt target 58).rowOperations.lookups.map (·.table) = fixedFor target 58 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, Circuit.foldlRange.operations_eq, List.ofFn_succ]

/-- The verifier-fixed membership provider has no legacy lookups. -/
private theorem lookup_slot_59 (target : MemorySnapshot) :
    (componentAt target 59).rowOperations.lookups.map (·.table) = fixedFor target 59 := by
  rfl

/-- Raw lookup identities at physical component 61. -/
private theorem lookup_slot_61 (target : MemorySnapshot) :
    (componentAt target 61).rowOperations.lookups.map (·.table) = fixedFor target 61 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 62. -/
private theorem lookup_slot_62 (target : MemorySnapshot) :
    (componentAt target 62).rowOperations.lookups.map (·.table) = fixedFor target 62 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 63. -/
private theorem lookup_slot_63 (target : MemorySnapshot) :
    (componentAt target 63).rowOperations.lookups.map (·.table) = fixedFor target 63 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 64. -/
private theorem lookup_slot_64 (target : MemorySnapshot) :
    (componentAt target 64).rowOperations.lookups.map (·.table) = fixedFor target 64 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 65. -/
private theorem lookup_slot_65 (target : MemorySnapshot) :
    (componentAt target 65).rowOperations.lookups.map (·.table) = fixedFor target 65 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 66. -/
private theorem lookup_slot_66 (target : MemorySnapshot) :
    (componentAt target 66).rowOperations.lookups.map (·.table) = fixedFor target 66 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 67. -/
private theorem lookup_slot_67 (target : MemorySnapshot) :
    (componentAt target 67).rowOperations.lookups.map (·.table) = fixedFor target 67 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 68. -/
private theorem lookup_slot_68 (target : MemorySnapshot) :
    (componentAt target 68).rowOperations.lookups.map (·.table) = fixedFor target 68 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 69. -/
private theorem lookup_slot_69 (target : MemorySnapshot) :
    (componentAt target 69).rowOperations.lookups.map (·.table) = fixedFor target 69 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 70. -/
private theorem lookup_slot_70 (target : MemorySnapshot) :
    (componentAt target 70).rowOperations.lookups.map (·.table) = fixedFor target 70 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 71. -/
private theorem lookup_slot_71 (target : MemorySnapshot) :
    (componentAt target 71).rowOperations.lookups.map (·.table) = fixedFor target 71 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 72. -/
private theorem lookup_slot_72 (target : MemorySnapshot) :
    (componentAt target 72).rowOperations.lookups.map (·.table) = fixedFor target 72 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 73. -/
private theorem lookup_slot_73 (target : MemorySnapshot) :
    (componentAt target 73).rowOperations.lookups.map (·.table) = fixedFor target 73 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 74. -/
private theorem lookup_slot_74 (target : MemorySnapshot) :
    (componentAt target 74).rowOperations.lookups.map (·.table) = fixedFor target 74 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 75. -/
private theorem lookup_slot_75 (target : MemorySnapshot) :
    (componentAt target 75).rowOperations.lookups.map (·.table) = fixedFor target 75 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 76. -/
private theorem lookup_slot_76 (target : MemorySnapshot) :
    (componentAt target 76).rowOperations.lookups.map (·.table) = fixedFor target 76 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 77. -/
private theorem lookup_slot_77 (target : MemorySnapshot) :
    (componentAt target 77).rowOperations.lookups.map (·.table) = fixedFor target 77 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 78. -/
private theorem lookup_slot_78 (target : MemorySnapshot) :
    (componentAt target 78).rowOperations.lookups.map (·.table) = fixedFor target 78 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 79. -/
private theorem lookup_slot_79 (target : MemorySnapshot) :
    (componentAt target 79).rowOperations.lookups.map (·.table) = fixedFor target 79 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 80. -/
private theorem lookup_slot_80 (target : MemorySnapshot) :
    (componentAt target 80).rowOperations.lookups.map (·.table) = fixedFor target 80 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 81. -/
private theorem lookup_slot_81 (target : MemorySnapshot) :
    (componentAt target 81).rowOperations.lookups.map (·.table) = fixedFor target 81 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 82. -/
private theorem lookup_slot_82 (target : MemorySnapshot) :
    (componentAt target 82).rowOperations.lookups.map (·.table) = fixedFor target 82 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 83. -/
private theorem lookup_slot_83 (target : MemorySnapshot) :
    (componentAt target 83).rowOperations.lookups.map (·.table) = fixedFor target 83 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 84. -/
private theorem lookup_slot_84 (target : MemorySnapshot) :
    (componentAt target 84).rowOperations.lookups.map (·.table) = fixedFor target 84 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 85. -/
private theorem lookup_slot_85 (target : MemorySnapshot) :
    (componentAt target 85).rowOperations.lookups.map (·.table) = fixedFor target 85 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 86. -/
private theorem lookup_slot_86 (target : MemorySnapshot) :
    (componentAt target 86).rowOperations.lookups.map (·.table) = fixedFor target 86 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 87. -/
private theorem lookup_slot_87 (target : MemorySnapshot) :
    (componentAt target 87).rowOperations.lookups.map (·.table) = fixedFor target 87 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 88. -/
private theorem lookup_slot_88 (target : MemorySnapshot) :
    (componentAt target 88).rowOperations.lookups.map (·.table) = fixedFor target 88 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 89. -/
private theorem lookup_slot_89 (target : MemorySnapshot) :
    (componentAt target 89).rowOperations.lookups.map (·.table) = fixedFor target 89 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- Raw lookup identities at physical component 90. -/
private theorem lookup_slot_90 (target : MemorySnapshot) :
    (componentAt target 90).rowOperations.lookups.map (·.table) = fixedFor target 90 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm]

/-- The fixed target provider has no legacy lookup. -/
private theorem lookup_slot_91 (target : MemorySnapshot) :
    (componentAt target 91).rowOperations.lookups.map (·.table) = fixedFor target 91 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- The fixed RAM provider has no legacy lookup. -/
private theorem lookup_slot_60 (target : MemorySnapshot) :
    (componentAt target 60).rowOperations.lookups.map (·.table) = fixedFor target 60 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- The fixed RAM provider has no legacy lookup. -/
private theorem lookup_slot_92 (target : MemorySnapshot) :
    (componentAt target 92).rowOperations.lookups.map (·.table) = fixedFor target 92 := by
  conv_lhs => arg 2; arg 1; arg 1; whnf
  simp [circuit_norm, StaticTable.provider]

/-- Each installed component has exactly its listed fixed-table predicates. -/
theorem lookup_slot (target : MemorySnapshot) (index : Fin 93) :
    (componentAt target index).rowOperations.lookups.map (·.table) = fixedFor target index := by
  fin_cases index
  · exact lookup_slot_0 target
  · exact lookup_slot_1 target
  · exact lookup_slot_2 target
  · exact lookup_slot_3 target
  · exact lookup_slot_4 target
  · exact lookup_slot_5 target
  · exact lookup_slot_6 target
  · exact lookup_slot_7 target
  · exact lookup_slot_8 target
  · exact lookup_slot_9 target
  · exact lookup_slot_10 target
  · exact lookup_slot_11 target
  · exact lookup_slot_12 target
  · exact lookup_slot_13 target
  · exact lookup_slot_14 target
  · exact lookup_slot_15 target
  · exact lookup_slot_16 target
  · exact lookup_slot_17 target
  · exact lookup_slot_18 target
  · exact lookup_slot_19 target
  · exact lookup_slot_20 target
  · exact lookup_slot_21 target
  · exact lookup_slot_22 target
  · exact lookup_slot_23 target
  · exact lookup_slot_24 target
  · exact lookup_slot_25 target
  · exact lookup_slot_26 target
  · exact lookup_slot_27 target
  · exact lookup_slot_28 target
  · exact lookup_slot_29 target
  · exact lookup_slot_30 target
  · exact lookup_slot_31 target
  · exact lookup_slot_32 target
  · exact lookup_slot_33 target
  · exact lookup_slot_34 target
  · exact lookup_slot_35 target
  · exact lookup_slot_36 target
  · exact lookup_slot_37 target
  · exact lookup_slot_38 target
  · exact lookup_slot_39 target
  · exact lookup_slot_40 target
  · exact lookup_slot_41 target
  · exact lookup_slot_42 target
  · exact lookup_slot_43 target
  · exact lookup_slot_44 target
  · exact lookup_slot_45 target
  · exact lookup_slot_46 target
  · exact lookup_slot_47 target
  · exact lookup_slot_48 target
  · exact lookup_slot_49 target
  · exact lookup_slot_50 target
  · exact lookup_slot_51 target
  · exact lookup_slot_52 target
  · exact lookup_slot_53 target
  · exact lookup_slot_54 target
  · exact lookup_slot_55 target
  · exact lookup_slot_56 target
  · exact lookup_slot_57 target
  · exact lookup_slot_58 target
  · exact lookup_slot_59 target
  · exact lookup_slot_60 target
  · exact lookup_slot_61 target
  · exact lookup_slot_62 target
  · exact lookup_slot_63 target
  · exact lookup_slot_64 target
  · exact lookup_slot_65 target
  · exact lookup_slot_66 target
  · exact lookup_slot_67 target
  · exact lookup_slot_68 target
  · exact lookup_slot_69 target
  · exact lookup_slot_70 target
  · exact lookup_slot_71 target
  · exact lookup_slot_72 target
  · exact lookup_slot_73 target
  · exact lookup_slot_74 target
  · exact lookup_slot_75 target
  · exact lookup_slot_76 target
  · exact lookup_slot_77 target
  · exact lookup_slot_78 target
  · exact lookup_slot_79 target
  · exact lookup_slot_80 target
  · exact lookup_slot_81 target
  · exact lookup_slot_82 target
  · exact lookup_slot_83 target
  · exact lookup_slot_84 target
  · exact lookup_slot_85 target
  · exact lookup_slot_86 target
  · exact lookup_slot_87 target
  · exact lookup_slot_88 target
  · exact lookup_slot_89 target
  · exact lookup_slot_90 target
  · exact lookup_slot_91 target
  · exact lookup_slot_92 target

/-- Actual lookup predicates, not just names, agree with the finite realization inventory. -/
theorem component_lookups (target : MemorySnapshot) :
    (assembly target).tables.map (fun component => component.rowOperations.lookups.map (·.table)) =
      componentLookupIndices.map (fun indices => indices.map fun index =>
        ((fixed target)[index.val]'(by change index.val < 5; exact index.isLt)).table) := by
  apply List.ext_getElem
  · simp only [List.length_map]
    rfl
  intro index bound otherBound
  simp only [List.getElem_map]
  have indexBound := otherBound
  change index < 93 at indexBound
  exact lookup_slot target ⟨index, indexBound⟩

/-- Every installed static lookup has an authenticated finite realization by table identity. -/
theorem lookups_complete (target : MemorySnapshot) (component : Component Fp)
    (member : component ∈ (assembly target).tables) (lookup : Lookup Fp)
    (used : lookup ∈ component.operations.lookups) :
    ∃ fixedTable ∈ fixed target, fixedTable.table = lookup.table := by
  rw [Component.lookups_eq] at used
  have present := List.mem_map_of_mem
    (f := fun component : Component Fp => component.rowOperations.lookups.map (·.table)) member
  rw [component_lookups] at present
  obtain ⟨indices, _, equal⟩ := List.mem_map.mp present
  have lookupPresent := List.mem_map_of_mem (f := fun lookup : Lookup Fp => lookup.table) used
  rw [← equal] at lookupPresent
  obtain ⟨index, _, tableEqual⟩ := List.mem_map.mp lookupPresent
  exact ⟨(fixed target)[index.val], List.getElem_mem _, tableEqual⟩


end SP1Clean.Audit.BranchEnsemble
