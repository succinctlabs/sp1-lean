import SP1Clean.Proofs.Completeness.Assembly
import ToClean.Air.Footprint
import SP1Clean.Model.Core.ResourceLimits

/-! # Exact construction costs of the retained native compiler

The existing semantic event buckets and provider occurrence lists determine every physical height.
The Halt table has its required padding row; SyscallInstrs is empty only in this legacy ordinary
constructor. Actual circuit interaction widths then give an exact cost for every channel. This
equivalence replaces hand-picked channel counts, without promoting a sufficient estimate to an
acceptance condition. The mixed A4/A5/A6 construction must supply its own full inventory.
-/

namespace SP1Clean.Soundness.SupportedCoreTraceWitness
open Air.Flat TraceGen Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
variable (trace : SupportedCoreTraceWitness p)

/-- Every instruction bucket builds exactly one row per event, with no hidden padding. -/
theorem instructionTableFor_length (id : InstructionChipId) :
    (trace.instructionTableFor id).length = (trace.instructionEvents id).length := by
  cases id with
  | add =>
    exact (Table.build_length AddChip.component
      (AddChip.traceInputs (trace.instructionEvents .add) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (AddChip.traceInputs (trace.instructionEvents .add) 0).length = _
      simp only [AddChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | addi =>
    exact (Table.build_length AddiChip.component
      (AddiChip.traceInputs (trace.instructionEvents .addi) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (AddiChip.traceInputs (trace.instructionEvents .addi) 0).length = _
      simp only [AddiChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | addw =>
    exact (Table.build_length AddwChip.component
      (AddwChip.traceInputs (trace.instructionEvents .addw) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (AddwChip.traceInputs (trace.instructionEvents .addw) 0).length = _
      simp only [AddwChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | sub =>
    exact (Table.build_length SubChip.component
      (SubChip.traceInputs (trace.instructionEvents .sub) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (SubChip.traceInputs (trace.instructionEvents .sub) 0).length = _
      simp only [SubChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | subw =>
    exact (Table.build_length SubwChip.component
      (SubwChip.traceInputs (trace.instructionEvents .subw) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (SubwChip.traceInputs (trace.instructionEvents .subw) 0).length = _
      simp only [SubwChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | bitwise =>
    exact (Table.build_length BitwiseChip.component
      (BitwiseChip.traceInputs (trace.instructionEvents .bitwise) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (BitwiseChip.traceInputs (trace.instructionEvents .bitwise) 0).length = _
      simp only [BitwiseChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | lt =>
    exact (Table.build_length LtChip.component
      (LtChip.traceInputs (trace.instructionEvents .lt) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (LtChip.traceInputs (trace.instructionEvents .lt) 0).length = _
      simp only [LtChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | shiftLeft =>
    exact (Table.build_length ShiftLeftChip.component
      (ShiftLeftChip.traceInputs (trace.instructionEvents .shiftLeft) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (ShiftLeftChip.traceInputs (trace.instructionEvents .shiftLeft) 0).length = _
      simp only [ShiftLeftChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | shiftRight =>
    exact (Table.build_length ShiftRightChip.component
      (ShiftRightChip.traceInputs (trace.instructionEvents .shiftRight) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (ShiftRightChip.traceInputs (trace.instructionEvents .shiftRight) 0).length = _
      simp only [ShiftRightChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | jal =>
    exact (Table.build_length JalChip.component
      (JalChip.traceInputs (trace.instructionEvents .jal) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (JalChip.traceInputs (trace.instructionEvents .jal) 0).length = _
      simp only [JalChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | jalr =>
    exact (Table.build_length JalrChip.component
      (JalrChip.traceInputs (trace.instructionEvents .jalr) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (JalrChip.traceInputs (trace.instructionEvents .jalr) 0).length = _
      simp only [JalrChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | branch =>
    exact (Table.build_length BranchChip.component
      (BranchChip.traceInputs (trace.instructionEvents .branch) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (BranchChip.traceInputs (trace.instructionEvents .branch) 0).length = _
      simp only [BranchChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | uType =>
    exact (Table.build_length UTypeChip.component
      (UTypeChip.traceInputs (trace.instructionEvents .uType) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (UTypeChip.traceInputs (trace.instructionEvents .uType) 0).length = _
      simp only [UTypeChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | loadByte =>
    exact (Table.build_length LoadByteChip.component
      (LoadByteChip.traceInputs (trace.instructionEvents .loadByte))
      trace.generationData trace.hint (by trivial)).trans (by
      change (LoadByteChip.traceInputs (trace.instructionEvents .loadByte)).length = _
      simp only [LoadByteChip.traceInputs]
      exact List.length_map ..)
  | loadHalf =>
    exact (Table.build_length LoadHalfChip.component
      (LoadHalfChip.traceInputs (trace.instructionEvents .loadHalf))
      trace.generationData trace.hint (by trivial)).trans (by
      change (LoadHalfChip.traceInputs (trace.instructionEvents .loadHalf)).length = _
      simp only [LoadHalfChip.traceInputs]
      exact List.length_map ..)
  | loadWord =>
    exact (Table.build_length LoadWordChip.component
      (LoadWordChip.traceInputs (trace.instructionEvents .loadWord))
      trace.generationData trace.hint (by trivial)).trans (by
      change (LoadWordChip.traceInputs (trace.instructionEvents .loadWord)).length = _
      simp only [LoadWordChip.traceInputs]
      exact List.length_map ..)
  | loadDouble =>
    exact (Table.build_length LoadDoubleChip.component
      (LoadDoubleChip.traceInputs (trace.instructionEvents .loadDouble))
      trace.generationData trace.hint (by trivial)).trans (by
      change (LoadDoubleChip.traceInputs (trace.instructionEvents .loadDouble)).length = _
      simp only [LoadDoubleChip.traceInputs]
      exact List.length_map ..)
  | loadX0 =>
    exact (Table.build_length LoadX0Chip.component
      (LoadX0Chip.traceInputs (trace.instructionEvents .loadX0))
      trace.generationData trace.hint (by trivial)).trans (by
      change (LoadX0Chip.traceInputs (trace.instructionEvents .loadX0)).length = _
      simp only [LoadX0Chip.traceInputs]
      exact List.length_map ..)
  | storeByte =>
    exact (Table.build_length StoreByteChip.component
      (StoreByteChip.traceInputs (trace.instructionEvents .storeByte))
      trace.generationData trace.hint (by trivial)).trans (by
      change (StoreByteChip.traceInputs (trace.instructionEvents .storeByte)).length = _
      simp only [StoreByteChip.traceInputs]
      exact List.length_map ..)
  | storeHalf =>
    exact (Table.build_length StoreHalfChip.component
      (StoreHalfChip.traceInputs (trace.instructionEvents .storeHalf))
      trace.generationData trace.hint (by trivial)).trans (by
      change (StoreHalfChip.traceInputs (trace.instructionEvents .storeHalf)).length = _
      simp only [StoreHalfChip.traceInputs]
      exact List.length_map ..)
  | storeWord =>
    exact (Table.build_length StoreWordChip.component
      (StoreWordChip.traceInputs (trace.instructionEvents .storeWord))
      trace.generationData trace.hint (by trivial)).trans (by
      change (StoreWordChip.traceInputs (trace.instructionEvents .storeWord)).length = _
      simp only [StoreWordChip.traceInputs]
      exact List.length_map ..)
  | storeDouble =>
    exact (Table.build_length StoreDoubleChip.component
      (StoreDoubleChip.traceInputs (trace.instructionEvents .storeDouble))
      trace.generationData trace.hint (by trivial)).trans (by
      change (StoreDoubleChip.traceInputs (trace.instructionEvents .storeDouble)).length = _
      simp only [StoreDoubleChip.traceInputs]
      exact List.length_map ..)
  | mul =>
    exact (Table.build_length MulChip.component
      (MulChip.traceInputs (trace.instructionEvents .mul) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (MulChip.traceInputs (trace.instructionEvents .mul) 0).length = _
      simp only [MulChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | divRem =>
    exact (Table.build_length DivRemChip.component
      (DivRemChip.traceInputs (trace.instructionEvents .divRem) 0)
      trace.generationData (ProverHint.empty _) (by trivial)).trans (by
      change (DivRemChip.traceInputs (trace.instructionEvents .divRem) 0).length = _
      simp only [DivRemChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)
  | aluX0 =>
    exact (Table.build_length AluX0Chip.component
      (AluX0Chip.traceInputs (trace.instructionEvents .aluX0) 0)
      trace.generationData trace.hint (by trivial)).trans (by
      change (AluX0Chip.traceInputs (trace.instructionEvents .aluX0) 0).length = _
      simp only [AluX0Chip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..)

/-- Provider height includes the ordinary compiler's one Halt padding row and empty syscall table. -/
def providerHeight (id : ProviderTableId) : ℕ :=
  match id with
  | .halt => 1
  | .syscallInstrs => 0
  | _ => (trace.providerOccurrences id).length

/-- Provider demand, including all refresh/boundary occurrences, gives the exact built height. -/
theorem providerTableFor_length (id : ProviderTableId) :
    (trace.providerTableFor id).length = trace.providerHeight id := by
  cases id with
  | byte provider =>
    cases provider with
      | u8Range =>
        exact (Table.build_length ByteChip.U8Range.component
          (ByteChip.U8Range.traceInputs (trace.providerOccurrences (.byte .u8Range)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.U8Range.traceInputs (trace.providerOccurrences (.byte .u8Range))).length = _
          simp only [providerHeight, ByteChip.U8Range.traceInputs]
          exact List.length_map ..)
      | msb =>
        exact (Table.build_length ByteChip.MSB.component
          (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb))).length = _
          simp only [providerHeight, ByteChip.MSB.traceInputs]
          exact List.length_map ..)
      | andByte =>
        exact (Table.build_length ByteChip.AndByte.component
          (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte))).length = _
          simp only [providerHeight, ByteChip.AndByte.traceInputs]
          exact List.length_map ..)
      | orByte =>
        exact (Table.build_length ByteChip.OrByte.component
          (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte))).length = _
          simp only [providerHeight, ByteChip.OrByte.traceInputs]
          exact List.length_map ..)
      | xorByte =>
        exact (Table.build_length ByteChip.XorByte.component
          (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte))).length = _
          simp only [providerHeight, ByteChip.XorByte.traceInputs]
          exact List.length_map ..)
      | ltu =>
        exact (Table.build_length ByteChip.Ltu.component
          (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu)))
          trace.generationData trace.hint (by trivial)).trans (by
          change (ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu))).length = _
          simp only [providerHeight, ByteChip.Ltu.traceInputs]
          exact List.length_map ..)
  | range width =>
    exact (Table.build_length (RangeChip.componentFor width)
      (RangeChip.traceInputs (trace.providerOccurrences (.range width)))
      trace.generationData trace.hint (by trivial)).trans (by
      change (RangeChip.traceInputs (trace.providerOccurrences (.range width))).length = _
      simp only [providerHeight, RangeChip.traceInputs]
      exact List.length_map ..)
  | program =>
    exact (Table.build_length ProgramProviderChip.component
      (ProgramProviderChip.traceInputs (trace.providerOccurrences .program))
      trace.generationData trace.hint (by trivial)).trans (by
      change (ProgramProviderChip.traceInputs (trace.providerOccurrences .program)).length = _
      simp only [providerHeight, ProgramProviderChip.traceInputs]
      exact List.length_map ..)
  | memoryInit =>
    exact (Table.build_length MemoryProviderChip.component
      (MemoryProviderChip.traceInputs (trace.providerOccurrences .memoryInit))
      trace.generationData trace.hint (by trivial)).trans (by
      change (MemoryProviderChip.traceInputs (trace.providerOccurrences .memoryInit)).length = _
      simp only [providerHeight, MemoryProviderChip.traceInputs]
      exact List.length_map ..)
  | memoryFinalize =>
    exact (Table.build_length MemoryFinalizeChip.component
      (MemoryFinalizeChip.traceInputs (trace.providerOccurrences .memoryFinalize))
      trace.generationData trace.hint (by trivial)).trans (by
      change (MemoryFinalizeChip.traceInputs (trace.providerOccurrences .memoryFinalize)).length = _
      simp only [providerHeight, MemoryFinalizeChip.traceInputs]
      exact List.length_map ..)
  | memoryBump =>
    exact (Table.build_length MemoryBumpChip.component
      (memoryBumpTraceInputs (trace.providerOccurrences .memoryBump))
      trace.generationData trace.hint (by trivial)).trans (by
      change (memoryBumpTraceInputs (trace.providerOccurrences .memoryBump)).length = _
      simp only [providerHeight, memoryBumpTraceInputs]
      exact List.length_map ..)
  | stateBump =>
    exact (Table.build_length StateBumpChip.component
      (stateBumpTraceInputs (trace.providerOccurrences .stateBump))
      trace.generationData trace.hint (by trivial)).trans (by
      change (stateBumpTraceInputs (trace.providerOccurrences .stateBump)).length = _
      simp only [providerHeight, stateBumpTraceInputs]
      exact List.length_map ..)
  | halt =>
    have empty : trace.providerOccurrences .halt = [] := by
      cases h : trace.providerOccurrences .halt with
      | nil => rfl
      | cons impossible _ => exact impossible.elim
    exact (Table.build_length HaltChip.component
      (HaltChip.haltTraceInputs (trace.providerOccurrences .halt))
      trace.generationData trace.hint (by trivial)).trans (by
      change (HaltChip.haltTraceInputs (trace.providerOccurrences .halt)).length = _
      simp only [providerHeight, HaltChip.haltTraceInputs, empty, List.length_singleton])
  | syscallInstrs =>
    exact (Table.build_length SyscallInstrsChip.component
      (SyscallInstrsChip.syscallInstrsTraceInputs (trace.providerOccurrences .syscallInstrs))
      trace.generationData trace.hint (by trivial)).trans (by
      simp only [providerHeight, SyscallInstrsChip.syscallInstrsTraceInputs, List.length_nil])

/-- Exact physical heights from event/occurrence inputs. The public verifier allocates no table. -/
def physicalHeights : List ℕ :=
  InstructionChipId.all.map (fun id => (trace.instructionEvents id).length) ++
    ProviderTableId.all.map trace.providerHeight

/-- Exact channel demand, including every actual public-verifier interaction and physical row. -/
noncomputable def channelDemand (channel : RawChannel (ZMod p)) : ℕ :=
  ((sp1Ensemble (p := p)).verifierOperations.interactionsWith channel).length +
    (InstructionChipId.all.map fun id =>
      (trace.instructionEvents id).length * (supportedChipFor (p := p) id).table.channelWidth channel).sum +
    (ProviderTableId.all.map fun id =>
      trace.providerHeight id * (Soundness.providerTableFor (p := p) id).channelWidth channel).sum

/-- Constructing row cells leaves the event-derived physical heights unchanged. -/
theorem physicalHeights_eq : trace.physicalHeights = trace.witness.tableHeights := by
  simp only [EnsembleWitness.tableHeights_eq, witness_tables, tables, instructionTables,
    providerTables, List.map_append, List.map_map, Function.comp_def, physicalHeights,
    instructionTableFor_length, providerTableFor_length]

/-- Construction costs are exactly the complete ledger lengths, for every raw channel. -/
theorem channelDemand_eq (channel : RawChannel (ZMod p)) :
    trace.channelDemand channel = trace.witness.channelOccurrences channel := by
  rw [EnsembleWitness.channelOccurrences_eq]
  simp only [witness_tables, tables, instructionTables, providerTables, List.map_append,
    List.map_map, Function.comp_def, List.sum_append, instructionTableFor_length, providerTableFor_length,
    instructionTableFor_component, providerTableFor_component, channelDemand, Nat.add_assoc]

/-- Exact arithmetic admission of the existing constructor: this is an iff, not a conservative bound.
The event/provider lists already include the compiler's canonical provider closure and refreshes. -/
theorem physicalFits_iff (limits : ResourceLimits) :
    trace.witness.PhysicalFits limits.tableRows limits.channelOccurrences ↔
      (∀ height ∈ trace.physicalHeights, height ≤ limits.tableRows) ∧
        ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.channelDemand channel ≤ limits.channelOccurrences := by
  simp only [EnsembleWitness.PhysicalFits, physicalHeights_eq, channelDemand_eq]

/-- The exact construction demand is equivalent to the migrated all-channel capacity boundary. -/
theorem channelCapacity_iff : trace.witness.ChannelCapacity p ↔
    ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.channelDemand channel < p := by
  simp only [EnsembleWitness.ChannelCapacity, channelDemand_eq]

end SP1Clean.Soundness.SupportedCoreTraceWitness
