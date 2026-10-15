import SP1Clean.FormalModel.Shard
import SP1Clean.Model.Core.Boot

/-! # The native shard contract requires actual ordinary write permission

The source is valid, and SW would write exactly the instruction word already present in ROM.
Every nonempty execution beginning with that ordinary event is rejected by the native contract,
even under an unrestricted resource profile. Empty identities remain admissible.
-/

namespace SP1CleanTest.Core.ExecutionWritePolicy

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D.Defs

private def image : ProgramImage := ⟨[(65536, 0x00112023)], 65536, []⟩

private def source : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x1 0x00112023).insert .x2 65536
            memory := image.initialMemory }
  host := {}
  clock := 17

private theorem source_valid : ExecutionSourceValid image source := by
  apply (checkExecutionSource_iff image source).mp
  native_decide

private theorem decode_store : ConfiguredDecode 0x00112023 (.STORE (0, .Regidx 1, .Regidx 2, 4)) := by
  intro state configured
  exact SailDecode.decode_SW state configured.init configured.priv configured.mseccfg_disabled

private theorem permitted_of_registers {left right : SailState} (program : GuestProgram)
    (readOnly : ℕ → Bool) (equal : left.regs = right.regs)
    (permitted : InstructionWrite.PermittedAt readOnly program left) :
    InstructionWrite.PermittedAt readOnly program right := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, checked⟩ := permitted
  have registers : left.get_reg? = right.get_reg? := by
    funext index
    simp only [SailState.get_reg?, equal]
  refine ⟨pc, word, decoded, ?_, fetched, decode, ?_⟩
  · rw [← equal]
    exact atPc
  · rw [← registers]
    exact checked

private theorem denied_skeleton : ¬ InstructionWrite.PermittedAt image.readOnly
    (image.toGuestProgram source_valid.1.1) source.sail.skeleton := by
  intro permitted
  have atPc : source.sail.skeleton.regs.get? .PC = some (65536 : BitVec 64) := by native_decide
  have fetched : (image.toGuestProgram source_valid.1.1).fetchWord 65536 = some 0x00112023 := by
    native_decide
  have rejected : InstructionWrite.check image.readOnly source.sail.skeleton.get_reg?
      (.STORE (0, .Regidx 1, .Regidx 2, 4)) = false := by native_decide
  have checked := permitted.check source_valid.2.1 atPc fetched decode_store
  exact Bool.false_ne_true (rejected.symm.trans checked)

private theorem denied : ¬ InstructionWrite.PermittedAt image.readOnly
    (image.toGuestProgram source_valid.1.1) source.sail.realize :=
  -- Name both carriers so inference does not compare the full policy by unfolding dense memory.
  fun permitted => denied_skeleton (permitted_of_registers
    (left := source.sail.realize) (right := source.sail.skeleton) _ _ rfl permitted)

/-- The protected store's register contains exactly the code word already in its target cell. -/
theorem sameValueStoreSource : ExecutionSourceValid image source ∧
    source.sail.registers.get? .x1 = some 0x00112023 ∧
    source.sail.memory.readWord 65536 = 0x00112023 := by
  exact ⟨source_valid, by native_decide, by native_decide⟩

/-- No chosen endpoint or continuation can excuse the first forbidden ordinary write. -/
theorem rejectsSameValueStore (characteristic : ℕ) (target : ExecutionSnapshot)
    (events : List Machine.ExecutionEvent) :
    ¬ FormalModel.Shard.Executes characteristic image source target (.ordinary :: events) := by
  rintro ⟨_, _, permitted⟩
  exact denied permitted.head

/-- No choice of numeric ceilings can remove the contract's fixed write policy. -/
theorem rejectsProfileBypass (limits : ResourceLimits) (characteristic : ℕ) (target : ExecutionSnapshot)
    (events : List Machine.ExecutionEvent) :
    ¬ FormalModel.Shard.AdmissibleExecution limits
      characteristic image source target (.ordinary :: events) :=
  fun execution => rejectsSameValueStore characteristic target events execution.1

/-- An empty local identity does not execute the forbidden instruction at its source PC. -/
theorem acceptsIdentity (characteristic : ℕ) :
    FormalModel.Shard.Executes characteristic image source source [] :=
  FormalModel.Shard.Executes.nil_iff.mpr ⟨source_valid, (ExecutionSnapshot.equivalent_iff _ _).mpr rfl⟩

end SP1CleanTest.Core.ExecutionWritePolicy
