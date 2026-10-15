import SP1Clean.Model.Semantics.SailArithmeticFrame
import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Proofs.Sail.InstructionDecode

/-! # Arithmetic retirement without a circuit witness

The source contains one committed instruction and no successor instruction. These semantic
fixtures exercise discarded x0 writes, signed division by zero and overflow, and word arithmetic.
Normal retirement, configuration, and the complete byte-map frame come from the core theorem;
native evaluation only checks finite source data; parsing reduces in the kernel.
-/

namespace SP1CleanTest.Core.ArithmeticFrame

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D.Defs

private def image (word : BitVec 32) : ProgramImage := ⟨[(65536, word)], 65536, []⟩

private def source (word : BitVec 32) (left right : BitVec 64) : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x2 left).insert .x3 right
            memory := (image word).initialMemory }
  host := {}
  clock := 17

private def RetiresWithFrame (word : BitVec 32) (left right : BitVec 64) : Prop :=
  ∃ target, SailRetiresNormally (source word left right).sail.realize target ∧
    SailConfigured target ∧ target.mem = (source word left right).sail.realize.mem

private theorem retires (word : BitVec 32) (left right : BitVec 64) (decoded : instruction)
    (checked : checkExecutionSource (image word) (source word left right) = true)
    (parsed : InstructionDecode.decode word = some decoded)
    (arithmetic : Advance.ArithmeticInstruction decoded) : RetiresWithFrame word left right := by
  have valid := (checkExecutionSource_iff _ _).mp checked
  apply Advance.arithmetic_retire valid.configured valid.romLoaded valid.pc
    (decode := SailDecode.instructionDecode_agrees word decoded parsed) (arithmetic := arithmetic)
  have pc : (source word left right).pc = 65536 := by
    simp only [ExecutionSnapshot.pc, source, configuredState, Std.ExtDHashMap.get?_insert,
      beq_iff_eq, reduceCtorEq, ↓reduceDIte, Option.getD_some, cast_eq]
  have fetched : ((image word).toGuestProgram valid.1.1).fetchWord 65536 = some word := rfl
  simpa only [pc] using fetched

/-- A discarded ADD to x0 still retires normally, preserving the complete code/data map. -/
theorem addToZero : RetiresWithFrame 0x00310033 (BitVec.allOnes 64) 1 :=
  retires _ _ _ (.RTYPE (.Regidx 3, .Regidx 2, .Regidx 0, .ADD))
    (by native_decide) rfl trivial

/-- Signed division by zero is a retiring arithmetic instruction, not a trap. -/
theorem divideByZero : RetiresWithFrame 0x023140b3 (BitVec.allOnes 64) 0 :=
  retires _ _ _ (.DIV (.Regidx 3, .Regidx 2, .Regidx 1, false))
    (by native_decide) rfl trivial

/-- Signed division overflow also retains the configured platform and every memory byte. -/
theorem divideOverflow : RetiresWithFrame 0x023140b3 0x8000000000000000 (BitVec.allOnes 64) :=
  retires _ _ _ (.DIV (.Regidx 3, .Regidx 2, .Regidx 1, false))
    (by native_decide) rfl trivial

/-- Word arithmetic may cross the sign bit while the full memory frame remains exact. -/
theorem addWordSign : RetiresWithFrame 0x0011009b 0x7fffffff 0 :=
  retires _ _ _ (.ADDIW (1, .Regidx 2, .Regidx 1))
    (by native_decide) rfl trivial

end SP1CleanTest.Core.ArithmeticFrame
