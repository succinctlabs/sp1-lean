import SP1Clean.Model.Core.ResourceUsage
import SP1Clean.Model.Core.ExecutionEncoding
import SP1Clean.Model.Core.MemorySupport

/-! # Resource edges independent of witness construction -/

namespace SP1CleanTest.Core.ResourceUsage
open SP1Clean.Model.Core LeanRV64D.Defs

private def memory : ByteMemory := ⟨[(32, 7), (32, 9), (33, 0), (64, 8)]⟩

/-- Shadowed writes, explicit zero bytes and excluded keys contribute no canonical payload. -/
theorem canonicalMemory : memory.supportBelow 64 = {32} := by decide +kernel

private def context : HostReadContext := ⟨fun index => if index = 12 then some 17 else some 0,
  fun _ => some 0⟩
private def verify : HostExecution := ⟨.verifyProof, 70000, 70000, 0, ⟨{}, none⟩⟩
private def write : HostExecution := ⟨.write, 1, 70000, 2, ⟨{}, none⟩⟩
private def readHint : HostExecution :=
  ⟨.hintRead, 70000, 8, 241, ⟨{}, some ⟨70000, hintWriteBytes [1, 2, 3, 4, 5, 6, 7, 8]⟩⟩⟩

/-- VERIFY counts both overlapping logical buffers; WRITE observes x12; aligned hints still pad. -/
theorem hostDemand : verify.readByteCount context = 64 ∧
    write.readByteCount context = 17 ∧ readHint.writeByteCount = 16 := by decide +kernel

private def oldHost : HostState := { io.hints := [[7]] }
private def hook : HostExecution :=
  ⟨.write, 15, 70000, 2, ⟨{ oldHost with io.hints := [[], [1, 2], [7]] }, none⟩⟩

/-- Empty fresh hints allocate nodes; allocation is not the final queue length. -/
theorem hookAllocation : oldHost.executionResources context hook .allocatedHints = 2 ∧
    hook.effect.state.io.hints.length = 3 := by decide +kernel

/-- The generic scheduler admits non-phase-one windows; native CPU rows additionally require phase one. -/
theorem windows : activeClockWindow 0 ∧ activeClockWindow 2 ∧
    activeClockWindow (2 ^ 24 - 5) ∧ ¬ activeClockWindow (2 ^ 24 - 4) := by
  unfold activeClockWindow
  decide +kernel

/-- A normally representable native doubleword access is stricter than Sail's misaligned access. -/
theorem memoryAlignment :
    instructionMemoryEncoded (fun _ => some 70000) (.STORE (0, .Regidx 0, .Regidx 1, 8)) ∧
    ¬ instructionMemoryEncoded (fun _ => some 70001) (.STORE (0, .Regidx 0, .Regidx 1, 8)) := by
  constructor
  · exact ⟨70000, rfl, by decide, by decide⟩
  · rintro ⟨base, observed, _, aligned⟩
    cases Option.some.inj observed
    exact (by decide : ¬ (70001 : ℕ) % 8 = 0) aligned

/-- Both LOAD signedness choices still require the decoded width's alignment. -/
theorem loadAlignment (signed : Bool) :
    ¬ instructionMemoryEncoded (fun _ => some 70001) (.LOAD (0, .Regidx 1, .Regidx 0, signed, 8)) := by
  rintro ⟨base, observed, _, aligned⟩
  cases Option.some.inj observed
  exact (by decide : ¬ (70001 : ℕ) % 8 = 0) aligned

end SP1CleanTest.Core.ResourceUsage
