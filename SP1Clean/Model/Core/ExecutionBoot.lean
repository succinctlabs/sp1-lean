import SP1Clean.Model.Core.ExecutionPath
import SP1Clean.Model.Core.Boot

/-! # Boot and HALT as endpoint conditions on local paths

The boot constructor supplies the checked image's complete initial Sail state and the finite host
inputs, with empty outputs/requests and zero commitment banks. It is one possible local boundary.
Joining local segments and then fixing these endpoints gives the boot-to-HALT corollary without
changing the transition relation. These are semantic composition theorems; authenticating the
boundaries of separate AIR witnesses remains an obligation of the native capstone.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Machine SP1Clean.Soundness.Target

/-- The finite external inputs fixed at boot. Later shard boundaries carry their remaining state. -/
structure HostInputs where
  hints : List Bytes := []
  replies : List HookReply := []
deriving DecidableEq, Repr

def HostInputs.initialHost (input : HostInputs) : HostState :=
  { io.hints := input.hints, replies := input.replies }

/-- Native boot is a particular complete local boundary, not a condition on every shard. -/
noncomputable def ProgramImage.executionBoot (image : ProgramImage) (input : HostInputs) :
    ExecutionState :=
  ⟨image.initialSailState, input.initialHost, 1⟩

theorem ProgramImage.executionBoot_loaded (image : ProgramImage) (valid : image.Valid)
    (input : HostInputs) :
    IsInitialState (image.toGuestProgram valid) (image.executionBoot input).sail :=
  image.initialSailState_loaded valid

@[simp] theorem ProgramImage.executionBoot_running (image : ProgramImage) (input : HostInputs) :
    (image.executionBoot input).host.exitCode = none := rfl

/-- A boot-to-HALT run is a local segment with the two distinguished endpoint conditions. -/
def BootToHalt (policy : HostPolicy) (image : ProgramImage) (valid : image.Valid)
    (input : HostInputs) (steps : ℕ) (target : ExecutionState) (exit : BitVec 32) : Prop :=
  ExecutionSegment policy (image.toGuestProgram valid) (image.executionBoot input) steps target ∧
    target.host.exitCode = some exit

/-- Shard composition gives boot-to-HALT by selecting endpoints; no shard-local boot premise is
introduced for the continuation. The combined run need not fit inside a single shard. -/
theorem BootToHalt.of_segments {policy : HostPolicy} {image : ProgramImage} {valid : image.Valid}
    {input : HostInputs} {m n : ℕ} {middle target : ExecutionState} {exit : BitVec 32}
    (first : ExecutionSegment policy (image.toGuestProgram valid) (image.executionBoot input) m middle)
    (last : ExecutionSegment policy (image.toGuestProgram valid) middle n target)
    (halted : target.host.exitCode = some exit) :
    BootToHalt policy image valid input (m + n) target exit :=
  ⟨first.append last, halted⟩

/-- A boot-to-HALT run always contains a real final ECALL observing the exit in the Sail registers. -/
theorem BootToHalt.halt_witness {policy : HostPolicy} {image : ProgramImage} {valid : image.Valid}
    {input : HostInputs} {steps : ℕ} {target : ExecutionState} {exit : BitVec 32}
    (run : BootToHalt policy image valid input steps target exit) :
    ∃ events before call, steps = events.length + 1 ∧
      ExecutionPath policy (image.toGuestProgram valid) (image.executionBoot input) events before ∧
      SP1Halted (image.toGuestProgram valid) call.arg1 before.sail ∧
      ExecutionStep policy (image.toGuestProgram valid) before (.syscall call) target ∧
      call.arg1.setWidth 32 = exit := by
  obtain ⟨events, length, path⟩ := run.1
  obtain ⟨leading, before, call, rfl, prefixPath, lastStep, zero, sameExit⟩ :=
    path.ends_in_halt (image.executionBoot_running input) run.2
  exact ⟨leading, before, call, by simpa using length.symm, prefixPath,
    lastStep.halt_source zero, lastStep, sameExit⟩

end SP1Clean.Model.Core
