import SP1Clean.Model.Core.ExecutionReplay

/-! # Complete host fields along a local execution

The existing interpreter determines terminal status from actual HALT labels. Calls other than
WRITE and VERIFY preserve public output, hook replies, requests, stdout, and stderr. This frame
is explicit here and must be derived from a physical receiver inventory before using it for AIR
soundness; it is not a restriction on the intended eight-call capstone.
-/

namespace SP1Clean.Model.Core

open Machine Soundness.Target

/-- Exactly the two calls that may change the host's external I/O fields are excluded. -/
def HostFrameSafe : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall call => call.rawCode ≠ SyscallKind.write.code ∧ call.rawCode ≠ SyscallKind.verifyProof.code

/-- The only label that changes terminal status is HALT, including a successful exit zero. -/
def hostExitAfter (status : Option (BitVec 32)) : ExecutionEvent → Option (BitVec 32)
  | .ordinary => status
  | .syscall call => if call.rawCode = SyscallKind.halt.code then some (call.arg1.setWidth 32) else status

private theorem HostState.executeKind_frame {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (success : host.executeKind policy context kind arg1 arg2 = some effect)
    (notWrite : kind ≠ .write) (notVerify : kind ≠ .verifyProof) :
    effect.state = { host with
      io.hints := effect.state.io.hints
      committed := effect.state.committed
      deferred := effect.state.deferred
      exitCode := effect.state.exitCode } := by
  cases kind with
  | write => exact (notWrite rfl).elim
  | verifyProof => exact (notVerify rfl).elim
  | hintRead =>
      obtain ⟨_, _, _, _, _, _, rfl⟩ :=
        (host.execute_hintRead_iff policy context arg1 arg2 effect).mp success
      rfl
  | enterUnconstrained | hintLength => cases success; rfl
  | halt | commit | commitDeferred =>
      simp only [HostState.executeKind] at success
      split_ifs at success
      all_goals cases success; rfl

/-- Preserve every remaining host field while allowing hints, banks, and exit status to change. -/
theorem ExecutionStep.host_frame {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target) (safe : HostFrameSafe event) :
    target.host = { source.host with
      io.hints := target.host.io.hints
      committed := target.host.committed
      deferred := target.host.deferred
      exitCode := target.host.exitCode } := by
  cases step with
  | ordinary => rfl
  | syscall ran =>
      obtain ⟨pc, execution, _, _, run, hostEq, _, eventEq⟩ := HostState.step_observations ran
      have observed := (HostState.run_eq_some_iff _ _ _ _).mp run
      rw [eventEq] at safe
      dsimp only
      rw [hostEq]
      exact HostState.executeKind_frame observed.2.2.2.2.2
        (fun same => safe.1 (congrArg SyscallKind.code same))
        (fun same => safe.2 (congrArg SyscallKind.code same))

/-- Preserve every external I/O field across the whole path, including an empty or stopped path. -/
theorem ExecutionPath.host_frame {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target)
    (safe : ∀ event ∈ events, HostFrameSafe event) :
    target.host = { source.host with
      io.hints := target.host.io.hints
      committed := target.host.committed
      deferred := target.host.deferred
      exitCode := target.host.exitCode } := by
  induction path with
  | nil => rfl
  | @cons source middle target event events step tail ih =>
      have first := step.host_frame (safe event (List.mem_cons_self ..))
      have rest := ih (fun event member => safe event (List.mem_cons_of_mem _ member))
      rw [first] at rest
      exact rest

/-- HALT effects agree with the existing full-state interpreter for all eight calls. -/
theorem ExecutionStep.host_exit {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target) :
    target.host.exitCode = hostExitAfter source.host.exitCode event := by
  cases step with
  | ordinary => rfl
  | syscall ran =>
      obtain ⟨pc, execution, _, _, run, hostEq, _, eventEq⟩ := HostState.step_observations ran
      have observed := (HostState.run_eq_some_iff _ _ _ _).mp run
      rw [hostEq, HostState.executeKind_exit observed.2.2.2.2.2, eventEq]
      simp only [hostExitAfter, HostExecution.toEvent, SyscallKind.code_injective.eq_iff]

/-- The event tape determines the complete optional exit status; zero does not stand for running. -/
theorem ExecutionPath.host_exit {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    target.host.exitCode = events.foldl hostExitAfter source.host.exitCode := by
  induction path with
  | nil => rfl
  | cons step _ ih => rw [List.foldl_cons, ← step.host_exit, ← ih]

/-- A local path emits exactly one exit receipt when it newly halts. Stopped sources emit none. -/
theorem ExecutionPath.exit_receipts {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy program source events target) :
    events.filterMap (hostExitAfter none) =
      if source.host.exitCode = none then target.host.exitCode.toList else [] := by
  induction path with
  | nil state => cases state.host.exitCode <;> simp
  | @cons source middle target event events step tail ih =>
      rw [step.running, if_pos rfl]
      cases event with
      | ordinary =>
          have running : middle.host.exitCode = none := step.host_exit.trans step.running
          simpa only [List.filterMap_cons, hostExitAfter, running, ↓reduceIte] using ih
      | syscall call =>
          by_cases halt : call.rawCode = SyscallKind.halt.code
          · have status : middle.host.exitCode = some (call.arg1.setWidth 32) := by
              simpa only [hostExitAfter, halt, ↓reduceIte] using step.host_exit
            have stopped : middle.host.exitCode ≠ none := by rw [status]; simp
            obtain ⟨rfl, rfl⟩ := tail.of_halted stopped
            simp [hostExitAfter, halt, status]
          · have running : middle.host.exitCode = none := by
              simpa only [hostExitAfter, halt, ↓reduceIte, step.running] using step.host_exit
            simpa only [List.filterMap_cons, hostExitAfter, halt, running, ↓reduceIte] using ih

end SP1Clean.Model.Core
