import SP1Clean.Model.Core.HostExecutionLaws

/-! # HALT is the only host transition that creates terminal status

This characterizes the stateful interpreter's exit field, including calls that mutate queues,
outputs, requests, or commitment banks. A final exit flag in a local path therefore denotes an
actual HALT rather than an unrelated host effect. The whole-machine no-resumption theorem also
guards ordinary Sail steps; stopping only the host dispatcher would not suffice.
-/

namespace SP1Clean.Model.Core

theorem HostState.writeOutput_exit {host next : HostState} {descriptor : BitVec 64}
    {bytes : Bytes} (success : host.writeOutput descriptor bytes = some next) :
    next.exitCode = host.exitCode := by
  unfold writeOutput at success
  split_ifs at success
  all_goals try { cases success; rfl }
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at success
  obtain ⟨⟨io, replies⟩, _, rfl⟩ := success
  rfl

/-- The final exit status is an exact semantic effect, independent of row selectors. -/
theorem HostState.executeKind_exit {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64}
    {effect : HostEffect}
    (success : host.executeKind policy context kind arg1 arg2 = some effect) :
    effect.state.exitCode =
      if kind = .halt then some (arg1.setWidth 32) else host.exitCode := by
  cases kind with
  | write =>
      obtain ⟨_, _, _, _, _, written, rfl⟩ :=
        (host.execute_write_iff policy context arg1 arg2 effect).mp success
      exact HostState.writeOutput_exit written
  | hintRead =>
      obtain ⟨_, _, _, _, _, _, rfl⟩ :=
        (host.execute_hintRead_iff policy context arg1 arg2 effect).mp success
      rfl
  | verifyProof =>
      simp only [executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq] at success
      obtain ⟨_, _, _, _, rfl⟩ := success
      rfl
  | enterUnconstrained | hintLength => cases success; rfl
  | halt | commit | commitDeferred =>
      simp only [executeKind] at success
      split_ifs at success
      all_goals cases success; rfl

theorem HostState.run_exit {host : HostState} {policy : HostPolicy} {context : HostReadContext}
    {execution : HostExecution} (success : host.run policy context = some execution) :
    execution.effect.state.exitCode =
      if execution.kind = .halt then some (execution.arg1.setWidth 32) else none := by
  have observed := (host.run_eq_some_iff policy context execution).mp success
  rw [HostState.executeKind_exit observed.2.2.2.2.2, observed.1]

end SP1Clean.Model.Core
