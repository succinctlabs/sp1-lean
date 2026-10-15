import SP1Clean.Model.Core.ExecutionReplay

/-! # Commitment-bank observations of whole-state execution

These are projections of the existing host interpreter and execution tape, not another host
machine. A selected bank changes only on its own COMMIT call. Every other call, including WRITE
and VERIFY, preserves it. Successful replay therefore determines the bank by the ordered list of
argument pairs. Bounds are established by successful execution, not assumed of a candidate tape.
-/

namespace SP1Clean.Model.Core

open Machine Soundness.Target

def HostState.bank (deferred : Bool) (host : HostState) : Vector (BitVec 32) 8 :=
  if deferred then host.deferred else host.committed

def bankKind (deferred : Bool) : SyscallKind := if deferred then .commitDeferred else .commit

/-- Select the existing call's arguments without introducing a second event representation. -/
def bankCall? (deferred : Bool) (code arg1 arg2 : BitVec 64) : Option (BitVec 64 × BitVec 64) :=
  if code = (bankKind deferred).code then some (arg1, arg2) else none

def bankEvent? (deferred : Bool) : ExecutionEvent → Option (BitVec 64 × BitVec 64)
  | .ordinary => none
  | .syscall call => bankCall? deferred call.rawCode call.arg1 call.arg2

/-- A total observation fold; successful execution separately establishes the slot bound. -/
def bankUpdate (values : Vector (BitVec 32) 8) (args : BitVec 64 × BitVec 64) :=
  if bound : args.1.toNat < 8 then values.set args.1.toNat (args.2.setWidth 32) else values

private theorem HostState.writeOutput_bank {host next : HostState} {descriptor : BitVec 64}
    {bytes : Bytes} (success : host.writeOutput descriptor bytes = some next) (deferred : Bool) :
    next.bank deferred = host.bank deferred := by
  unfold writeOutput at success
  split_ifs at success
  all_goals try { cases success; cases deferred <;> rfl }
  simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at success
  obtain ⟨⟨io, replies⟩, _, rfl⟩ := success
  cases deferred <;> rfl

/-- All eight concrete host calls have exactly this effect on either selected bank. -/
theorem HostState.executeKind_bank {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (success : host.executeKind policy context kind arg1 arg2 = some effect) (deferred : Bool) :
    (bankCall? deferred kind.code arg1 arg2).toList.foldl bankUpdate (host.bank deferred) =
      effect.state.bank deferred := by
  cases kind with
  | write =>
      obtain ⟨_, _, _, _, _, written, rfl⟩ :=
        (host.execute_write_iff policy context arg1 arg2 effect).mp success
      cases deferred <;> simpa [bankCall?, bankKind, SyscallKind.code] using
        (HostState.writeOutput_bank written _).symm
  | hintRead =>
      obtain ⟨_, _, _, _, _, _, rfl⟩ :=
        (host.execute_hintRead_iff policy context arg1 arg2 effect).mp success
      cases deferred <;> simp [bankCall?, bankKind, SyscallKind.code, HostState.bank]
  | verifyProof =>
      simp only [HostState.executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq] at success
      obtain ⟨_, _, _, _, rfl⟩ := success
      cases deferred <;> simp [bankCall?, bankKind, SyscallKind.code, HostState.bank]
  | enterUnconstrained | hintLength =>
      cases success
      cases deferred <;> simp [bankCall?, bankKind, SyscallKind.code]
  | halt | commit | commitDeferred =>
      simp only [HostState.executeKind] at success
      split_ifs at success
      all_goals cases success
      all_goals cases deferred <;> simp_all [bankCall?, bankKind, SyscallKind.code, bankUpdate, HostState.bank]

/-- The selected COMMIT directly performs one bounded bank update. -/
theorem HostState.executeBank_bank {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} (deferred : Bool) {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (success : host.executeKind policy context (bankKind deferred) arg1 arg2 = some effect) :
    bankUpdate (host.bank deferred) (arg1, arg2) = effect.state.bank deferred := by
  simpa only [bankCall?, if_pos rfl, ↓reduceIte, Option.toList_some, List.foldl_cons, List.foldl_nil] using
    HostState.executeKind_bank success deferred

theorem replayStep?_bank {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (success : replayStep? policy program source event = some target) (deferred : Bool) :
    (bankEvent? deferred event).toList.foldl bankUpdate (source.host.bank deferred) =
      target.host.bank deferred := by
  cases event with
  | ordinary =>
      simp only [replayStep?] at success
      split_ifs at success
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp success
      rfl
  | syscall call =>
      have step := (replayHost?_eq_some_iff _ _ _ _ _).mp success
      cases step with
      | syscall ran =>
          obtain ⟨pc, execution, _, _, run, hostEq, _, eventEq⟩ := HostState.step_observations ran
          have executed := ((source.host.run_eq_some_iff policy _ execution).mp run).2.2.2.2.2
          simpa only [bankEvent?, eventEq, HostExecution.toEvent, hostEq] using
            HostState.executeKind_bank executed deferred

/-- A successful whole-state replay fixes both banks, including nonzero continuation values. -/
theorem replayEvents?_bank {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (success : replayEvents? policy program source events = some target) (deferred : Bool) :
    (events.filterMap (bankEvent? deferred)).foldl bankUpdate (source.host.bank deferred) =
      target.host.bank deferred := by
  induction events generalizing source with
  | nil => cases success; rfl
  | cons event rest ih =>
      obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
      have split : (event :: rest).filterMap (bankEvent? deferred) =
          (bankEvent? deferred event).toList ++ rest.filterMap (bankEvent? deferred) := by
        cases found : bankEvent? deferred event <;> simp [found]
      rw [split, List.foldl_append, replayStep?_bank step deferred, ih suffix]

end SP1Clean.Model.Core
