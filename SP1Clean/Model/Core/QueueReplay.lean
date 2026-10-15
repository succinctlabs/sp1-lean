import SP1Clean.Model.Core.ExecutionReplay
import SP1Clean.Model.Core.HintQueueEvent

/-! # Queue observations in successful whole-state replay

Length observations and reads are decoded from the complete semantic call label. All other
currently registered host calls preserve the hint queue. WRITE can prepend bytes and therefore
must not be erased: these projection lemmas explicitly exclude WRITE, to be discharged by the
installed receiver inventory. The general allocation-aware `HostState.hintEvent` remains the
queue projection for all eight host calls.

Successful replay is a premise, not a consequence of this module. The resulting invariant is
intended for each already-replayed prefix of the mixed grounding induction.
-/

namespace SP1Clean.Model.Core

open Machine Soundness.Target

/-- Observable queue actions carried by a call label; WRITE's allocated bytes need a richer label. -/
def queueCallEvent? (code arg2 result : BitVec 64) : Option HintQueue.Event :=
  if code = SyscallKind.hintLength.code then some (.length result)
  else if code = SyscallKind.hintRead.code then some (.read arg2.toNat) else none

def queueEvent? : ExecutionEvent → Option HintQueue.Event
  | .ordinary => none
  | .syscall call => queueCallEvent? call.rawCode call.arg2 call.result

/-- This explicit condition prevents silently erasing queue allocations from host replay. -/
def QueueProjectionSafe : ExecutionEvent → Prop
  | .ordinary => True
  | .syscall call => call.rawCode ≠ SyscallKind.write.code

private theorem HostState.executeKind_hints_eq {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (success : host.executeKind policy context kind arg1 arg2 = some effect)
    (notWrite : kind ≠ .write) (notRead : kind ≠ .hintRead) : effect.state.io.hints = host.io.hints := by
  cases kind with
  | write => exact (notWrite rfl).elim
  | hintRead => exact (notRead rfl).elim
  | enterUnconstrained | hintLength => cases success; rfl
  | halt | commit | commitDeferred =>
    simp only [HostState.executeKind] at success
    split_ifs at success
    cases success
    rfl
  | verifyProof =>
    simp only [HostState.executeKind, bind, Option.bind_eq_some_iff] at success
    obtain ⟨key, _, values, _, equal⟩ := success
    cases equal
    rfl

/-- A successful nonallocating host call agrees with its label's checked byte-queue action. -/
theorem HostState.run_queueReplay {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution}
    (success : host.run policy context = some execution) (notWrite : execution.kind ≠ .write) :
    HintQueue.replay? (queueCallEvent? execution.kind.code execution.arg2 execution.result).toList host.io.hints =
      some execution.effect.state.io.hints := by
  have projected := HostState.hintEvent_sound success
  by_cases length : execution.kind = .hintLength
  · simpa only [HostState.hintEvent, if_pos length, queueCallEvent?, length, ↓reduceIte,
      Option.toList_some, HintQueue.replay?, List.foldlM_cons, List.foldlM_nil,
      bind, pure, Option.bind_fun_some] using projected
  · by_cases read : execution.kind = .hintRead
    · simpa only [HostState.hintEvent, if_neg length, if_pos read, queueCallEvent?, read,
        SyscallKind.code, BitVec.reduceEq, reduceCtorEq, ↓reduceIte, Option.toList_some,
        HintQueue.replay?, List.foldlM_cons, List.foldlM_nil, bind, pure,
        Option.bind_fun_some] using projected
    · have same := HostState.executeKind_hints_eq
        ((host.run_eq_some_iff policy context execution).mp success).2.2.2.2.2 notWrite read
      have notLength : execution.kind.code ≠ SyscallKind.hintLength.code :=
        fun equal => length (SyscallKind.code_injective equal)
      have notRead : execution.kind.code ≠ SyscallKind.hintRead.code :=
        fun equal => read (SyscallKind.code_injective equal)
      simp only [queueCallEvent?, if_neg notLength, if_neg notRead, Option.toList_none,
        HintQueue.replay?, List.foldlM_nil, same, pure]

/-- Successful ordinary replay preserves the host; successful allowed host replay performs exactly
the label's queue observation or read. No Memory or host-success premise is replaced by this fact. -/
theorem replayStep?_queue {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (safe : QueueProjectionSafe event) (success : replayStep? policy program source event = some target) :
    HintQueue.replay? (queueEvent? event).toList source.host.io.hints = some target.host.io.hints := by
  cases event with
  | ordinary =>
    simp only [replayStep?] at success
    split_ifs at success
    obtain ⟨sail, _, rfl⟩ := Option.map_eq_some_iff.mp success
    rfl
  | syscall call =>
    have step := (replayHost?_eq_some_iff _ _ _ _ _).mp success
    cases step with
    | syscall ran =>
      obtain ⟨pc, execution, _, _, run, hostEq, _, eventEq⟩ := HostState.step_observations ran
      have noWrite : execution.kind ≠ .write := by
        intro equal
        apply safe
        rw [eventEq]
        exact congrArg SyscallKind.code equal
      simpa only [queueEvent?, eventEq, HostExecution.toEvent, hostEq] using HostState.run_queueReplay run noWrite

/-- A successful prefix's full host state contains exactly the bytes obtained from its queue
observations/reads. The caller must prove the tape contains no WRITE allocation event. -/
theorem replayEvents?_queue {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (safe : ∀ event ∈ events, QueueProjectionSafe event)
    (success : replayEvents? policy program source events = some target) :
    HintQueue.replay? (events.filterMap queueEvent?) source.host.io.hints = some target.host.io.hints := by
  induction events generalizing source with
  | nil => cases success; rfl
  | cons event rest ih =>
    obtain ⟨middle, step, suffix⟩ := Option.bind_eq_some_iff.mp success
    have first := replayStep?_queue (safe event (List.mem_cons_self ..)) step
    have remaining := ih (fun event member => safe event (List.mem_cons_of_mem _ member)) suffix
    have split : (event :: rest).filterMap queueEvent? =
        (queueEvent? event).toList ++ rest.filterMap queueEvent? := by
      cases found : queueEvent? event <;> simp only [List.filterMap_cons, found, Option.toList_none,
        Option.toList_some, List.nil_append, List.cons_append]
    rw [split, HintQueue.replay?_append, first, Option.bind_some, remaining]

end SP1Clean.Model.Core
