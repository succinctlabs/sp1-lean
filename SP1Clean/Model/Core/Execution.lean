import SP1Clean.Model.Core.HostSail
import SP1Clean.Model.Core.HostTerminal
import SP1Clean.Model.Machine.EventExecution

/-! # Stateful local execution of the native core

A boundary contains the entire Sail and host states, together with the execution clock. In
particular, equal PCs and clocks do not identify a boundary: RAM, registers, pending hints and
replies, accumulated outputs, commitment banks, and terminal status must agree as well.

Ordinary steps retire normally in official Sail. ECALL steps use the concrete host interpreter,
after checking the committed word against all four bytes in actual Sail memory, threading its
returned state. Both arms require a running source; HALT is a real transition and
there are no transitions out of a stopped state. Padding and provider/refresh rows are not
semantic steps. Supported decoding, ROM-write exclusion, and shard resource limits belong to the
native profile layered over this execution relation; no AIR correctness is asserted here.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Machine SP1Clean.Soundness.Target LeanRV64D

/-- A complete local semantic boundary. The host exit code is the sole terminal-status flag. -/
structure ExecutionState where
  sail : SailState
  host : HostState
  clock : ℕ

/-- One normally retiring instruction or one concretely interpreted SP1 host call. -/
inductive ExecutionStep (policy : HostPolicy) (program : GuestProgram) :
    ExecutionState → ExecutionEvent → ExecutionState → Prop
  | ordinary {source : ExecutionState} {target : SailState} :
      source.host.exitCode = none →
      ¬ AboutToExecuteEcall program source.sail →
      SailRetiresNormally source.sail target →
      ExecutionStep policy program source .ordinary
        ⟨target, source.host, source.clock + ordinarySchedule.duration⟩
  | syscall {source : ExecutionState} {host : HostState} {target : SailState}
      {event : CoreSyscallEvent} :
      source.host.step policy program source.clock source.sail = some (host, target, event) →
      ExecutionStep policy program source (.syscall event)
        ⟨target, host, source.clock + syscallSchedule.duration⟩

/-- A successful host step exposes the one concrete execution whose effects it applies. -/
theorem HostState.step_observations {host nextHost : HostState} {policy : HostPolicy}
    {program : GuestProgram} {clock : ℕ} {source target : SailState} {event : CoreSyscallEvent}
    (success : host.step policy program clock source = some (nextHost, target, event)) :
    ∃ pc execution, source.regs.get? LeanRV64D.Defs.Register.PC = some pc ∧
      program.fetchWord pc = some ECALL_ENC ∧
      host.run policy (.ofSail source) = some execution ∧
      nextHost = execution.effect.state ∧ target = execution.apply source pc ∧
      event = execution.toEvent clock pc := by
  simp only [HostState.step, bind, Option.bind_eq_some_iff] at success
  obtain ⟨pc, atPc, success⟩ := success
  split_ifs at success with fetched
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at success
    obtain ⟨execution, ran, hostEq, targetEq, eventEq⟩ := success
    exact ⟨pc, execution, atPc, fetched.1, ran, hostEq.symm, targetEq.symm, eventEq.symm⟩

/-- Construct a host step from observations and the concrete dispatcher result. -/
theorem HostState.step_of_run {host : HostState} {policy : HostPolicy} {program : GuestProgram}
    {source : SailState} {pc : BitVec 64} {execution : HostExecution}
    (atPc : source.regs.get? LeanRV64D.Defs.Register.PC = some pc)
    (fetched : program.fetchWord pc = some ECALL_ENC)
    (loaded : InstructionBytes.check source.mem.get? pc ECALL_ENC = true)
    (ran : host.run policy (.ofSail source) = some execution) (clock : ℕ) :
    host.step policy program clock source =
      some (execution.effect.state, execution.apply source pc, execution.toEvent clock pc) := by
  simp only [HostState.step, atPc, bind, Option.bind_some, fetched, loaded, and_self, ↓reduceIte, ran]

namespace ExecutionStep

variable {policy : HostPolicy} {program : GuestProgram}
  {source target : ExecutionState} {event : ExecutionEvent}

/-- Ordinary execution cannot resume after the host has halted either. -/
theorem running (step : ExecutionStep policy program source event target) :
    source.host.exitCode = none := by
  cases step with
  | ordinary running _ _ => exact running
  | syscall success =>
      obtain ⟨_, execution, _, _, ran, _⟩ := HostState.step_observations success
      exact ((source.host.run_eq_some_iff policy (.ofSail source.sail) execution).mp ran).1

/-- The architectural step count and the interaction clock are distinct quantities. -/
theorem clock (step : ExecutionStep policy program source event target) :
    target.clock = source.clock + event.duration := by
  cases step <;> rfl

theorem clock_lt (step : ExecutionStep policy program source event target) :
    source.clock < target.clock := by
  rw [step.clock]
  cases event <;> simp [ExecutionEvent.duration, ExecutionEvent.schedule,
    ordinarySchedule, syscallSchedule]

/-- The timestamp inside a syscall label is authenticated by the executing boundary. -/
theorem startsAt (step : ExecutionStep policy program source event target) :
    event.StartsAt source.clock := by
  cases step with
  | ordinary => trivial
  | syscall success =>
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := HostState.step_observations success
      rfl

/-- Projection uses the incoming host for this single step; whole paths thread the next host. -/
theorem sailEvent (step : ExecutionStep policy program source event target) :
    EventStep (source.host.handler policy) program source.sail event target.sail := by
  cases step with
  | ordinary _ notEcall normal => exact .ordinary notEcall normal.sailStep
  | syscall success =>
      have interpreted := HostState.step_sound success
      exact .syscall interpreted.1 interpreted.2

/-- A syscall label's PC names an ECALL in the actual incoming Sail memory as well as ROM. -/
theorem syscall_instructionBytes {call : CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall call) target) :
    InstructionBytes.check source.sail.mem.get? call.pc ECALL_ENC = true := by
  cases step with
  | syscall success =>
      obtain ⟨pc, execution, atPc, _, _, _, _, rfl⟩ := HostState.step_observations success
      exact HostState.step_instructionBytes success atPc

/-- A halted boundary has no outgoing semantic step, including an ordinary instruction. -/
theorem not_of_halted (halted : source.host.exitCode ≠ none) :
    ¬ ExecutionStep policy program source event target :=
  fun step => halted step.running

/-- Terminal status can only be produced by a genuine canonical HALT call. -/
theorem exit (step : ExecutionStep policy program source event target) :
    target.host.exitCode = match event with
      | .ordinary => none
      | .syscall call =>
          if call.rawCode = 0 then some (call.arg1.setWidth 32) else none := by
  cases step with
  | ordinary running _ _ => exact running
  | syscall success =>
      obtain ⟨pc, execution, _, _, ran, rfl, _, rfl⟩ := HostState.step_observations success
      have status := HostState.run_exit ran
      simpa only [HostExecution.toEvent,
        show execution.kind.code = 0 ↔ execution.kind = .halt by
          cases execution.kind <;> decide] using status

/-- The public exit, including exit zero, identifies the final real instruction. -/
theorem halted_iff (step : ExecutionStep policy program source event target) (code : BitVec 32) :
    target.host.exitCode = some code ↔
      ∃ call, event = .syscall call ∧ call.rawCode = 0 ∧ call.arg1.setWidth 32 = code := by
  rw [step.exit]
  cases event with
  | ordinary => simp
  | syscall call => by_cases halt : call.rawCode = 0 <;> simp [halt]

/-- The HALT label is backed by the committed ECALL and actual Sail x5/x10 observations. -/
theorem halt_source {call : CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall call) target) (zero : call.rawCode = 0) :
    SP1Halted program call.arg1 source.sail := by
  cases step with
  | syscall success =>
      obtain ⟨pc, execution, atPc, fetched, ran, _, _, rfl⟩ := HostState.step_observations success
      have observed := (source.host.run_eq_some_iff policy (.ofSail source.sail) execution).mp ran
      have code : source.sail.get_reg? 5#5 = some execution.kind.code := observed.2.1
      change execution.kind.code = 0 at zero
      exact ⟨pc, atPc, fetched, by simpa only [zero, HALT_SYSCALL] using code, observed.2.2.1⟩

/-- With the same complete input, neither the next event nor its effects are witness choices. -/
theorem deterministic {other : ExecutionState} {otherEvent : ExecutionEvent}
    (left : ExecutionStep policy program source event target)
    (right : ExecutionStep policy program source otherEvent other) :
    event = otherEvent ∧ target = other := by
  cases left with
  | ordinary _ notEcall normal =>
      cases right with
      | ordinary _ _ otherNormal =>
          obtain ⟨_, first⟩ := normal.sailStep
          obtain ⟨_, second⟩ := otherNormal.sailStep
          rw [first] at second
          cases second
          exact ⟨rfl, rfl⟩
      | syscall success => exact (notEcall (HostState.step_sound success).1).elim
  | syscall success =>
      cases right with
      | ordinary _ notEcall _ => exact (notEcall (HostState.step_sound success).1).elim
      | syscall otherSuccess =>
          rw [success] at otherSuccess
          cases otherSuccess
          exact ⟨rfl, rfl⟩

end ExecutionStep

end SP1Clean.Model.Core
