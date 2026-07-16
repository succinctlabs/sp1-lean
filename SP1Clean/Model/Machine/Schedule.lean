import Mathlib.Tactic

/-! # SP1 step schedules

SP1's interaction clocks are a schedule attached to an instruction, not the definition of an
instruction step.  In particular, ordinary instructions currently occupy eight clock ticks while
syscalls and state-bump rows use different windows.  Keeping that information in a first-class
schedule prevents the semantic machine from baking in `/ 8`, `% 8`, or fixed register/RAM offsets.

This module is intentionally independent of circuits and Sail.  Decoding an instruction into a
schedule belongs to the machine/AIR bridge; the generic clock arithmetic lives here. -/

namespace SP1Clean.Machine

/-- The kind of observable event placed in an instruction's clock window. -/
inductive AccessKind
  | statePull
  | statePush
  | registerRead
  | registerWrite
  | memoryRead
  | memoryWrite
  | programRead
deriving DecidableEq, Repr

/-- One event at an offset from the beginning of an instruction's clock window. -/
structure ScheduledAccess where
  kind : AccessKind
  offset : ℕ
deriving DecidableEq, Repr

/-- A positive-width instruction window together with the bus-event slots available in it.

Offsets may equal `duration`: that endpoint is shared with the following instruction and is used by
the outgoing State access.  Interior register and memory events have smaller offsets. -/
structure StepSchedule where
  duration : ℕ
  duration_pos : 0 < duration
  accesses : List ScheduledAccess
  accesses_bounded : ∀ access ∈ accesses, access.offset ≤ duration

/-- The absolute time of a scheduled access in a window beginning at `start`. -/
def ScheduledAccess.time (start : ℕ) (access : ScheduledAccess) : ℕ :=
  start + access.offset

/-- The start clock of step `n` for a possibly non-uniform schedule. -/
def clockAt (initialClock : ℕ) (schedule : ℕ → StepSchedule) : ℕ → ℕ
  | 0 => initialClock
  | n + 1 => clockAt initialClock schedule n + (schedule n).duration

@[simp] theorem clockAt_zero (initialClock : ℕ) (schedule : ℕ → StepSchedule) :
    clockAt initialClock schedule 0 = initialClock := rfl

@[simp] theorem clockAt_succ (initialClock : ℕ) (schedule : ℕ → StepSchedule) (n : ℕ) :
    clockAt initialClock schedule (n + 1) =
      clockAt initialClock schedule n + (schedule n).duration := rfl

/-- Every instruction advances time. -/
theorem clockAt_lt_succ (initialClock : ℕ) (schedule : ℕ → StepSchedule) (n : ℕ) :
    clockAt initialClock schedule n < clockAt initialClock schedule (n + 1) := by
  rw [clockAt_succ]
  have h := (schedule n).duration_pos
  omega

/-- The current ordinary-instruction convention.  This is a reusable schedule value rather than a
global semantic assumption; opcode-specific decoding may select a different schedule. -/
def ordinarySchedule : StepSchedule where
  duration := 8
  duration_pos := by omega
  accesses :=
    [ ⟨.statePull, 0⟩,
      ⟨.programRead, 0⟩,
      ⟨.memoryRead, 1⟩,
      ⟨.memoryWrite, 1⟩,
      ⟨.memoryRead, 2⟩,
      ⟨.registerRead, 2⟩,
      ⟨.registerRead, 3⟩,
      ⟨.registerRead, 4⟩,
      ⟨.registerWrite, 4⟩,
      ⟨.statePush, 8⟩ ]
  accesses_bounded := by simp

/-- SP1's core ECALL/syscall row advances by `CLK_INC + 256 = 264`.  The reserved interior region is
used by syscall-specific memory activity; its detailed slots belong to each syscall/precompile AIR. -/
def syscallSchedule : StepSchedule where
  duration := 264
  duration_pos := by omega
  accesses :=
    [ ⟨.statePull, 0⟩,
      ⟨.programRead, 0⟩,
      ⟨.registerRead, 2⟩,
      ⟨.registerRead, 3⟩,
      ⟨.registerRead, 4⟩,
      ⟨.statePush, 264⟩ ]
  accesses_bounded := by simp

/-- Constant eight-tick schedules recover the legacy clock formula. -/
@[simp] theorem clockAt_ordinary (initialClock n : ℕ) :
    clockAt initialClock (fun _ => ordinarySchedule) n = initialClock + 8 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [clockAt_succ, ih]
      simp only [ordinarySchedule]
      omega

@[simp] theorem clockAt_syscall (initialClock n : ℕ) :
    clockAt initialClock (fun _ => syscallSchedule) n = initialClock + 264 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [clockAt_succ, ih]
      simp only [syscallSchedule]
      omega

end SP1Clean.Machine
