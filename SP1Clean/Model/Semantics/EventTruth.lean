import SP1Clean.Model.Semantics.Truth
import SP1Clean.Model.Semantics.EventTime

/-! # Shard-local truth against the event transcript

`Model/Semantics/Truth.lean` says what it means for a bus message to be *true*: a State message is
true when some prefix of the official Sail run reaches a state with that pc at that clock, and a
Memory record is true when the location's content at that micro-time matches. Both quantify over
`SailChain` — a chain of `try_step` iterations — and that is what a syscall row cannot satisfy, at
any timeline, because its transition is deliberately not a `SailStep`.

This file restates the same three predicates against `Semantics.eventTrajectory`, so a step may be
an ordinary Sail step *or* a handled syscall. The definitions are otherwise unchanged, and each
comes with the bridge that keeps the generalization free: on an all-ordinary transcript the event
form **implies** the Sail form, so anything proved here is available to every existing consumer.

The implication is one-directional on purpose. `LocalStateTruthT` asks only that *some* Sail chain
reaches the state; the event form additionally pins which transcript did it. That is a strictly
stronger statement, which is the right direction — the grounding engine consumes truth, so a
stronger hypothesis is free, and the converse would be a claim that the transcript is the only
route, which nothing needs and nothing proves. -/

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open LeanRV64D.Defs
open SP1Clean.Machine
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Where the transcript runs out -/

/-- A defined event trajectory bounds its index by the transcript's length: past the end there is
no state, so an existential over reachable steps is automatically finite. This is what lets the
truth predicates below quantify over an unbounded `n` and still bridge to the Sail form, which
needs the bound. -/
theorem le_length_of_eventTrajectory_eq_some {handler : ExecutableSyscallHandler}
    {program : GuestProgram} {events : List ExecutionEvent} {initial state : SailState} :
    ∀ {n : ℕ}, eventTrajectory handler program events initial n = some state → n ≤ events.length := by
  intro n
  induction n generalizing state with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
      intro hstep
      rw [eventTrajectory_succ] at hstep
      match hget : events[n]? with
      | none => rw [hget] at hstep; exact absurd hstep (by simp)
      | some event =>
          exact (List.getElem?_eq_some_iff.mp hget).choose

/-! ## The three predicates, event-indexed -/

/-- The timeline reader against a transcript: the location's content at micro-time `τ`, where each
step is executed by the handler rather than assumed to be a Sail step. -/
noncomputable def microValueE (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (events : List ExecutionEvent) (s0 : SailState) (tl : Timeline) (loc : MemLoc) (τ : ℕ) :
    Option (BitVec 64) :=
  if τ < tl.start 0 then
    locContent s0 loc
  else
    let k := tl.stepOf τ
    let δ := τ - tl.start k
    let takePost : Bool := match loc with
      | .reg _ => regEffectOffset ≤ δ
      | .ram _ => ramEffectOffset ≤ δ
    (eventTrajectory handler program events s0 (if takePost then k + 1 else k)).bind
      (locContent · loc)

/-- `value` is the content of `location` at `time` on the transcript's execution. -/
def LocalValueAtE (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (tl : Timeline) (location : MemLoc)
    (time : ℕ) (value : Word (ZMod p)) : Prop :=
  microValueE handler program events initial tl location time = some (Word.toBitVec64 value)

/-- A State message is true when the transcript reaches a state with that pc at that clock. -/
def LocalStateTruthE (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (events : List ExecutionEvent) (initial : SailState) (tl : Timeline)
    (m : StateMsg (ZMod p)) : Prop :=
  ∃ (n : ℕ) (state : SailState),
    eventTrajectory handler program events initial n = some state ∧
    StateMsg.timeNat m = tl.start n ∧
    state.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
    RomLoaded program state ∧
    SailConfigured state

/-! ## The bridges

Each is the `_allOrdinary` analogue of the existing `_ordinary` family: on a transcript of ordinary
events the new predicate lands on the old one, so no consumer of the Sail-indexed layer has to
change to benefit from a proof carried out here. -/

/-- On an all-ordinary transcript the event reader agrees with the Sail reader at every micro-time
the transcript covers. The side condition is the reader's own step index, not the message's: past
the transcript the event trajectory is undefined while `chainState` keeps going, and the two cannot
agree there. -/
theorem microValueE_allOrdinary (handler : ExecutableSyscallHandler) (program : GuestProgram)
    (events : List ExecutionEvent) (s0 : SailState) (tl : Timeline) (loc : MemLoc) (τ : ℕ)
    (ordinary : ∀ event ∈ events, event = ExecutionEvent.ordinary)
    (covered : ¬ τ < tl.start 0 →
      (if (match loc with
            | .reg _ => decide (regEffectOffset ≤ τ - tl.start (tl.stepOf τ))
            | .ram _ => decide (ramEffectOffset ≤ τ - tl.start (tl.stepOf τ)))
          then tl.stepOf τ + 1 else tl.stepOf τ) ≤ events.length) :
    microValueE handler program events s0 tl loc τ = microValueT s0 tl loc τ := by
  rw [microValueE, microValueT]
  by_cases hpre : τ < tl.start 0
  · rw [if_pos hpre, if_pos hpre]
  · rw [if_neg hpre, if_neg hpre]
    exact congrArg (Option.bind · _)
      (eventTrajectory_allOrdinary handler program events s0 ordinary _ (covered hpre))

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- On an all-ordinary transcript, event-indexed State truth implies the Sail-indexed form. -/
theorem localStateTruthT_of_localStateTruthE {handler : ExecutableSyscallHandler}
    {program : GuestProgram} {events : List ExecutionEvent} {initial : SailState} {tl : Timeline}
    {m : StateMsg (ZMod p)}
    (ordinary : ∀ event ∈ events, event = ExecutionEvent.ordinary)
    (truth : LocalStateTruthE handler program events initial tl m) :
    LocalStateTruthT program initial tl m := by
  obtain ⟨n, state, hstep, hclock, hpc, hrom, hcfg⟩ := truth
  refine ⟨n, state, ?_, hclock, hpc, hrom, hcfg⟩
  refine sailChain_of_chainState ?_
  rw [chainState, ← eventTrajectory_allOrdinary handler program events initial ordinary n
    (le_length_of_eventTrajectory_eq_some hstep)]
  exact hstep

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The uniform instantiation: an all-ordinary transcript at its own timeline is the eight-tick
one, so a proof carried out against the transcript lands exactly where the engine reads today. -/
theorem localStateTruthT_of_localStateTruthE_ordinary {handler : ExecutableSyscallHandler}
    {program : GuestProgram} {events : List ExecutionEvent} {initial : SailState}
    {initialClock : ℕ} {m : StateMsg (ZMod p)}
    (ordinary : ∀ event ∈ events, event = ExecutionEvent.ordinary)
    (truth : LocalStateTruthE handler program events initial
      (eventTimeline events initialClock) m) :
    LocalStateTruth program initial initialClock m := by
  rw [← localStateTruthT_ordinary]
  rw [← eventTimeline_allOrdinary events initialClock ordinary]
  exact localStateTruthT_of_localStateTruthE ordinary truth

end SP1Clean.Semantics
