import SP1Clean.FormalModel.TraceGen.Events
import SP1Clean.Model.Semantics.MicroTime

/-!
# The trace layer's clock literals are the machine model's constants

`FormalModel/TraceGen/Events.lean` imports nothing Sail-side, by design: an event is a description
of what the *executor* did, and forcing the trace vocabulary through the Sail model would put the
whole generated interpreter underneath every chip's completeness proof. The cost of that separation
is that the layer spells its clock arithmetic as bare literals — `clk % 8 = 1`, `prevTsA < clk + 4`,
`prevTsB < clk + 3`, `prevTsC < clk + 2`, and the RAM access at `clk + 1`.

Those are SP1's `CLK_INC` and `MemoryAccessPosition` values, and on the semantics side the same
numbers are named (`Model/Semantics/MicroTime.lean`) and carried structurally by
`Machine.ordinarySchedule`. Until this module they agreed only by inspection. Every equation here is
`rfl` — that is the point: the constants really are the same, and a change to either side now breaks
a named theorem instead of silently desynchronising a comment from a literal.

This matters at exactly one seam. A generator producing events from a Sail execution knows its
clocks through `clockAt` and `microValue`; the events it emits owe `WellFormed`, which is stated in
literals. These lemmas are what let one discharge the other.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Semantics
open SP1Clean.Machine (ordinarySchedule)

/-! ## The window width -/

/-- The schedule's window width **is** `CLK_INC`. `Model/Machine/Schedule.lean` carries the number
structurally (as a `StepSchedule` field) and `Model/Semantics/MicroTime.lean` names it; the timed
grounding engine consumes the former and `microValue` the latter. -/
theorem ordinarySchedule_duration_eq : ordinarySchedule.duration = ordinaryClkInc := rfl

/-- The trace layer's clock modulus is that width. Every event family's `clk_mod` conjunct is
`e.clk % ordinaryClkInc = 1`, spelled with the literal. -/
theorem clkInc_eq_eight : ordinaryClkInc = 8 := rfl

/-! ## The access offsets

SP1's `MemoryAccessPosition { UntrustedInstruction = 0, Memory = 1, C = 2, B = 3, A = 4 }`. The
trace layer times each access at `clk + position`, and the timestamp conjuncts of every event
family's `WellFormed` say the previous access to that location was strictly earlier. -/

theorem ramOffset_eq_one : ramEffectOffset = 1 := rfl
theorem regCOffset_eq_two : regCOffset = 2 := rfl
theorem regBOffset_eq_three : regBOffset = 3 := rfl
theorem regAOffset_eq_four : regEffectOffset = 4 := rfl

/-- The four offsets are strictly ordered, and all lie inside one window. That ordering is what
makes the intra-row effect convention coherent — a RAM effect lands before the operand reads
observe it, and the `op_a` write lands after both. -/
theorem accessOffsets_ordered :
    0 < ramEffectOffset ∧ ramEffectOffset < regCOffset ∧ regCOffset < regBOffset ∧
      regBOffset < regEffectOffset ∧ regEffectOffset < ordinaryClkInc := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## Restating the event contracts over the named constants

The four timestamp conjuncts of `RTypeEvent.WellFormed`, and the state discipline, with every
literal replaced by the constant it stands for. A generator discharges these; the `rfl` is what
says it has discharged the right thing. -/

theorem rTypeEvent_clk_mod_eq (e : RTypeEvent) :
    (e.clk % 8 = 1) = (e.clk % ordinaryClkInc = 1) := rfl

theorem rTypeEvent_prevTsA_eq (e : RTypeEvent) :
    (e.prevTsA < e.clk + 4) = (e.prevTsA < e.clk + regEffectOffset) := rfl

theorem rTypeEvent_prevTsB_eq (e : RTypeEvent) :
    (e.prevTsB < e.clk + 3) = (e.prevTsB < e.clk + regBOffset) := rfl

theorem rTypeEvent_prevTsC_eq (e : RTypeEvent) :
    (e.prevTsC < e.clk + 2) = (e.prevTsC < e.clk + regCOffset) := rfl

/-- The RAM access block is built at `clk + 1` (`TraceGen/Inputs.lean`'s `memoryAccessCols`
`currTs` argument), which is `clk + MemoryAccessPosition::Memory`. -/
theorem ramAccess_clock_eq (clk : ℕ) : clk + 1 = clk + ramEffectOffset := rfl

/-! ## The clock a step occupies

`clockAt_ordinary` already gives `clockAt c₀ (fun _ => ordinarySchedule) n = c₀ + 8 * n`. Restated
here over the constant, and paired with the fact a generator actually needs: an execution whose
genesis clock obeys the discipline has every step's clock obeying it too. -/

theorem clockAt_ordinary_eq (initialClock n : ℕ) :
    Machine.clockAt initialClock (fun _ => ordinarySchedule) n
      = initialClock + ordinaryClkInc * n :=
  Machine.clockAt_ordinary initialClock n

/-- **The clock discipline propagates.** SP1's clock starts at 1 and steps by `CLK_INC`, so every
ordinary step's clock is `≡ 1 (mod 8)` — which is exactly the `clk_mod` conjunct every event family
owes, and the only clock fact the trace layer asks a generator to supply. -/
theorem clockAt_ordinary_mod (initialClock n : ℕ) (h : initialClock % ordinaryClkInc = 1) :
    Machine.clockAt initialClock (fun _ => ordinarySchedule) n % ordinaryClkInc = 1 := by
  have hmod : initialClock % 8 = 1 := h
  rw [clockAt_ordinary_eq]
  show (initialClock + 8 * n) % 8 = 1
  omega

end SP1Clean.TraceGen
