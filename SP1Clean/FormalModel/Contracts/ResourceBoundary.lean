import SP1Clean.FormalModel.Contracts.LocalCoreBoundary
import SP1Clean.Model.Core.ExecutionResources

/-! # Resource checks on fixed complete boundaries

These are necessary endpoint conditions of the semantic profile. They do not assert that the
supplied target is the actual complete outgoing state, or bound intermediate peak occupancy.
Those conclusions require the complete boundary and event inventories.
-/

namespace SP1Clean.ResourceBoundary
open Model.Core

/-- Finite endpoint checks, computed before field narrowing. -/
def checkBounds (limits : ResourceLimits) (source target : ExecutionSnapshot) : Bool :=
  source.resources.checkFits limits && target.resources.checkFits limits &&
    decide (source.clock ≤ target.clock) && decide (target.clock - source.clock ≤ limits.ticks) &&
    decide (target.clock < 2 ^ 48) && decide (target.pc.toNat < 2 ^ 48)

/-- Endpoint occupancy and representability with an inclusive elapsed-tick ceiling. -/
def Bounds (limits : ResourceLimits) (source target : ExecutionSnapshot) : Prop :=
  source.resources.Fits limits ∧ target.resources.Fits limits ∧ source.clock ≤ target.clock ∧
    target.clock - source.clock ≤ limits.ticks ∧ target.clock < 2 ^ 48 ∧ target.pc.toNat < 2 ^ 48

/-- The executable endpoint check has no hidden capacity estimate. -/
theorem checkBounds_iff (limits : ResourceLimits) (source target : ExecutionSnapshot) :
    checkBounds limits source target = true ↔ Bounds limits source target := by
  simp only [checkBounds, Bool.and_eq_true, ResourceUsage.checkFits_iff, decide_eq_true_eq, Bounds]
  tauto

/-- The public outgoing clock is the canonical two-limb encoding of the supplied target. -/
def ClockFor {p : ℕ} [Fact p.Prime] (target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) : Prop :=
  input.final_clk_high = (target.clock / 2 ^ 24 : ℕ) ∧
    input.final_clk_low = (target.clock % 2 ^ 24 : ℕ)

/-- Meaning of the resource boundary subcircuit. -/
def Spec {p : ℕ} [Fact p.Prime] (limits : ResourceLimits) (source target : ExecutionSnapshot)
    (input : SP1PublicIO (ZMod p)) : Prop := Bounds limits source target ∧ ClockFor target input

/-- Field equality identifies the literal natural clock, without modular aliases. -/
theorem ClockFor.clock {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    {target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    (bound : target.clock < 2 ^ 48) (binding : ClockFor target input) :
    Semantics.clkNat input.final_clk_high input.final_clk_low = target.clock := by
  have primeBound := Fact.out (p := 2 ^ 24 < p)
  have high : target.clock / 2 ^ 24 < p := by omega
  have low : target.clock % 2 ^ 24 < p := by omega
  simp only [Semantics.clkNat, binding.1, binding.2,
    ZMod.val_natCast, Nat.mod_eq_of_lt high, Nat.mod_eq_of_lt low]
  omega

/-- The checked endpoint bounds the same path observer used by the semantic profile. -/
theorem Spec.path_work {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
    {limits : ResourceLimits} {source target : ExecutionSnapshot} {input : SP1PublicIO (ZMod p)}
    {policy : HostPolicy} {program : Soundness.Target.GuestProgram} {events : List Machine.ExecutionEvent}
    {actual : ExecutionState} (spec : Spec limits source target input)
    (path : ExecutionPath policy program source.realize events actual)
    (clock : actual.clock = Semantics.clkNat input.final_clk_high input.final_clk_low) :
    actual.clock = target.clock ∧
      (executionResources policy program source.realize events) .ticks ≤ limits.ticks ∧
      8 * events.length ≤ target.clock - source.clock := by
  have endpoint := clock.trans (spec.2.clock spec.1.2.2.2.2.1)
  have elapsed : (events.map Machine.ExecutionEvent.duration).sum = target.clock - source.clock := by
    have pathClock := path.clock
    change actual.clock = source.clock + _ at pathClock
    omega
  refine ⟨endpoint, ?_, ?_⟩
  · rw [path.resources_ticks, elapsed]
    exact spec.1.2.2.2.1
  · rw [← elapsed]
    exact event_count_le_ticks events

end SP1Clean.ResourceBoundary
