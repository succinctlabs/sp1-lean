module

public import PolyFun.PFunctor.Dynamical.Safety
public import ToPolyFun.Dynamical.Orbit

/-! # Event traces of labeled systems

## Gap against upstream

PolyFun's `DynSystem.Labeled` attaches an event label to every direction, and `Prefix.events` /
`Prefix.last` read the trace and endpoint of a finite orbit, but there is no named relation
"`t` is reachable from `s` along the trace `events`". `Labeled.Trace` is that relation — the
labeled counterpart of `ReachableIn` — with the algebra a semantic statement needs: the empty
trace, concatenation (via `Prefix.append`), and the projection back to `ReachableIn`. Stated in
PolyFun's own namespace so it can be contributed as it is. -/

@[expose] public section

namespace PFunctor.DynSystem.Labeled

universe u uA uB w

variable {p : PFunctor.{uA, uB}} (m : Labeled.{u, uA, uB, w} p)

/-- Some finite orbit from `s` ends at `t` with exactly the event trace `events`. -/
def Trace (s : m.State) (events : List m.Event) (t : m.State) : Prop :=
  ∃ (n : ℕ) (orbit : m.toDynSystem.Prefix s n), orbit.events m.event = events ∧ orbit.last = t

variable {m}

/-- The empty trace stays put. -/
theorem Trace.nil (s : m.State) : m.Trace s [] s := ⟨0, .nil, rfl, rfl⟩

/-- Traces concatenate at their shared state. -/
theorem Trace.append {s mid t : m.State} {first second : List m.Event}
    (left : m.Trace s first mid) (right : m.Trace mid second t) :
    m.Trace s (first ++ second) t := by
  obtain ⟨_, pre, rfl, rfl⟩ := left
  obtain ⟨_, post, rfl, rfl⟩ := right
  exact ⟨_, pre.append post, pre.events_append m.event post, pre.last_append post⟩

/-- A trace witnesses counted reachability. -/
theorem Trace.reachableIn {s t : m.State} {events : List m.Event} (trace : m.Trace s events t) :
    m.toDynSystem.ReachableIn events.length s t := by
  obtain ⟨n, orbit, rfl, rfl⟩ := trace
  rw [orbit.length_events m.event]
  exact ⟨orbit, rfl⟩

end PFunctor.DynSystem.Labeled
