module

public import ToPolyFun.Dynamical.Labeled
public import ToClean.Air.CompleteEnsemble

/-! # A flat AIR ensemble realizing a labeled machine

## Gap against upstream

Clean's `Air.Flat.FormalEnsemble` bundles an ensemble with its soundness proof and nothing else,
and Clean has no notion of the machine an ensemble is meant to realize. `Realizes m ens boundary
admissible` says that raw acceptance of the ensemble `ens` at a public input is exactly the
existence of an admissible trace of the PolyFun `Labeled` machine `m` between the boundary states
read from that public input: soundness in Clean's own `Ensemble.Soundness` shape and a
proof-independent compiler in the `EnsembleCompiler` shape (`CompleteEnsemble.lean`). Neither
direction may mention rows, provers, or compiler success in its domain; `admissible` is the
semantic resource profile. The single statement is `Realizes.statement_iff`; reachability of the
boundary is its corollary. The machine side is PolyFun's own vocabulary (`Labeled`, `Prefix`,
`ReachableIn`, `Labeled.Trace`), which Clean plans to import; this file only ties it to Clean.
-/

@[expose] public section

namespace Air.Flat

open Air.Flat PFunctor PFunctor.DynSystem

universe uA uB

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable {p : PFunctor.{uA, uB}}

/-- The semantic reading of a public input: an admissible trace between its boundary states. -/
def Interpretation (m : Labeled.{0, uA, uB, 0} p) (boundary : PublicIO F → m.State × m.State)
    (admissible : PublicIO F → List m.Event → Prop) (publicInput : PublicIO F)
    (events : List m.Event) : Prop :=
  m.Trace (boundary publicInput).1 events (boundary publicInput).2 ∧ admissible publicInput events

/-- An ensemble realizes a machine: sound and complete for admissible traces at every boundary. -/
structure Realizes (m : Labeled.{0, uA, uB, 0} p) (ens : Ensemble F PublicIO)
    (boundary : PublicIO F → m.State × m.State)
    (admissible : PublicIO F → List m.Event → Prop) where
  sound : ens.Soundness (fun _ => True)
    (fun publicInput => ∃ events, Interpretation m boundary admissible publicInput events)
  compiler : EnsembleCompiler ens (List m.Event) (Interpretation m boundary admissible)

namespace Realizes

variable {m : Labeled.{0, uA, uB, 0} p} {ens : Ensemble F PublicIO}
  {boundary : PublicIO F → m.State × m.State} {admissible : PublicIO F → List m.Event → Prop}

/-- The single statement: raw acceptance is exactly an admissible trace between the boundary
states. -/
theorem statement_iff (r : Realizes m ens boundary admissible) (publicInput : PublicIO F) :
    ens.Statement publicInput ↔
      ∃ events, m.Trace (boundary publicInput).1 events (boundary publicInput).2 ∧
        admissible publicInput events :=
  (r.compiler.toCompleteEnsemble r.sound).statement_iff publicInput trivial

/-- An accepted public input has a reachable boundary. -/
theorem reachable_of_statement (r : Realizes m ens boundary admissible) {publicInput : PublicIO F}
    (accepted : ens.Statement publicInput) :
    ∃ n, m.toDynSystem.ReachableIn n (boundary publicInput).1 (boundary publicInput).2 := by
  obtain ⟨events, trace, _⟩ := (r.statement_iff publicInput).mp accepted
  exact ⟨events.length, trace.reachableIn⟩

end Realizes

end Air.Flat
