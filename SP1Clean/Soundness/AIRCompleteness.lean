import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Soundness.AIR

/-! # Machine-level completeness: a generated trace yields a valid AIR witness

The converse direction of `Soundness/AIR.lean`. Soundness starts from an arbitrary witness the
verifier accepts and extracts a Sail execution; this file starts from a *generated trace* and
constructs a witness the verifier accepts. Together they say the supported-core AIR neither admits
executions that did not happen nor rejects traces that did.

## The claim, exactly

`supported_core_native_complete` is `WitnessRelation.Complete` for the pair

* AIR side — `SupportedCoreNativeRelation`, the *same* relation soundness consumes: the public
  input matches, all forty-one tables satisfy their constraints, all four channels balance, and the
  boundary binding holds;
* execution side — `SupportedCoreTraceGeneratableExecutionRelation`, a well-formed generated trace.

Nothing is weakened on the AIR side to make the construction go through. What the theorem provides
is the witness itself: `Assembly.lean`'s forty built tables plus the verifier's boundary row, with
every witnessed cell computed by the circuits' own generators — never chosen to satisfy a
constraint.

## What the execution side asks for, and why each conjunct is there

1. **`trace.WellFormed`** — every occurrence routed to a table belongs there. This is the
   generator's routing obligation, and everything downstream of it (the whole assertion system of
   forty-one tables, on every row) is *derived*, in `witness_constraints`.
2. **`trace.Balanced`** — the four buses' pushed and pulled message multisets agree, with signed
   multiplicities and a length below the field characteristic. This is a combinatorial property of
   the emitted trace: a real generator gets it by construction (it emits a provider row per lookup,
   a State push per row consumed by the next row, a Memory push per read record), and the ledger
   turns it into Clean's `BalancedChannels`.
3. **`SemanticBoundaryBinding`** — the program and memory-boundary tables really describe the
   caller's committed program and one concrete initial Sail state. This is the same companion
   predicate `SupportedCoreNativeRelation` carries, so it passes straight through.

## The boundary this theorem does *not* cross

It does **not** say every supported Sail execution produces a well-formed balanced trace. That is
the trace generator's own correctness — the step from `Model/Semantics/`'s `SailChain` to a
`SupportedCoreTraceWitness` — and it is not proved here or anywhere in this repository. Stated
plainly: this is completeness *relative to* a generator that routes and balances correctly, and the
value it adds is that no chip's constraint system, and no combination of the forty, can reject a
correctly routed trace. Composing it with a verified generator is future work; see
`docs/roadmap.md`.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table EnsembleWitness)
open SP1Clean.Ledger (SignedMults pushedMessages pulledMessages
  balancedInteractions_of_signed_perm)
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceCompletenessFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-! ## The bus ledger of a generated trace -/

/--
**One channel's ledger balances.** The three conditions Clean's `BalancedInteractions` reduces to
under the ledger bridge: every interaction's multiplicity is `+1`, `0`, or `-1`; the whole
machine's pushed messages are a permutation of its pulled messages; and the total interaction count
stays below the field characteristic, so counting in `ZMod p` does not wrap.

This is a statement about the *emitted trace*, not about any row's witnessed cells. A generator
satisfies it by construction: it emits one provider row per lookup a chip performs, one State push
per row the next row consumes, and one Memory record per read.
-/
def BalancedOn (channel : RawChannel (ZMod p)) : Prop :=
  (trace.witness.interactionsWith channel).length < p ∧
    SignedMults (trace.witness.interactionsWith channel) ∧
    (pushedMessages (trace.witness.interactionsWith channel)).Perm
      (pulledMessages (trace.witness.interactionsWith channel))

/-- The generated trace balances on all four buses of `sp1Ensemble`. -/
def Balanced : Prop :=
  ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.BalancedOn channel

/-- **A balanced trace assembles into a witness whose channels balance.** One citation of the
ledger's `balancedInteractions_of_signed_perm` per channel; the ensemble's own
`allTablesWitness.interactionsWith` is definitionally the witness's, so no row is re-evaluated. -/
theorem witness_balancedChannels (hbal : trace.Balanced) : trace.witness.BalancedChannels := by
  intro channel hchannel
  obtain ⟨hlen, hbin, hperm⟩ := hbal channel hchannel
  exact balancedInteractions_of_signed_perm _ hlen hbin hperm

end SupportedCoreTraceWitness

/-! ## The relation and the theorem -/

/--
**The trace-generatable execution relation.** A generated trace counts as an execution of the
public statement when it is well-formed, its bus ledger balances, and its boundary tables bind to
the caller's committed program and one concrete initial Sail state.

The third conjunct is literally the companion predicate `SupportedCoreNativeRelation` carries, so
soundness and completeness speak about the same boundary object rather than two paraphrases of it.
-/
def SupportedCoreTraceGeneratableExecutionRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreTraceWitness p) :=
  fun statement trace =>
    trace.WellFormed ∧ trace.Balanced ∧
      trace.publicValues = statement.publicValues ∧
      SemanticBoundaryBinding statement trace.witness

/--
**Machine-level completeness of the supported-core AIR.**

Every well-formed, balanced, boundary-bound generated trace has an AIR witness the verifier
accepts: the forty tables of `SupportedCoreTraceWitness.tables` plus the public boundary row, with
every witnessed cell produced by the circuits' own witness generators.

The two substantive conjuncts are proved, not assumed. `Constraints` is
`SupportedCoreTraceWitness.witness_constraints` — forty-one tables' complete assertion systems,
each a citation of that table's `traceTable_constraints`, so the arithmetic content is the chips'
own completeness proofs. `BalancedChannels` is the ledger bridge applied per channel. The public
input matches by construction, and the boundary binding is carried through unchanged.
-/
theorem supported_core_native_complete :
    WitnessRelation.Complete (SupportedCoreNativeRelation (p := p))
      (SupportedCoreTraceGeneratableExecutionRelation (p := p)) := by
  rintro statement trace ⟨wf, balanced, publicEq, boundary⟩
  exact ⟨trace.witness, ⟨publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels balanced⟩, boundary⟩

/-- The public statement a generated trace proves, in the shape Clean's ensemble layer states:
`Ensemble.Statement` is the existential over witnesses that `SupportedCoreEnsembleRelation` spells
out per field. -/
theorem sp1Ensemble_statement_of_traceGeneratable
    (statement : SupportedCoreStatement p) (trace : SupportedCoreTraceWitness p)
    (valid : SupportedCoreTraceGeneratableExecutionRelation statement trace) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  obtain ⟨wf, balanced, publicEq, -⟩ := valid
  exact ⟨trace.witness, publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels balanced⟩

end SP1Clean.Soundness
