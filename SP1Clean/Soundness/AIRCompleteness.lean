import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Model.BalanceBridge
import SP1Clean.Soundness.AIR

/-! # Machine-level completeness: a generated trace yields a valid AIR witness

The construction-facing companion to `Soundness/AIR.lean`. Soundness starts from an arbitrary
witness the native relation accepts and extracts a Sail execution; this file starts from a
*well-formed, balanced, boundary-bound generated trace* and constructs a witness the native
relation accepts. The qualification matters: this theorem validates the AIR assembly performed by
a trace generator, but it does not construct that trace from an arbitrary Sail execution.

## The claim, exactly

`supported_core_native_complete` is `WitnessRelation.Complete` for the pair

* AIR side — `SupportedCoreNativeRelation`, the *same* relation soundness consumes: the public
  input matches, all 54 tables satisfy their constraints, all four channels balance, and the
  boundary binding holds;
* execution side — `SupportedCoreTraceGeneratableExecutionRelation`, a well-formed generated trace.

Nothing is weakened on the AIR side to make the construction go through. What the theorem provides
is the witness itself: `Assembly.lean`'s 53 built tables plus the verifier's boundary row, with
every witnessed cell computed by the circuits' own generators — never chosen to satisfy a
constraint.

## What the execution side asks for, and why each conjunct is there

1. **`trace.WellFormed`** — every occurrence routed to a table belongs there. This is the
   generator's routing obligation, and everything downstream of it (the whole assertion system of
   54 tables, on every row) is *derived*, in `witness_constraints`.
2. **`trace.ProviderMultiplicitiesFit`** — each aggregate Byte/Range/Program count satisfies
   `2 * m ≤ p`, so its field encoding has the intended nonnegative centered representative.
3. **`trace.Balanced`** — the four buses' centered-integer multiplicity sums vanish key by key and
   each channel has fewer interactions than the field characteristic. This admits both unit rows
   and canonically bounded aggregate provider counts. It is a combinatorial property of the emitted
   trace, and the integer-to-field bridge turns it into Clean's `BalancedChannels`.
4. **`SemanticBoundaryBinding`** — the program and memory-boundary tables really describe the
   caller's committed program and one concrete initial Sail state. This is the same companion
   predicate `SupportedCoreNativeRelation` carries, so it passes straight through.

## The boundary this theorem does *not* cross

It does **not** say every supported Sail execution produces a well-formed balanced trace. That is
the trace generator's own correctness — the step from `Model/Semantics/`'s `SailChain` to a
`SupportedCoreTraceWitness` — and it is not proved here or anywhere in this repository. Stated
plainly: this is completeness *relative to* a generator that routes and balances correctly, and the
value it adds is that no chip's constraint system, and no combination of the 53, can reject a
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

/-- **Provider-count capacity.**  Byte, Range, and Program providers accept aggregate natural
counts, while the AIR stores those counts in `ZMod p` and the machine ledger reads their centered
integer representatives.  These 24 source-level bounds make that encoding faithful: no
`m + p` alias is admitted and every count remains on the nonnegative side of `signedVal`.

Memory boundary multiplicities are already `Bool`, so they need no companion field here. -/
structure ProviderMultiplicitiesFit : Prop where
  u8Range : ∀ e ∈ trace.u8RangeEntries, e.MultiplicityFits p
  msb : ∀ e ∈ trace.msbEntries, e.MultiplicityFits p
  andByte : ∀ e ∈ trace.andByteEntries, e.MultiplicityFits p
  orByte : ∀ e ∈ trace.orByteEntries, e.MultiplicityFits p
  xorByte : ∀ e ∈ trace.xorByteEntries, e.MultiplicityFits p
  ltu : ∀ e ∈ trace.ltuEntries, e.MultiplicityFits p
  range : ∀ width e, e ∈ trace.rangeEntries width → e.MultiplicityFits p
  rom : ∀ e ∈ trace.romEntries, e.MultiplicityFits p

/-- **One channel's integer ledger balances.**  `Interaction.toAccess` converts every evaluated
field multiplicity to its centered integer representative.  Requiring its exact per-key sum to
vanish supports both the historical `0/±1` occurrence form and aggregate provider rows; the
separate count bound is precisely Clean's field no-wrap premise. -/
def BalancedOn (channel : RawChannel (ZMod p)) : Prop :=
  (trace.witness.interactionsWith channel).length < p ∧
    LookupAccessList.isConsistentBalanced
      ((trace.witness.interactionsWith channel).map Interaction.toAccess)

/-- The unit-occurrence ledger remains a convenient sufficient condition for `BalancedOn`.
This compatibility constructor is useful to trace generators which have not aggregated equal
provider keys: the old signed-message permutation first gives Clean balance, and the proved reverse
bridge then recovers exact centered-integer balance. -/
theorem balancedOn_of_signed_perm (channel : RawChannel (ZMod p))
    (hlen : (trace.witness.interactionsWith channel).length < p)
    (hbin : SignedMults (trace.witness.interactionsWith channel))
    (hperm : (pushedMessages (trace.witness.interactionsWith channel)).Perm
      (pulledMessages (trace.witness.interactionsWith channel))) :
    trace.BalancedOn channel := by
  refine ⟨hlen, LookupAccessList.isConsistentBalanced_of_balancedInteractions
    _ _ channel ?_ (List.Perm.refl _)
      (balancedInteractions_of_signed_perm _ hlen hbin hperm) ?_⟩
  · exact fun _ interactionMem =>
      Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem
  · intro access accessMem
    obtain ⟨interaction, interactionMem, rfl⟩ := List.mem_map.mp accessMem
    change signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
      signedVal interaction.mult = 1
    have hp : 2 < p := by
      have := Fact.out (p := 2 ^ 25 < p)
      omega
    rcases hbin interaction interactionMem with h | h | h
    · right; left
      rw [h, signedVal_is_real hp (Or.inl rfl), ZMod.val_zero, Nat.cast_zero]
    · right; right
      rw [h, signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (by omega), Nat.cast_one]
    · left
      rw [h, signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (by omega), Nat.cast_one]

/-- The generated trace balances on all four buses of `sp1Ensemble`. -/
def Balanced : Prop :=
  ∀ channel ∈ (sp1Ensemble (p := p)).channels, trace.BalancedOn channel

/-- **A balanced trace assembles into a witness whose channels balance.** The exact integer ledger
casts to Clean's field balance without a binary-multiplicity restriction; channel homogeneity is
provided by the ensemble's own `interactionsWith` membership theorem. -/
theorem witness_balancedChannels (hbal : trace.Balanced) : trace.witness.BalancedChannels := by
  intro channel hchannel
  obtain ⟨hlen, integerBalanced⟩ := hbal channel hchannel
  change BalancedInteractions (trace.witness.allTablesWitness.interactionsWith channel)
  rw [Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness]
  exact LookupAccessList.balancedInteractions_of_isConsistentBalanced
    _ _ channel
    (fun _ interactionMem =>
      Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem)
    (List.Perm.refl _) hlen integerBalanced

end SupportedCoreTraceWitness

/-! ## The relation and the theorem -/

/--
**The trace-generatable execution relation.** A generated trace counts as an execution of the
public statement when it is well-formed, its aggregate provider counts have faithful centered-field
encodings, its bus ledger balances, and its boundary tables bind to the caller's committed program
and one concrete initial Sail state.

The final conjunct is literally the companion predicate `SupportedCoreNativeRelation` carries, so
soundness and completeness speak about the same boundary object rather than two paraphrases of it.
-/
def SupportedCoreTraceGeneratableExecutionRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreTraceWitness p) :=
  fun statement trace =>
    trace.WellFormed ∧ trace.ProviderMultiplicitiesFit ∧ trace.Balanced ∧
      trace.publicValues = statement.publicValues ∧
      SemanticBoundaryBinding statement trace.witness

/--
**Machine-level completeness of the supported-core AIR.**

Every well-formed, capacity-bounded, balanced, boundary-bound generated trace has a native ensemble
witness satisfying `SupportedCoreNativeRelation`: the 53 tables of
`SupportedCoreTraceWitness.tables` plus the public
boundary row, with every witnessed cell produced by the circuits' own witness generators.

The two substantive conjuncts are proved, not assumed. `Constraints` is
`SupportedCoreTraceWitness.witness_constraints` — 54 tables' complete assertion systems,
each a citation of that table's `traceTable_constraints`, so the arithmetic content is the chips'
own completeness proofs. `BalancedChannels` is the ledger bridge applied per channel. The public
input matches by construction, and the boundary binding is carried through unchanged.
-/
theorem supported_core_native_complete :
    WitnessRelation.Complete (SupportedCoreNativeRelation (p := p))
      (SupportedCoreTraceGeneratableExecutionRelation (p := p)) := by
  rintro statement trace ⟨wf, _, balanced, publicEq, boundary⟩
  exact ⟨trace.witness, ⟨publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels balanced⟩, boundary⟩

/-- The public statement a generated trace proves, in the shape Clean's ensemble layer states:
`Ensemble.Statement` is the existential over witnesses that `SupportedCoreEnsembleRelation` spells
out per field. -/
theorem sp1Ensemble_statement_of_traceGeneratable
    (statement : SupportedCoreStatement p) (trace : SupportedCoreTraceWitness p)
    (valid : SupportedCoreTraceGeneratableExecutionRelation statement trace) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  obtain ⟨wf, _, balanced, publicEq, -⟩ := valid
  exact ⟨trace.witness, publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels balanced⟩

end SP1Clean.Soundness
