import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Proofs.Completeness.ClosureRealization
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

/-- `Closure.lean`'s `CountsFit` is this predicate plus the five Program cells that circuit passes
through unchecked. Both name the same capacity contract, so a caller supplies one and gets the
other; the closure needs the stronger form because its key round trip reads those cells back. -/
theorem CountsFit.providerMultiplicitiesFit (h : trace.CountsFit) :
    trace.ProviderMultiplicitiesFit where
  u8Range := h.u8Range
  msb := h.msb
  andByte := h.andByte
  orByte := h.orByte
  xorByte := h.xorByte
  ltu := h.ltu
  range := h.range
  rom := h.rom

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

/-- **`BalancedOn` on a preprocessed bus, derived rather than assumed.**

The payoff of the provider closure (`Proofs/Completeness/ClosureRealization.lean`): for the Byte and
Program channels — the two a preprocessed provider supplies unilaterally — `BalancedOn` follows from
the providers supplying exactly the demand. `suppliesDemand_of_closureRealized` derives that
hypothesis from the canonical realization with no evaluation at all;
`suppliesDemand_of_keys` reduces it to a finite check for a trace that supplies the same per-key
sums a different way (one unit-multiplicity row per occurrence, say).

The length bound stays a hypothesis: it is the field's no-wrap premise, a fact about how big this
shard is, not something the closure can supply. State and Memory are out of scope by construction —
their balance is a clock telescope and a per-address touch chain, and `closingAccesses_state` /
`closingAccesses_memory` record that the closure leaves them untouched. -/
theorem balancedOn_of_closure
    (hwf : trace.WellFormed) (hfit : trace.CountsFit) (hsupply : trace.SuppliesDemand)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (hkind : kindOf channel.name = InteractionKind.Byte ∨
      kindOf channel.name = InteractionKind.Program)
    (hlen : (trace.witness.interactionsWith channel).length < p) :
    trace.BalancedOn channel :=
  ⟨hlen, trace.channelLedger_isConsistentBalanced hwf hfit hsupply hnonpos channel hchannel
    hkind⟩

/-- **`BalancedOn` on a hand-off bus**, from a *computable* obligation.

The State and Memory buses carry tokens rather than aggregate demand, so their completeness
obligation is not a recount but a permutation: the bus's own half of the trace's ledger is the
concatenation of the complete lives of the tokens it carried, in whatever order fifty-three tables
happened to emit them.

Stated over `stateLedger` / `memoryLedger` — `List.filter` on the computable `fullLedger` — rather
than over Clean's per-channel `interactionsWith`, which is `noncomputable`. On a concrete shard both
sides of the permutation are then closed list terms, so the obligation is *decided* rather than
proved. `LookupAccessList.handoff` needs no side condition to balance, which is the whole contrast
with `balancedOn_of_closure`'s three: a structural fact about tokens, not an arithmetic one about
counts.

The `active` filter is load-bearing: padding rows emit their accesses at multiplicity `0`, and a
token's life is `±1`, so without it the permutation is false for every trace that pads.

The length bound stays a hypothesis on every bus for the same reason — it is the field's no-wrap
premise, a fact about how big this shard is. -/
theorem balancedOn_of_handoff (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (keys : List LookupAccessList.LookupKey)
    (hperm : (LookupAccessList.active (trace.fullLedger.filter fun a => a.1 = K)).Perm
      (LookupAccessList.handoff keys))
    (hlen : (trace.witness.interactionsWith channel).length < p) :
    trace.BalancedOn channel :=
  ⟨hlen, trace.channelLedger_isConsistentBalanced_of_handoff channel hchannel K hkind keys hperm⟩

/--
**The whole ensemble's channels balance — for the two structural reasons, and nothing else.**

The ensemble's completeness obligation, stated in the model's own terms rather than as four opaque
assumptions. What it costs:

* **Byte and Program** cost *nothing beyond the trace itself*. The providers supply the demand
  (`hsupply`) and no consumer key is already net-supplied (`hnonpos`); the demand is recounted from
  the consumers' own ledger, so there is no separate promise about what a provider row carries.
* **State and Memory** cost one permutation each — `stateKeys` are the machine's successive
  `(clock, pc)` tokens, `memoryKeys` the successive `(address, value, timestamp)` records, and the
  obligation is that each bus's ledger is exactly those tokens' complete lives. Both are stated over
  computable lists.
* **All four** cost the field's no-wrap bound, a fact about shard size that belongs to whoever chose
  the shard.

What is *absent* is as informative. No per-chip hypothesis, no promise about what any individual row
emits, and no appeal to the execution: four buses discharged by two constructions over
`LookupAccess` lists plus a size bound.
-/
theorem balanced_of_closure_and_handoff
    (hwf : trace.WellFormed) (hfit : trace.CountsFit) (hsupply : trace.SuppliesDemand)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    (stateKeys memoryKeys : List LookupAccessList.LookupKey)
    (hstate : (LookupAccessList.active trace.stateLedger).Perm
      (LookupAccessList.handoff stateKeys))
    (hmemory : (LookupAccessList.active trace.memoryLedger).Perm
      (LookupAccessList.handoff memoryKeys))
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p) :
    trace.Balanced := by
  intro channel hchannel
  have hlenc := hlen channel hchannel
  have hmem := hchannel
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.State rfl stateKeys hstate hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inl rfl) hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inr rfl) hlenc
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.Memory rfl memoryKeys hmemory hlenc

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


/-!
## Whole-ensemble propositional completeness

The composition, and the point of the framing. `Ensemble.Statement` is what the verifier layer
consumes: *there exists a witness whose public input matches, whose fifty-four tables all satisfy
their constraints, and whose four channels balance*. Every part of it is now discharged from
properties of the **trace**, and each part by a named mechanism rather than an assumption:

| Part | Mechanism | Costs |
|---|---|---|
| public input | construction | nothing |
| 54 tables' constraints | each table's own completeness proof | `WellFormed` |
| Byte + Program balance | closure — providers supply recounted demand | `CountsFit`, `SuppliesDemand`, nonpositivity |
| State + Memory balance | hand-off — each token created once, consumed once | one permutation per bus |
| all four | the field's no-wrap bound | shard size |

The two balance mechanisms are the whole content of the bus model, and they are disjoint by
structure rather than by convention: a hand-off bus cannot be closed (a recount would invent a
supplier for a token nobody created) and a closed bus has no chain to telescope.

The two permutation obligations are stated over `stateLedger` / `memoryLedger` — `List.filter` on
the computable `fullLedger` — so on a concrete shard both sides are closed list terms and the
obligation is decided rather than proved.
-/

/-- **A trace whose buses balance for the two structural reasons proves the ensemble's public
statement.** -/
theorem sp1Ensemble_statement_of_structural_balance
    (statement : SupportedCoreStatement p) (trace : SupportedCoreTraceWitness p)
    (wf : trace.WellFormed) (fit : trace.CountsFit) (hsupply : trace.SuppliesDemand)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    (stateKeys memoryKeys : List LookupAccessList.LookupKey)
    (hstate : (LookupAccessList.active trace.stateLedger).Perm
      (LookupAccessList.handoff stateKeys))
    (hmemory : (LookupAccessList.active trace.memoryLedger).Perm
      (LookupAccessList.handoff memoryKeys))
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p)
    (publicEq : trace.witness.publicInput = statement.publicValues) :
    (sp1Ensemble (p := p)).Statement statement.publicValues :=
  ⟨trace.witness, publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels
      (trace.balanced_of_closure_and_handoff wf fit hsupply hnonpos stateKeys memoryKeys
        hstate hmemory hlen)⟩

end SP1Clean.Soundness
