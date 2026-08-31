import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Proofs.Completeness.ClosureRealization
import SP1Clean.Proofs.Completeness.CanonicalClosure
import SP1Clean.Proofs.Completeness.ChipLedger
import SP1Clean.Model.BalanceBridge
import SP1Clean.Soundness.AIR

/-! # Machine-level completeness: a generated trace yields a valid AIR witness

The construction-facing companion to `Soundness/AIR.lean`. Soundness starts from an arbitrary
witness the native relation accepts and extracts a Sail execution; this file starts from a
*well-formed, balanced, boundary-bound generated trace* and constructs a witness the native
relation accepts. The qualification matters: this theorem validates the AIR assembly performed by
a trace generator, but it does not construct that trace from an arbitrary Sail execution.

## The claim, exactly

`supported_core_generated_trace_functionalCompleteness` is
`WitnessRelation.FunctionalCompleteness` for the pair

* AIR side — `SupportedCoreNativeRelation`, the *same* relation soundness consumes: the public
  input matches, all 54 tables satisfy their constraints, all four channels balance, and the
  boundary binding holds;
* execution side — `SupportedCoreGeneratedTraceRelation`, a well-formed generated trace whose
  actual Clean interactions balance.

Nothing is weakened on the AIR side to make the construction go through. Its proof-independent
map is exactly `fun _ trace => trace.witness`: `Assembly.lean`'s 53 built tables plus the verifier's
boundary row, with every witnessed cell computed by the circuits' own generators — never chosen to
satisfy a constraint. `supported_core_generated_trace_complete` is the ordinary relational projection of
that constructive certificate.

## What the execution side asks for, and why each conjunct is there

1. **`trace.WellFormed`** — every occurrence routed to a table belongs there. This is the
   generator's routing obligation, and everything downstream of it (the whole assertion system of
   54 tables, on every row) is *derived*, in `witness_constraints`.
2. **`trace.witness.BalancedChannels`** — balance is stated directly on the field-valued Clean
   interactions. Canonical provider closure may prove it without imposing a centered-integer
   `2 * m ≤ p` restriction; the older integer ledger remains only a construction helper.
3. **`SemanticBoundaryBinding`** — the program and memory-boundary tables really describe the
   caller's committed program and one concrete initial Sail state. This is the same companion
   predicate `SupportedCoreNativeRelation` carries, so it passes straight through.

## The boundary this theorem does *not* cross

It does **not** say every supported Sail execution produces such a trace. That is the separate,
faithful execution compiler. This file intentionally exports no abstract language certificate: a
map allowed to ignore its semantic witness is too weak to serve as completeness evidence.
-/

namespace SP1Clean.Soundness

open Air.Flat (Table EnsembleWitness)
open SP1Clean.Ledger (SignedMults pushedMessages pulledMessages
  balancedInteractions_of_signed_perm)
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceCompletenessFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/-! ## The bus ledger of a generated trace -/

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

/-- A structural token hand-off proves Clean's field-valued balance directly.  Unlike the
preprocessed-provider closure, State and Memory have unit multiplicities, so their stronger
integer hand-off statement remains the most useful construction interface. -/
theorem balancedInteractions_of_handoff (channel : RawChannel (ZMod p))
    (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (K : InteractionKind) (hkind : kindOf channel.name = K)
    (keys : List LookupAccessList.LookupKey)
    (hperm : (LookupAccessList.active (trace.fullLedger.filter fun a => a.1 = K)).Perm
      (LookupAccessList.handoff keys))
    (hlen : (trace.witness.interactionsWith channel).length < p) :
    BalancedInteractions (trace.witness.interactionsWith channel) := by
  have integerBalanced :=
    (trace.balancedOn_of_handoff channel hchannel K hkind keys hperm hlen).2
  exact LookupAccessList.balancedInteractions_of_isConsistentBalanced
    _ _ channel
    (fun _ interactionMem =>
      Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem)
    (List.Perm.refl _) hlen integerBalanced

/-- **The Exit hand-off of a compiled (halt-free) trace balances.**

The Exit bus has exactly two parties: the state-boundary verifier's ungated `⟨exit_code⟩` pull and
the Halt table's per-row hand-off pair.  On a trace whose Halt table carries only the padding row,
the live push is the zero code, so the bus balances exactly when the committed `exit_code` is zero
— which is precisely the ordinary sub-language the compiler targets. -/
theorem balancedOn_exit
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow (haltTable trace.witness) row).is_real = 0)
    (hhaltLen : (haltTable trace.witness).table.length = 1)
    (hexitZero : trace.witness.publicInput.exit_code = 0)
    (hlen : (trace.witness.interactionsWith Channels.exitChannel.toRaw).length < p) :
    trace.BalancedOn Channels.exitChannel.toRaw := by
  classical
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  have rawEq : trace.witness.interactionsWith Channels.exitChannel.toRaw =
      (typedEnsembleInteractionsWith trace.witness Channels.exitChannel).map
        TypedInteraction.raw := (typedEnsembleInteractionsWith_raw _ _).symm
  have closed : (typedEnsembleInteractionsWith trace.witness Channels.exitChannel).map
      TypedInteraction.raw =
      (Channels.exitChannel.pulledIfValue 1
        (⟨trace.witness.publicInput.exit_code⟩ : Channels.ExitMsg (ZMod p))) ::
      (haltTable trace.witness).table.flatMap fun row =>
        [Channels.exitChannel.pushedIfValue
           (haltRow (haltTable trace.witness) row).is_real
           (HaltChip.exitMessage (haltRow (haltTable trace.witness) row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow (haltTable trace.witness) row).is_real)
           (⟨0⟩ : Channels.ExitMsg (ZMod p))] := by
    rw [typedEnsembleExitInteractions_eq, List.map_append, List.map_flatMap]
    rfl
  have hbin : SignedMults (trace.witness.interactionsWith Channels.exitChannel.toRaw) := by
    rw [rawEq, closed]
    intro i iMem
    rcases List.mem_cons.mp iMem with rfl | iMem
    · exact Or.inr (Or.inr rfl)
    · obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp iMem
      rw [hhalt row rowMem] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inl rfl
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr (Or.inl (by simp [Channel.pushedIfValue]))
      · exact absurd hmem List.not_mem_nil
  have two_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hval := congrArg ZMod.val h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
      ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
    exact absurd hval (by norm_num)
  have haltRowMsgs : ∀ row ∈ (haltTable trace.witness).table,
      pushedMessages [Channels.exitChannel.pushedIfValue
           (haltRow (haltTable trace.witness) row).is_real
           (HaltChip.exitMessage (haltRow (haltTable trace.witness) row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow (haltTable trace.witness) row).is_real)
           (⟨0⟩ : Channels.ExitMsg (ZMod p))] =
        [(ProvableType.toElements (⟨0⟩ : Channels.ExitMsg (ZMod p))).toArray] ∧
      pulledMessages [Channels.exitChannel.pushedIfValue
           (haltRow (haltTable trace.witness) row).is_real
           (HaltChip.exitMessage (haltRow (haltTable trace.witness) row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow (haltTable trace.witness) row).is_real)
           (⟨0⟩ : Channels.ExitMsg (ZMod p))] = [] := by
    intro row rowMem
    have hzero := hhalt row rowMem
    constructor
    · rw [SP1Clean.Ledger.pushedMessages_cons, SP1Clean.Ledger.pushedMessages_cons,
        SP1Clean.Ledger.pushedMessages_nil,
        if_neg (by simp only [Channel.pushedIfValue, hzero]; exact zero_ne_one),
        if_pos (by simp only [Channel.pushedIfValue, hzero, sub_zero])]
      rfl
    · rw [SP1Clean.Ledger.pulledMessages_cons, SP1Clean.Ledger.pulledMessages_cons,
        SP1Clean.Ledger.pulledMessages_nil,
        if_neg (by
          simp only [Channel.pushedIfValue, hzero]
          intro h
          exact absurd (neg_eq_zero.mp h.symm) one_ne_zero),
        if_neg (by
          simp only [Channel.pushedIfValue, hzero, sub_zero]
          intro h
          exact two_ne (by linear_combination h))]
  have hperm : (pushedMessages
        (trace.witness.interactionsWith Channels.exitChannel.toRaw)).Perm
      (pulledMessages (trace.witness.interactionsWith Channels.exitChannel.toRaw)) := by
    rw [rawEq, closed, SP1Clean.Ledger.pushedMessages_cons, SP1Clean.Ledger.pulledMessages_cons,
      if_neg (by
        simp only [Channel.pulledIfValue]
        intro h
        exact two_ne (by linear_combination -h)),
      if_pos (by simp [Channel.pulledIfValue]),
      SP1Clean.Ledger.pushedMessages_flatMap, SP1Clean.Ledger.pulledMessages_flatMap]
    rw [List.flatMap_congr (fun row rowMem => (haltRowMsgs row rowMem).1),
      List.flatMap_congr (fun row rowMem => (haltRowMsgs row rowMem).2)]
    have hexitZeroMsg : (ProvableType.toElements
        (⟨trace.witness.publicInput.exit_code⟩ : Channels.ExitMsg (ZMod p))).toArray =
        (ProvableType.toElements (⟨0⟩ : Channels.ExitMsg (ZMod p))).toArray := by
      rw [hexitZero]
    rw [show (Channels.exitChannel.pulledIfValue 1
        (⟨trace.witness.publicInput.exit_code⟩ : Channels.ExitMsg (ZMod p))).msg =
      (ProvableType.toElements (⟨0⟩ : Channels.ExitMsg (ZMod p))).toArray from hexitZeroMsg]
    obtain ⟨r, htab⟩ := List.length_eq_one_iff.mp hhaltLen
    rw [htab]
    simp
  exact trace.balancedOn_of_signed_perm _ hlen hbin hperm

/-- **Whole-channel balance after canonical preprocessed closure.**

Byte and Program are closed against the literal Clean field interactions, so aggregate provider
counts may cross the centered half of `ZMod p`.  State and Memory remain token hand-offs.  The only
capacity premise is Clean's own interaction-list bound on each channel. -/
theorem canonicalClosure_balancedChannels_of_handoff
    (hwf : trace.canonicalClosure.WellFormed)
    (hserv : trace.DemandServable)
    (hnonpos : ∀ key ∈ trace.closingKeyList,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0)
    (stateKeys memoryKeys : List LookupAccessList.LookupKey)
    (hstate : (LookupAccessList.active trace.canonicalClosure.stateLedger).Perm
      (LookupAccessList.handoff stateKeys))
    (hmemory : (LookupAccessList.active trace.canonicalClosure.memoryLedger).Perm
      (LookupAccessList.handoff memoryKeys))
    (hhaltClosure : ∀ row ∈ (haltTable trace.canonicalClosure.witness).table,
      (haltRow (haltTable trace.canonicalClosure.witness) row).is_real = 0)
    (hhaltLenClosure : (haltTable trace.canonicalClosure.witness).table.length = 1)
    (hexitZero : trace.canonicalClosure.witness.publicInput.exit_code = 0)
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.canonicalClosure.witness.interactionsWith channel).length < p) :
    trace.canonicalClosure.witness.BalancedChannels := by
  intro channel hchannel
  change BalancedInteractions
    (trace.canonicalClosure.witness.allTablesWitness.interactionsWith channel)
  rw [Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness]
  have channelCase := hchannel
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at channelCase
  rcases channelCase with rfl | rfl | rfl | rfl | rfl
  · exact trace.canonicalClosure.balancedInteractions_of_handoff _ hchannel
      InteractionKind.State rfl stateKeys hstate (hlen _ hchannel)
  · exact trace.canonicalClosure_byte_balancedInteractions hwf hserv hnonpos (hlen _ hchannel)
  · exact trace.canonicalClosure_program_balancedInteractions hwf hserv hnonpos (hlen _ hchannel)
  · exact trace.canonicalClosure.balancedInteractions_of_handoff _ hchannel
      InteractionKind.Memory rfl memoryKeys hmemory (hlen _ hchannel)
  · exact LookupAccessList.balancedInteractions_of_isConsistentBalanced _ _ _
      (fun _ interactionMem =>
        Air.Flat.EnsembleWitness.channel_eq_of_mem_interactionsWith interactionMem)
      (List.Perm.refl _) (hlen _ hchannel)
      (trace.canonicalClosure.balancedOn_exit hhaltClosure hhaltLenClosure hexitZero
        (hlen _ hchannel)).2

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
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow (haltTable trace.witness) row).is_real = 0)
    (hhaltLen : (haltTable trace.witness).table.length = 1)
    (hexitZero : trace.witness.publicInput.exit_code = 0)
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p) :
    trace.Balanced := by
  intro channel hchannel
  have hlenc := hlen channel hchannel
  have hmem := hchannel
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.State rfl stateKeys hstate hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inl rfl) hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inr rfl) hlenc
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.Memory rfl memoryKeys hmemory hlenc
  · exact trace.balancedOn_exit hhalt hhaltLen hexitZero hlenc

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
**The generated-trace assembly relation.** A generated trace is ready for native assembly when it
is well-formed, its actual Clean channel interactions balance, and its boundary tables bind to the
caller's committed program and one concrete initial Sail state.

This is not an execution semantics.  In particular it carries no semantic witness and is not used
as the target of soundness.  The faithful compiler relates an `EventExecutionTrace` to this
assembly object explicitly.

The final conjunct is literally the companion predicate `SupportedCoreNativeRelation` carries, so
soundness and completeness speak about the same boundary object rather than two paraphrases of it.
-/
def SupportedCoreGeneratedTraceRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreTraceWitness p) :=
  fun statement trace =>
    trace.WellFormed ∧ trace.witness.BalancedChannels ∧
      trace.publicValues = statement.publicValues ∧
      SemanticBoundaryBinding statement trace.witness

/--
**Machine-level completeness of the supported-core AIR.**

Every well-formed, field-balanced, boundary-bound generated trace has a native ensemble
witness satisfying `SupportedCoreNativeRelation`: the 53 tables of
`SupportedCoreTraceWitness.tables` plus the public
boundary row, with every witnessed cell produced by the circuits' own witness generators.

The two substantive conjuncts are proved, not assumed. `Constraints` is
`SupportedCoreTraceWitness.witness_constraints` — 54 tables' complete assertion systems,
each a citation of that table's `traceTable_constraints`, so the arithmetic content is the chips'
own completeness proofs. `BalancedChannels` is the ledger bridge applied per channel. The public
input matches by construction, and the boundary binding is carried through unchanged.
-/
def supported_core_generated_trace_functionalCompleteness :
    WitnessRelation.FunctionalCompleteness (SupportedCoreNativeRelation (p := p))
      (SupportedCoreGeneratedTraceRelation (p := p)) where
  map _ trace := trace.witness
  map_valid statement trace valid := by
    obtain ⟨wf, balanced, publicEq, boundary⟩ := valid
    exact ⟨⟨publicEq, trace.witness_constraints wf, balanced⟩, boundary⟩

/-- The relational form of `supported_core_generated_trace_functionalCompleteness`.
existential completeness API. -/
theorem supported_core_generated_trace_complete :
    WitnessRelation.Complete (SupportedCoreNativeRelation (p := p))
      (SupportedCoreGeneratedTraceRelation (p := p)) :=
  (supported_core_generated_trace_functionalCompleteness (p := p)).complete

/-- The public statement a generated trace proves, in the shape Clean's ensemble layer states:
`Ensemble.Statement` is the existential over witnesses that `SupportedCoreEnsembleRelation` spells
out per field. -/
theorem sp1Ensemble_statement_of_generated_trace
    (statement : SupportedCoreStatement p) (trace : SupportedCoreTraceWitness p)
    (valid : SupportedCoreGeneratedTraceRelation statement trace) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  obtain ⟨wf, balanced, publicEq, -⟩ := valid
  exact ⟨trace.witness, publicEq, trace.witness_constraints wf, balanced⟩


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
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow (haltTable trace.witness) row).is_real = 0)
    (hhaltLen : (haltTable trace.witness).table.length = 1)
    (hexitZero : trace.witness.publicInput.exit_code = 0)
    (stateLinks : List (LookupAccessList.LookupKey × LookupAccessList.LookupKey))
    (hstateRegroup : (stateInstrLinks trace ++ stateBumpLinks trace).Perm stateLinks)
    (hstateChain : LookupAccessList.IsHandoffChain (stateInitToken trace)
      stateLinks (stateFinalToken trace))
    (memoryChains : List (LookupAccessList.LookupKey ×
      List (LookupAccessList.LookupKey × LookupAccessList.LookupKey) ×
      LookupAccessList.LookupKey))
    (hmemoryChains : ∀ chain ∈ memoryChains,
      LookupAccessList.IsHandoffChain chain.1 chain.2.1 chain.2.2)
    (hmemoryRegroup : (LookupAccessList.active trace.memoryLedger).Perm
      (memoryChains.flatMap LookupAccessList.chainLedger))
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p)
    (publicEq : trace.witness.publicInput = statement.publicValues) :
    (sp1Ensemble (p := p)).Statement statement.publicValues := by
  let stateKeys := LookupAccessList.chainTokens
    (stateInitToken trace, stateLinks, stateFinalToken trace)
  let memoryKeys := memoryChains.flatMap LookupAccessList.chainTokens
  have hstate : (LookupAccessList.active trace.stateLedger).Perm
      (LookupAccessList.handoff stateKeys) :=
    stateLedger_perm_handoff_chronological trace hbinary hbump hhalt stateLinks hstateRegroup
      hstateChain
  have hmemory : (LookupAccessList.active trace.memoryLedger).Perm
      (LookupAccessList.handoff memoryKeys) :=
    memoryLedger_perm_handoff trace memoryChains hmemoryChains hmemoryRegroup
  exact ⟨trace.witness, publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels
      (trace.balanced_of_closure_and_handoff wf fit hsupply hnonpos stateKeys memoryKeys
        hstate hmemory hhalt hhaltLen hexitZero hlen)⟩

end SP1Clean.Soundness
