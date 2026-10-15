import SP1Clean.Proofs.Completeness.Assembly
import SP1Clean.Proofs.Completeness.Ledger
import SP1Clean.Proofs.Completeness.ClosureRealization
import SP1Clean.Proofs.Completeness.CanonicalClosure
import SP1Clean.Proofs.Completeness.ChipLedger
import SP1Clean.Model.BalanceBridge
import SP1Clean.Soundness.AIR

/-! # Generated-trace assembly completeness

A well-formed generated trace with balanced Clean interactions, matching public values and
semantic boundary binding yields the same native relation consumed by `Soundness/AIR.lean`.
The witness map is `trace.witness`: 55 physical tables with canonical derived data and a separate
public verifier. Circuit completeness proves physical constraints; channel balance and boundary
binding are explicit obligations of `SupportedCoreGeneratedTraceRelation`.

Byte/Program providers close demand, State/Memory use token chains, and Exit uses the ordinary
compiler's zero-exit Halt padding. Its Syscall and PublicValues channels are silent because this
constructor's syscall table is empty. Every channel retains Clean's occurrence bound.

This is an assembly theorem, not a compiler from arbitrary Sail executions. The complete mixed
execution domain and authenticated boundary obligations remain separate semantic work.
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

/-- An empty channel ledger balances vacuously, including the two syscall channels of this
ordinary trace constructor. -/
theorem balancedOn_of_interactions_nil {channel : RawChannel (ZMod p)}
    (h : trace.witness.interactionsWith channel = []) : trace.BalancedOn channel := by
  refine ⟨?_, ?_⟩ <;> rw [h]
  · simpa using (Fact.out (p := p.Prime)).pos
  · intro k
    rfl

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

/-- The generated trace balances on every registered channel of `sp1Ensemble`. -/
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
concatenation of the complete lives of the tokens it carried, in their physical emission order.

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
      (haltRow trace.witness.data row).is_real = 0)
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
           (haltRow trace.witness.data row).is_real
           (HaltChip.exitMessage (haltRow trace.witness.data row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow trace.witness.data row).is_real)
           (⟨0⟩ : Channels.ExitMsg (ZMod p))] := by
    -- The syscall table is a second Exit contributor in general; for a *compiled* trace it has no
    -- rows, so its gated pushes collapse and the hand-off is the halt table's alone.
    rw [typedEnsembleExitInteractions_eq, syscallInstrsTable_nil trace]
    simp only [List.flatMap_nil, List.append_nil, List.map_append, List.map_flatMap]
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
           (haltRow trace.witness.data row).is_real
           (HaltChip.exitMessage (haltRow trace.witness.data row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow trace.witness.data row).is_real)
           (⟨0⟩ : Channels.ExitMsg (ZMod p))] =
        [(ProvableType.toElements (⟨0⟩ : Channels.ExitMsg (ZMod p))).toArray] ∧
      pulledMessages [Channels.exitChannel.pushedIfValue
           (haltRow trace.witness.data row).is_real
           (HaltChip.exitMessage (haltRow trace.witness.data row)),
         Channels.exitChannel.pushedIfValue
           (1 - (haltRow trace.witness.data row).is_real)
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
      (haltRow trace.canonicalClosure.witness.data row).is_real = 0)
    (hhaltLenClosure : (haltTable trace.canonicalClosure.witness).table.length = 1)
    (hexitZero : trace.canonicalClosure.witness.publicInput.exit_code = 0)
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.canonicalClosure.witness.interactionsWith channel).length < p) :
    trace.canonicalClosure.witness.BalancedChannels := by
  intro channel hchannel
  change BalancedInteractions (trace.canonicalClosure.witness.interactionsWith channel)
  have channelCase := hchannel
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at channelCase
  rcases channelCase with rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [witness_syscallChannel_silent _ trace.canonicalClosure.witness_syscallTable_nil]
    exact balancedInteractions_nil
  · rw [witness_publicValuesChannel_silent _ trace.canonicalClosure.witness_syscallTable_nil]
    exact balancedInteractions_nil

/-- Integer balance on every registered channel: Byte/Program use provider closure,
State/Memory use token hand-offs, Exit uses zero-exit Halt padding, and the two syscall channels
are silent. The occurrence bound applies to every channel. -/
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
      (haltRow trace.witness.data row).is_real = 0)
    (hhaltLen : (haltTable trace.witness).table.length = 1)
    (hexitZero : trace.witness.publicInput.exit_code = 0)
    (hlen : ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p) :
    trace.Balanced := by
  intro channel hchannel
  have hlenc := hlen channel hchannel
  have hmem := hchannel
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.State rfl stateKeys hstate hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inl rfl) hlenc
  · exact trace.balancedOn_of_closure hwf hfit hsupply hnonpos _ hchannel (Or.inr rfl) hlenc
  · exact trace.balancedOn_of_handoff _ hchannel InteractionKind.Memory rfl memoryKeys hmemory hlenc
  · exact trace.balancedOn_exit hhalt hhaltLen hexitZero hlenc
  · exact trace.balancedOn_of_interactions_nil (witness_syscallChannel_silent _ trace.witness_syscallTable_nil)
  · exact trace.balancedOn_of_interactions_nil (witness_publicValuesChannel_silent _ trace.witness_syscallTable_nil)

/-- **A balanced trace assembles into a witness whose channels balance.** The exact integer ledger
casts to Clean's field balance without a binary-multiplicity restriction; channel homogeneity is
provided by the ensemble's own `interactionsWith` membership theorem. -/
theorem witness_balancedChannels (hbal : trace.Balanced) : trace.witness.BalancedChannels := by
  intro channel hchannel
  obtain ⟨hlen, integerBalanced⟩ := hbal channel hchannel
  change BalancedInteractions (trace.witness.interactionsWith channel)
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

/-- **The compiler's trace meets the interim syscall boundary.** `noActiveRows` is a consequence of
the syscall table having no rows at all; `haltTablePresent` is the compiled Halt table's one padding
row — the `⟨0⟩` Exit push that balances the verifier's ungated pull. -/
theorem SupportedCoreTraceWitness.syscallTableInactive (trace : SupportedCoreTraceWitness p) :
    SyscallTableInactive trace.witness where
  noActiveRows := by
    rw [realSyscallInstrsRows, syscallInstrsTable_nil trace]; rfl
  haltTablePresent := by
    have hlen := trace.haltTablePadding.1
    intro hnil
    rw [hnil] at hlen
    simp at hlen

/-- Assemble a native witness from a well-formed, balanced, boundary-bound generated trace.
Circuit completeness derives physical-table constraints. Balance includes the public verifier;
semantic boundary binding comes from the relation, and public input matches by construction. -/
def supported_core_generated_trace_functionalCompleteness :
    WitnessRelation.FunctionalCompleteness (SupportedCoreNativeRelation (p := p))
      (SupportedCoreGeneratedTraceRelation (p := p)) where
  map _ trace := trace.witness
  map_valid statement trace valid := by
    obtain ⟨wf, balanced, publicEq, boundary⟩ := valid
    exact ⟨⟨publicEq, trace.witness_constraints wf, balanced⟩, boundary,
      trace.syscallTableInactive⟩

/-- The existential form of `supported_core_generated_trace_functionalCompleteness`. -/
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


/-! ## Ensemble statements from structural balance -/

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
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
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
    stateLedger_perm_handoff_chronological trace hbinary hbump hhalt
      (witness_syscallRows_padding trace) stateLinks hstateRegroup hstateChain
  have hmemory : (LookupAccessList.active trace.memoryLedger).Perm
      (LookupAccessList.handoff memoryKeys) :=
    memoryLedger_perm_handoff trace memoryChains hmemoryChains hmemoryRegroup
  exact ⟨trace.witness, publicEq, trace.witness_constraints wf,
    trace.witness_balancedChannels
      (trace.balanced_of_closure_and_handoff wf fit hsupply hnonpos stateKeys memoryKeys
        hstate hmemory hhalt hhaltLen hexitZero hlen)⟩

end SP1Clean.Soundness
