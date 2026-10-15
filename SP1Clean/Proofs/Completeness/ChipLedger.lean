import SP1Clean.Model.CleanLedger
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.TypedMemoryBalance
import SP1Clean.Proofs.Completeness.ClosureRealization

/-! # State and Memory ledgers of generated traces

Filter the canonical witness's complete interaction list to obtain each bus's literal access
ledger. The typed State and Memory emission theorems supply its row decomposition; no parallel
per-table ledger representation is needed. State hand-off chains and per-location Memory chains
then discharge the existing balance contracts, retaining the public boundary and count bounds.

The current compiler emits no active HALT or syscall rows. Their padding/silence proofs below
are properties of this compiler, not restrictions on the chip semantics or the full mixed target.
-/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.Channels (stateChannel)
open LookupAccessList

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section Trace

variable [Fact (2 ^ 25 < p)]

/-- Filtering by a declared bus's kind retains exactly that channel's evaluated occurrences. -/
theorem busLedger_eq_channelLedger (trace : SupportedCoreTraceWitness p)
    (channel : RawChannel (ZMod p)) (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (K : InteractionKind) (hkind : kindOf channel.name = K) :
    trace.fullLedger.filter (fun a => a.1 = K) =
      (trace.witness.interactionsWith channel).map Interaction.toAccess := by
  rw [trace.fullLedger_eq_witness_interactions]
  exact (witness_channelLedger_eq_filter_kind trace.witness channel hchannel K hkind).symm

/-- The State instance. -/
theorem stateLedger_eq_channelLedger (trace : SupportedCoreTraceWitness p) :
    trace.stateLedger =
      (trace.witness.interactionsWith (stateChannel (p := p)).toRaw).map Interaction.toAccess :=
  busLedger_eq_channelLedger trace _ (by simp [sp1Ensemble_channels]) InteractionKind.State rfl

omit [Fact (2 ^ 24 < p)] in
/-- The stable halt position of an assembled witness is its generated Halt table. -/
theorem SupportedCoreTraceWitness.haltTable_witness
    (trace : SupportedCoreTraceWitness p) :
    haltTable trace.witness = trace.providerTableFor .halt := by
  unfold haltTable SupportedCoreTraceWitness.witness
  simp [SupportedCoreTraceWitness.tables, SupportedCoreTraceWitness.instructionTables,
    SupportedCoreTraceWitness.providerTables, haltIndex, instructionTableCount,
    stateSilentProviderTableCount, InstructionChipId.all, ProviderTableId.all,
    ByteProviderId.all]

omit [Fact (2 ^ 25 < p)] in
/-- HALT decoding reads the input prefix independently of the evaluation data. -/
@[simp] theorem haltRow_buildRow
    (input : HaltChip.Inputs (ZMod p)) (generationData evaluationData : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    haltRow evaluationData (HaltChip.component.buildRow input generationData hint) = input :=
  HaltChip.component.rowInput_buildRow input generationData evaluationData hint

/-- **The compiled trace's Halt table is exactly the padding row.**  The deterministic compiler
emits no halt event yet (`Occurrence .halt := Empty`), so its Halt table is the one all-zero
padding row: the exit hand-off pushes the zero code, which is what balances the state-boundary
verifier's ungated `⟨exit_code⟩` pull on the ordinary sub-language. -/
theorem SupportedCoreTraceWitness.haltTablePadding
    (trace : SupportedCoreTraceWitness p) :
    (haltTable trace.witness).table.length = 1 ∧
      ∀ row ∈ (haltTable trace.witness).table,
        (haltRow trace.witness.data row).is_real = 0 := by
  have htab : (haltTable trace.witness).table =
      [HaltChip.component.buildRow (HaltChip.paddingInputs (p := p)) trace.generationData trace.hint] := by
    have hocc : trace.providerOccurrences ProviderTableId.halt = [] := by
      cases h : trace.providerOccurrences ProviderTableId.halt with
      | nil => rfl
      | cons e _ => exact e.elim
    rw [trace.haltTable_witness]
    simp only [SupportedCoreTraceWitness.providerTableFor, hocc]
    rfl
  refine ⟨by rw [htab]; rfl, ?_⟩
  intro row rowMem
  rw [htab, List.mem_singleton] at rowMem
  subst rowMem
  rw [haltRow_buildRow]
  rfl

/-- The compiled trace has no active Halt row: its Halt table is the padding row. -/
theorem SupportedCoreTraceWitness.realHaltRows_nil (trace : SupportedCoreTraceWitness p) :
    realHaltRows trace.witness = [] := by
  obtain ⟨-, hpad⟩ := trace.haltTablePadding
  rw [realHaltRows, List.filter_eq_nil_iff]
  intro row rowMem
  simp only [decide_eq_true_eq, hpad row rowMem]
  exact zero_ne_one

/-- The Memory projection retains the channel's complete evaluated occurrence list. -/
theorem memoryLedger_eq_channelLedger (trace : SupportedCoreTraceWitness p) :
    trace.memoryLedger =
      (trace.witness.interactionsWith (Channels.memoryChannel (p := p)).toRaw).map
        Interaction.toAccess :=
  busLedger_eq_channelLedger trace _ (by simp [sp1Ensemble_channels]) InteractionKind.Memory rfl

/-! ## The State bus is a hand-off

Everything above composes here. `Soundness/TypedState.lean` already decomposes an arbitrary
`EnsembleWitness`'s State interactions into the public boundary pair, the decoded instruction rows'
pull/push pairs, and the StateBump rows'. `busLedger_eq_channelLedger` puts that in this layer's
orientation, `active_flatMap_gatedPair` drops the padding rows, and `chainLedger_perm_handoff`
turns the resulting chain into a hand-off.

The tokens are the messages themselves: `msgToken` of the boundary's init/final states, and of each
row's pulled and pushed state. -/

noncomputable def stateInitToken (trace : SupportedCoreTraceWitness p) : LookupKey :=
  msgToken stateChannel
    ⟨trace.witness.publicInput.init_clk_high, trace.witness.publicInput.init_clk_low,
      trace.witness.publicInput.init_pc0, trace.witness.publicInput.init_pc1,
      trace.witness.publicInput.init_pc2⟩

noncomputable def stateFinalToken (trace : SupportedCoreTraceWitness p) : LookupKey :=
  msgToken stateChannel
    ⟨trace.witness.publicInput.final_clk_high, trace.witness.publicInput.final_clk_low,
      trace.witness.publicInput.final_pc0, trace.witness.publicInput.final_pc1,
      trace.witness.publicInput.final_pc2⟩

noncomputable def stateInstrLinks (trace : SupportedCoreTraceWitness p) :
    List (LookupKey × LookupKey) :=
  ((decodedInstructionRows (p := p) trace.witness.tables).filter fun d =>
      signedVal (d.toChipRow trace.witness.data).is_real = 1).map fun d =>
    (msgToken stateChannel (statePullMessage (d.toChipRow trace.witness.data)),
      msgToken stateChannel (statePushMessage (d.toChipRow trace.witness.data)))

noncomputable def stateBumpLinks (trace : SupportedCoreTraceWitness p) :
    List (LookupKey × LookupKey) :=
  ((stateBumpTable trace.witness).table.filter fun row =>
      signedVal (stateBumpRow trace.witness.data row).is_real = 1).map fun row =>
    (msgToken stateChannel
        (StateBumpChip.pulledMessage (stateBumpRow trace.witness.data row)),
      msgToken stateChannel
        (StateBumpChip.pushedMessage (stateBumpRow trace.witness.data row)))

omit [Fact (2 ^ 24 < p)] in
/-- The syscall table's row list, in the form `BumpDecode`'s accessor spells it. -/
theorem syscallInstrsTable_nil (trace : SupportedCoreTraceWitness p) :
    (syscallInstrsTable trace.witness).table = [] :=
  trace.witness_syscallTable_nil _ rfl

omit [Fact (2 ^ 24 < p)] in
/-- **Every syscall row is padding — vacuously, since there are none.** This is the shape the State
ledger's `hsyscall` premise asks for, and it is a property of *this compiler's trace* rather than of
the chip: `syscallInstrsTraceInputs` is `[]` by construction. -/
theorem witness_syscallRows_padding (trace : SupportedCoreTraceWitness p) :
    ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0 := by
  intro row hrow
  rw [syscallInstrsTable_nil trace] at hrow
  exact absurd hrow List.not_mem_nil

theorem active_stateLedger_eq (trace : SupportedCoreTraceWitness p)
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
    (hsyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0) :
    active trace.stateLedger =
      ([accessAt (stateFinalToken trace) (-1), accessAt (stateInitToken trace) 1] ++
        (stateInstrLinks trace).flatMap fun l => linkAccesses l.1 l.2) ++
        ((stateBumpLinks trace).flatMap fun l => linkAccesses l.1 l.2) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  have h1 : signedVal (1 : ZMod p) = 1 := by
    rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    rfl
  have hm1 : signedVal (-1 : ZMod p) = -1 := by
    rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega)]
    rfl
  rw [stateLedger_eq_channelLedger, ← typedEnsembleInteractionsWith_raw,
    typedEnsembleStateInteractions_eq]
  simp only [List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    TypedInteraction.pulledIfValue, TypedInteraction.pushedIfValue,
    toAccess_pulledIfValue, toAccess_pushedIfValue, h1, hm1, active_append]
  have h0 : signedVal (0 : ZMod p) = 0 := by
    rw [signedVal_is_real hp (Or.inl rfl), ZMod.val_zero]
    rfl
  have hgateInstr : ∀ a ∈ decodedInstructionRows (p := p) trace.witness.tables,
      signedVal (a.toChipRow trace.witness.data).is_real = 0 ∨
        signedVal (a.toChipRow trace.witness.data).is_real = 1 := by
    intro a ha
    rcases hbinary a ha with h | h <;> rw [h]
    · exact Or.inl h0
    · exact Or.inr h1
  have hgateBump : ∀ row ∈ (stateBumpTable trace.witness).table,
      signedVal (stateBumpRow trace.witness.data row).is_real = 0 ∨
        signedVal (stateBumpRow trace.witness.data row).is_real = 1 := by
    intro row hrow
    rcases hbump row hrow with h | h <;> rw [h]
    · exact Or.inl h0
    · exact Or.inr h1
  have hgateHalt : ∀ row ∈ (haltTable trace.witness).table,
      signedVal (haltRow trace.witness.data row).is_real = 0 ∨
        signedVal (haltRow trace.witness.data row).is_real = 1 := by
    intro row hrow
    rw [hhalt row hrow]
    exact Or.inl h0
  have hfilterHalt : ((haltTable trace.witness).table.filter fun row =>
      signedVal (haltRow trace.witness.data row).is_real = 1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row hrow
    rw [hhalt row hrow, h0]
    decide
  have hgateSyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      signedVal (syscallInstrsRow trace.witness.data row).is_real = 0 ∨
        signedVal (syscallInstrsRow trace.witness.data row).is_real = 1 := by
    intro row hrow
    rw [hsyscall row hrow]
    exact Or.inl h0
  have hfilterSyscall : ((syscallInstrsTable trace.witness).table.filter fun row =>
      signedVal (syscallInstrsRow trace.witness.data row).is_real = 1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row hrow
    rw [hsyscall row hrow, h0]
    decide
  simp only [signedVal_neg hp]
  rw [active_flatMap_gatedPair _ _ _ _ hgateInstr,
    active_flatMap_gatedPair _ _ _ _ hgateBump,
    active_flatMap_gatedPair _ _ _ _ hgateHalt, hfilterHalt,
    active_flatMap_gatedPair _ _ _ _ hgateSyscall, hfilterSyscall]
  simp only [stateInstrLinks, stateBumpLinks, stateInitToken, stateFinalToken,
    List.flatMap_map, List.flatMap_nil, List.append_nil, active, List.filter_cons,
    multOf_accessAt, List.filter_nil]
  norm_num

/-- **The State bus's ledger is its tokens' complete lives.**

The obligation `balancedOn_of_handoff` asks for, discharged from the chain. `IsHandoffChain` is the
PC chain in this layer's vocabulary: the machine starts holding the public initial state, each real
row consumes what it holds and produces its successor, and the boundary pulls the final state.

The two binarity hypotheses are the selector facts the ensemble's constraints already supply
(`witness_stateBumpRows_selectorBinary` and the decoded-row analogue); they are what makes a padding
row's pair vanish rather than land on a token nobody holds. -/
theorem stateLedger_perm_handoff (trace : SupportedCoreTraceWitness p)
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
    (hsyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0)
    (hchain : IsHandoffChain (stateInitToken trace)
      (stateInstrLinks trace ++ stateBumpLinks trace) (stateFinalToken trace)) :
    (active trace.stateLedger).Perm
      (handoff (stateInitToken trace ::
        (stateInstrLinks trace ++ stateBumpLinks trace).map Prod.snd)) := by
  rw [active_stateLedger_eq trace hbinary hbump hhalt hsyscall, List.append_assoc,
    ← List.flatMap_append]
  exact List.Perm.trans (List.Perm.swap _ _ _)
    (chainLedger_perm_handoff _ _ _ hchain)


/-! ## The Memory bus

Memory follows the same route as State up to one real difference, and it is structural rather than
incidental.

The State bus carries **one** token — the machine's `(clock, pc)` — so its ledger is one chain whose
links are supplied by the ordered trace construction. The Memory bus carries **one token per
location**: a record is pushed by whoever wrote it
and pulled by the next access to that same address. So its ledger is a *family* of chains, one per
touched location, each opened by memory-init and closed by memory-finalize
(`multiChainLedger_perm_handoff` is why that costs no more than one chain).

The consequence for this layer: the decomposition below is generic, but the **regrouping** of the
emitted ledger — which is ordered by row and table — into per-location chains is not. Which accesses
belong to which chain is determined by the addresses in the messages, so it is a fact about the
trace rather than about any chip, and it is supplied rather than derived. That is a different kind
of premise from State's, and the docstring on `memoryLedger_perm_handoff` says so. -/

/-- **The Memory bus's ledger, decomposed.** The decoded instruction rows' accesses, then the three
boundary tables' — memory-init, memory-finalize, and MemoryBump.

The per-row terms stay folded. That is deliberate and it is what
`TypedMemoryBalance.typedEnsembleMemoryInteractions_eq` does too: unlike State, whose emission shape
is uniform across all twenty-five chips, Memory's is family-typed by design, so there is no single
closed form to expand into. Nothing downstream needs one — a hand-off asks that accesses pair off,
not what any particular row's look like. -/
theorem memoryLedger_eq (trace : SupportedCoreTraceWitness p) :
    trace.memoryLedger =
      ((decodedInstructionRows (p := p) trace.witness.tables).flatMap fun decoded =>
        (decoded.interactionsWith trace.witness.data (Channels.memoryChannel (p := p))).map
          fun i => Interaction.toAccess i.raw) ++
      (((typedTableInteractionsWith (memoryInitProviderTable trace.witness) trace.witness.data
            (Channels.memoryChannel (p := p))).map fun i => Interaction.toAccess i.raw) ++
        (((typedTableInteractionsWith (memoryFinalizeProviderTable trace.witness) trace.witness.data
              (Channels.memoryChannel (p := p))).map fun i => Interaction.toAccess i.raw) ++
          (((typedTableInteractionsWith (memoryBumpTable trace.witness) trace.witness.data
              (Channels.memoryChannel (p := p))).map fun i => Interaction.toAccess i.raw) ++
            (((typedTableInteractionsWith (haltTable trace.witness) trace.witness.data
              (Channels.memoryChannel (p := p))).map fun i => Interaction.toAccess i.raw) ++
              ((typedTableInteractionsWith (syscallInstrsTable trace.witness) trace.witness.data
                (Channels.memoryChannel (p := p))).map fun i => Interaction.toAccess i.raw))))) := by
  rw [memoryLedger_eq_channelLedger, ← typedEnsembleInteractionsWith_raw,
    typedEnsembleMemoryInteractions_eq]
  simp only [List.map_append, List.map_map, Function.comp_def,
    decodedWitnessMemoryInteractions_eq_flatMap, List.map_flatMap]


omit [Fact (2 ^ 24 < p)] in
/-- **The Memory bus's ledger is its records' complete lives**, given the per-location chains.

The Memory counterpart of `stateLedger_perm_handoff`, and the premise is a *different kind* of thing
— worth being explicit about rather than letting the symmetry of the statements hide it.

State's chain is a fact about adjacent rows supplied by the machine's ordered step relation.
Memory's `hregroup` is a **regrouping**: the
emitted ledger is ordered by row and table, while the chains are per location, and which access
belongs to which chain is determined by the addresses the messages carry. That is a fact about the
particular trace, not about any chip and not about the ISA, so it is supplied here rather than
derived.

`multiChainLedger_perm_handoff` is what makes the per-location structure cost nothing extra:
`handoff` distributes over concatenation, so independent chains compose without interacting.

Feeding `AIRCompleteness.balancedOn_of_handoff` is immediate — `memoryLedger` is by definition
`fullLedger.filter (kind = Memory)`, which is exactly the shape that theorem asks for. -/
theorem memoryLedger_perm_handoff (trace : SupportedCoreTraceWitness p)
    (chains : List (LookupKey × List (LookupKey × LookupKey) × LookupKey))
    (hchains : ∀ chain ∈ chains, IsHandoffChain chain.1 chain.2.1 chain.2.2)
    (hregroup : (active trace.memoryLedger).Perm (chains.flatMap chainLedger)) :
    (active trace.memoryLedger).Perm (handoff (chains.flatMap chainTokens)) :=
  hregroup.trans (multiChainLedger_perm_handoff chains hchains)

/-- The State bus stated the same way, for comparison at the call site: one chain rather than a
family, and its regrouping is `List.Perm.refl` because `active_stateLedger_eq` already delivers the
chain form. -/
theorem stateLedger_perm_handoff_singleChain (trace : SupportedCoreTraceWitness p)
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
    (hsyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0)
    (hchain : IsHandoffChain (stateInitToken trace)
      (stateInstrLinks trace ++ stateBumpLinks trace) (stateFinalToken trace)) :
    (active trace.stateLedger).Perm
      (handoff (chainTokens (stateInitToken trace,
        stateInstrLinks trace ++ stateBumpLinks trace, stateFinalToken trace))) :=
  stateLedger_perm_handoff trace hbinary hbump hhalt hsyscall hchain

/-- **The State hand-off in chronological form.**

Instruction rows are physically stored table-by-table, and the StateBump table is a separate
physical table.  Neither order is the execution order.  A compiler therefore supplies its one
chronological link list together with the purely structural permutation which regroups the
physical instruction/bump links into it.  The semantic obligation is stated only on that
chronological list.

This is the State analogue of `memoryLedger_perm_handoff`: State has one chain rather than a family
of per-location chains, but it still needs an explicit physical-to-semantic regrouping. -/
theorem stateLedger_perm_handoff_chronological (trace : SupportedCoreTraceWitness p)
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow trace.witness.data row).is_real = 0 ∨
        (stateBumpRow trace.witness.data row).is_real = 1)
    (hhalt : ∀ row ∈ (haltTable trace.witness).table,
      (haltRow trace.witness.data row).is_real = 0)
    (hsyscall : ∀ row ∈ (syscallInstrsTable trace.witness).table,
      (syscallInstrsRow trace.witness.data row).is_real = 0)
    (links : List (LookupKey × LookupKey))
    (hregroup : (stateInstrLinks trace ++ stateBumpLinks trace).Perm links)
    (hchain : IsHandoffChain (stateInitToken trace) links (stateFinalToken trace)) :
    (active trace.stateLedger).Perm
      (handoff (chainTokens (stateInitToken trace, links, stateFinalToken trace))) := by
  have linkLedgerPerm :
      ((stateInstrLinks trace ++ stateBumpLinks trace).flatMap
          fun link => linkAccesses link.1 link.2).Perm
        (links.flatMap fun link => linkAccesses link.1 link.2) :=
    hregroup.flatMap fun _ _ => List.Perm.refl _
  rw [active_stateLedger_eq trace hbinary hbump hhalt hsyscall, List.append_assoc,
    ← List.flatMap_append]
  refine (linkLedgerPerm.append_left _).trans ?_
  exact (List.Perm.swap _ _ _).trans (chainLedger_perm_handoff _ _ _ hchain)


/-! ## The closure's nonpositivity premise, pointwise

`byteProgram_balanced` needs `hnonpos`: at every demanded key, the consumer skeleton's signed sum is
nonpositive. Without it `providerRecount`'s `Int.toNat` silently rounds a negative demand to zero
and the closure supplies nothing where something was needed.

Stated as an aggregate it is awkward — a sum over fifty-odd tables. Stated pointwise it is the
property that is actually true: **a consumer only ever pulls on a provider-supplied bus**, so every
Byte or Program access the skeleton emits carries multiplicity `-is_real ≤ 0`.

`ConsumersOnlyPull` is that pointwise form and `hnonpos_of_consumersOnlyPull` discharges the
aggregate from it.

**What deriving `ConsumersOnlyPull` itself would take, stated plainly.** It is not available from
Clean's channel bookkeeping: `channelsWithGuarantees` / `channelsWithRequirements` record which
channels a circuit owes *guarantees* and *requirements* on, not which polarity it emits with — a
circuit in neither list could still push. Nor is it available from the retired trace-level Byte
shadow, which carried the pre-W11 `+is_real` orientation rather than the live consumer pull.
What remains is the per-chip route `Proofs/Completeness/Closure.lean` describes and declines: for
eight of the twenty-five chips the Byte pulls descend through the `CPUState` reader and the
arithmetic operation subcircuits, so exposing them means extending each chip's `exposedChannels_eq`
lawfulness proof through those subcircuits.

Program is the cheap half — `Soundness/TypedProgram.lean`'s `supportedChip_programEmissionShape` is
proved 25/25 and gives each chip's single Program pull outright. Byte is the expensive half, and it
should be costed on its own rather than folded into this section's estimate. -/

/-- **Consumers only pull.** Every access the trace's consumer skeleton emits on a bus a preprocessed
provider supplies carries nonpositive multiplicity. -/
def ConsumersOnlyPull (trace : SupportedCoreTraceWitness p) : Prop :=
  ∀ a ∈ trace.skeletonLedger,
    SupportedCoreTraceWitness.preprocessedKey (LookupAccessList.keyOf a) = true →
    LookupAccessList.multOf a ≤ 0

omit [Fact (2 ^ 24 < p)] in
/-- The closure's aggregate premise, from the pointwise one. -/
theorem hnonpos_of_consumersOnlyPull (trace : SupportedCoreTraceWitness p)
    (h : ConsumersOnlyPull trace) :
    ∀ key ∈ trace.closingKeyList,
      LookupAccessList.multiplicitySum trace.skeletonLedger key ≤ 0 := by
  intro key hkey
  refine LookupAccessList.multiplicitySum_nonpos _ fun a ha hka => ?_
  exact h a ha (hka ▸ LookupAccessList.select_of_mem_closingKeys hkey)


end Trace

end SP1Clean.Soundness
