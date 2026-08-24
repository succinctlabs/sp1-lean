import SP1Clean.Model.CleanLedger
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.TypedState
import SP1Clean.Proofs.Completeness.ClosureRealization

/-!
# A built instruction table's State ledger

The instruction-chip counterpart of `ProviderTables.lean`. A provider table's ledger is one access
per row; an instruction table's is eight to twelve, spread across up to four buses — so the two need
different machinery, and this is the State half of it.

**Almost nothing here is per-chip, and that was the surprise.** Three facts already proved for all
twenty-five chips do the work:

* `<Chip>.traceTable_interactionsWith` (25/25) opens a built table into a `flatMap` over its rows;
* `Soundness/TypedState.lean`'s `supportedChip_stateEmissionShape` (25/25) says a row's State
  interactions are exactly the pull/push pair its `RowView` denotes — for *any* physical row array,
  which is what lets it apply to a row the trace layer built;
* `Model/CleanLedger.lean`'s `tableCleanAccesses_filterKind` restricts the whole-table ledger to one
  bus, its side condition discharged once by `EnsembleChannels.interactions_channel_eq_of_kindOf`.

So the State ledger of a built table is a theorem about an arbitrary `SupportedChip`, with no case
split over the registry. The Memory half will not be so lucky: its emission shapes are family-typed
by design, so that one really is an assembly of ten families.
-/

namespace SP1Clean.Soundness

open SP1Clean
open Air.Flat (Component Table)
open SP1Clean.Channels (stateChannel)
open LookupAccessList

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The two State accesses one built row contributes: the pull at its current state, the push at its
successor, both gated by the row's own selector. -/
noncomputable def rowStateAccesses (chip : SupportedChip p) (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) : LookupAccessList :=
  let row := chip.decodeRow data physical
  [Interaction.toAccess (stateChannel.pulledIfValue row.is_real (statePullMessage row)),
    Interaction.toAccess (stateChannel.pushedIfValue row.is_real (statePushMessage row))]

/-- A registered chip's component is one of the ensemble's tables. -/
theorem supportedChip_table_mem_allTables (chip : SupportedChip p)
    (hmem : chip ∈ supportedChips (p := p)) :
    chip.table ∈ (sp1Ensemble (p := p)).allTables := by
  rw [Air.Flat.Ensemble.allTables, List.mem_cons, sp1Ensemble_tables, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map_of_mem hmem))

/-! ## Decomposing the trace's State ledger

`stateLedger` is `fullLedger.filter (kind = State)`, and `fullLedger` is the verifier row's accesses
appended to a `flatMap` over the fifty-three tables. `List.filter` distributes over both, so the
bus's ledger is the per-table State halves — which is what turns the whole-trace obligation into
per-table content. -/

/-- One table's State half. -/
def tableStateLedger (table : Table (ZMod p)) : LookupAccessList :=
  (tableCleanAccesses table).filter fun a => a.1 = InteractionKind.State

/-- **A table that never names the State channel contributes nothing to it.** Twenty-six of the
twenty-eight provider tables are in this case — besides the instruction chips, only `StateBump` and
the verifier row touch the State bus at all. -/
theorem tableStateLedger_eq_nil (table : Table (ZMod p))
    (hcomponent : table.component ∈ (sp1Ensemble (p := p)).allTables)
    (hnot : (stateChannel (p := p)).toRaw ∉ table.component.circuit.channels) :
    tableStateLedger table = [] := by
  rw [tableStateLedger, tableCleanAccesses_filterKind _ (stateChannel (p := p)).toRaw
      InteractionKind.State rfl
      (interactions_channel_eq_of_kindOf _ hcomponent (stateChannel (p := p)).toRaw
        (by simp [sp1Ensemble_channels])),
    Air.Flat.Table.interactionsWith_nil_of_channel_not_mem hnot, List.map_nil]

/-- **Any table of a registered chip has that chip's pull/push pair per physical row** — however it
was built.

Stated over the table's own `table` rows rather than over a builder's inputs, which is strictly
better: it needs no `Table.build`/`Table.buildHinted` split (the seven hint-reading chips are
covered by the same statement), and it says the thing that is actually true — the State ledger is a
function of the *rows*, not of how they were produced.

Both side conditions are discharged from registry membership. -/
theorem tableStateLedger_eq_of_component (table : Table (ZMod p)) (chip : SupportedChip p)
    (hmem : chip ∈ supportedChips (p := p)) (hcomp : table.component = chip.table) :
    tableStateLedger table =
      table.table.flatMap fun row => rowStateAccesses chip table.data row := by
  have hcomponent : table.component ∈ (sp1Ensemble (p := p)).allTables :=
    hcomp ▸ supportedChip_table_mem_allTables chip hmem
  rw [tableStateLedger, tableCleanAccesses_filterKind _ (stateChannel (p := p)).toRaw
      InteractionKind.State rfl
      (interactions_channel_eq_of_kindOf _ hcomponent (stateChannel (p := p)).toRaw
        (by simp [sp1Ensemble_channels])),
    Air.Flat.Table.interactionsWith, List.map_flatMap]
  refine congrArg (List.flatMap · table.table) (funext fun row => ?_)
  rw [Air.Flat.Table.environment, hcomp,
    supportedChip_stateEmissionShape chip hmem table.data row]
  rfl


section Trace

variable [Fact (2 ^ 25 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- **The trace's State ledger is its tables' State halves**, verifier row first. -/
theorem stateLedger_eq_flatMap (trace : SupportedCoreTraceWitness p) :
    trace.stateLedger =
      tableStateLedger trace.skeletonVerifierTable ++
        trace.tables.flatMap tableStateLedger := by
  simp only [SupportedCoreTraceWitness.stateLedger, SupportedCoreTraceWitness.fullLedger,
    List.filter_append, tablesCleanAccesses, List.filter_flatMap]
  rfl





/-- **A bus's half of the trace's ledger IS that channel's evaluated interaction list.**

The bridge that makes the soundness layer's ensemble assemblies reusable here.
`Soundness/TypedState.lean` and `Soundness/TypedMemoryBalance.lean` already decompose
`typedEnsembleInteractionsWith witness channel` — State into the boundary pair plus the decoded
rows' and StateBump rows' pull/push pairs, Memory into the decoded rows' interactions plus the
init/finalize/bump tables'. Both are exactly the chain shape
`LookupAccessList.chainLedger_perm_handoff` consumes.

What was missing was only the change of orientation: those layers work in Clean `Interaction`s on
one channel, this one in `LookupAccess`es filtered from the whole computable ledger. Both sides are
`allTables.flatMap`, and per table the two agree by `tableCleanAccesses_filterKind`.

Stated for an arbitrary channel because the State and Memory halves need the identical fact —
writing it twice would have been the same proof with two names. -/
theorem busLedger_eq_channelLedger (trace : SupportedCoreTraceWitness p)
    (channel : RawChannel (ZMod p)) (hchannel : channel ∈ (sp1Ensemble (p := p)).channels)
    (K : InteractionKind) (hkind : kindOf channel.name = K) :
    trace.fullLedger.filter (fun a => a.1 = K) =
      (trace.witness.interactionsWith channel).map Interaction.toAccess := by
  rw [← trace.tablesCleanAccesses_allTables, tablesCleanAccesses, List.filter_flatMap,
    Air.Flat.EnsembleWitness.interactionsWith, List.map_flatMap]
  refine List.flatMap_congr fun table htable => ?_
  refine tableCleanAccesses_filterKind table channel K hkind fun i hi hk => ?_
  exact interactions_channel_eq_of_kindOf _ (trace.allTables_component_mem table htable)
    channel hchannel i hi (by rw [hk, hkind])

/-- The State instance. -/
theorem stateLedger_eq_channelLedger (trace : SupportedCoreTraceWitness p) :
    trace.stateLedger =
      (trace.witness.interactionsWith (stateChannel (p := p)).toRaw).map Interaction.toAccess :=
  busLedger_eq_channelLedger trace _ (by simp [sp1Ensemble_channels]) InteractionKind.State rfl

/-- The Memory instance — the same fact, and the reason the Memory half of the sweep is not the
ten-family assembly it looked like. -/
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
      signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1).map fun row =>
    (msgToken stateChannel
        (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable trace.witness) row)),
      msgToken stateChannel
        (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable trace.witness) row)))

theorem active_stateLedger_eq (trace : SupportedCoreTraceWitness p)
    (hbinary : ∀ d ∈ decodedInstructionRows (p := p) trace.witness.tables,
      (d.toChipRow trace.witness.data).is_real = 0 ∨
        (d.toChipRow trace.witness.data).is_real = 1)
    (hbump : ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1) :
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
      signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1 := by
    intro row hrow
    rcases hbump row hrow with h | h <;> rw [h]
    · exact Or.inl h0
    · exact Or.inr h1
  have hneg : ∀ (x : ZMod p), (x = 0 ∨ x = 1) → signedVal (-x) = -signedVal x := by
    intro x hx
    rw [signedVal_neg_is_real hp hx, signedVal_is_real hp hx]
  rw [show (decodedInstructionRows (p := p) trace.witness.tables).flatMap
      (fun a => [accessAt (msgToken stateChannel (statePullMessage (a.toChipRow trace.witness.data)))
          (signedVal (-(a.toChipRow trace.witness.data).is_real)),
        accessAt (msgToken stateChannel (statePushMessage (a.toChipRow trace.witness.data)))
          (signedVal (a.toChipRow trace.witness.data).is_real)])
      = (decodedInstructionRows (p := p) trace.witness.tables).flatMap
      (fun a => [accessAt (msgToken stateChannel (statePullMessage (a.toChipRow trace.witness.data)))
          (-signedVal (a.toChipRow trace.witness.data).is_real),
        accessAt (msgToken stateChannel (statePushMessage (a.toChipRow trace.witness.data)))
          (signedVal (a.toChipRow trace.witness.data).is_real)]) from
    List.flatMap_congr fun a ha => by rw [hneg _ (hbinary a ha)]]
  rw [show ((stateBumpTable trace.witness).table).flatMap
      (fun row => [accessAt (msgToken stateChannel
            (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable trace.witness) row)))
          (signedVal (-(stateBumpRow (stateBumpTable trace.witness) row).is_real)),
        accessAt (msgToken stateChannel
            (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable trace.witness) row)))
          (signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real)])
      = ((stateBumpTable trace.witness).table).flatMap
      (fun row => [accessAt (msgToken stateChannel
            (StateBumpChip.pulledMessage (stateBumpRow (stateBumpTable trace.witness) row)))
          (-signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real),
        accessAt (msgToken stateChannel
            (StateBumpChip.pushedMessage (stateBumpRow (stateBumpTable trace.witness) row)))
          (signedVal (stateBumpRow (stateBumpTable trace.witness) row).is_real)]) from
    List.flatMap_congr fun row hrow => by rw [hneg _ (hbump row hrow)]]
  rw [active_flatMap_gatedPair _ _ _ _ hgateInstr,
    active_flatMap_gatedPair _ _ _ _ hgateBump]
  simp only [stateInstrLinks, stateBumpLinks, stateInitToken, stateFinalToken,
    List.flatMap_map, active, List.filter_cons, multOf_accessAt, List.filter_nil]
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
      (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1)
    (hchain : IsHandoffChain (stateInitToken trace)
      (stateInstrLinks trace ++ stateBumpLinks trace) (stateFinalToken trace)) :
    (active trace.stateLedger).Perm
      (handoff (stateInitToken trace ::
        (stateInstrLinks trace ++ stateBumpLinks trace).map Prod.snd)) := by
  rw [active_stateLedger_eq trace hbinary hbump, List.append_assoc, ← List.flatMap_append]
  exact List.Perm.trans (List.Perm.swap _ _ _)
    (chainLedger_perm_handoff _ _ _ hchain)


end Trace

end SP1Clean.Soundness
