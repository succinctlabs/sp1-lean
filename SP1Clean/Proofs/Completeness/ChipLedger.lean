import SP1Clean.Model.CleanLedger
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.TypedState
import SP1Clean.Proofs.Completeness.Assembly

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

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The two State accesses one built row contributes: the pull at its current state, the push at its
successor, both gated by the row's own selector. -/
noncomputable def rowStateAccesses (chip : SupportedChip p) (data : ProverData (ZMod p))
    (physical : Array (ZMod p)) : LookupAccessList :=
  let row := chip.decodeRow data physical
  [Interaction.toAccess (stateChannel.pulledIfValue row.is_real (statePullMessage row)),
    Interaction.toAccess (stateChannel.pushedIfValue row.is_real (statePushMessage row))]

/-- **A built instruction table's State ledger is its rows' pull/push pairs.**

The `honly` side condition is the ensemble's, not the chip's — it says the table emits only on
channels whose kinds are distinct, which `EnsembleChannels.interactions_channel_eq_of_kindOf`
supplies for every table of `sp1Ensemble`. -/
theorem stateLedger_build (chip : SupportedChip p) (hshape : StateEmissionShape chip)
    (inputs : List (chip.table.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (honly : ∀ i ∈ (Table.build chip.table inputs data hint).interactions,
      kindOf i.channel.name = InteractionKind.State →
        i.channel = (stateChannel (p := p)).toRaw) :
    (tableCleanAccesses (Table.build chip.table inputs data hint)).filter
        (fun a => a.1 = InteractionKind.State) =
      inputs.flatMap fun input =>
        rowStateAccesses chip data (chip.table.buildRow input data hint) := by
  rw [tableCleanAccesses_filterKind _ (stateChannel (p := p)).toRaw InteractionKind.State rfl
      honly,
    Table.build_interactions, List.map_flatMap]
  refine congrArg (List.flatMap · inputs) (funext fun input => ?_)
  rw [hshape data (chip.table.buildRow input data hint)]
  rfl


/-- A registered chip's component is one of the ensemble's tables. -/
theorem supportedChip_table_mem_allTables (chip : SupportedChip p)
    (hmem : chip ∈ supportedChips (p := p)) :
    chip.table ∈ (sp1Ensemble (p := p)).allTables := by
  rw [Air.Flat.Ensemble.allTables, List.mem_cons, sp1Ensemble_tables, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map_of_mem hmem))

/-- **The State ledger of any registered chip's built table**, with both side conditions discharged:
the emission shape from `supportedChip_stateEmissionShape`, the channel-kind condition from
`EnsembleChannels`. A caller supplies only registry membership.

This is the whole State half of the per-chip sweep. There is no case split, because the two facts it
composes are themselves registry-wide. -/
theorem stateLedger_build_of_mem (chip : SupportedChip p) (hmem : chip ∈ supportedChips (p := p))
    (inputs : List (chip.table.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (tableCleanAccesses (Table.build chip.table inputs data hint)).filter
        (fun a => a.1 = InteractionKind.State) =
      inputs.flatMap fun input =>
        rowStateAccesses chip data (chip.table.buildRow input data hint) :=
  stateLedger_build chip (supportedChip_stateEmissionShape chip hmem) inputs data hint
    (interactions_channel_eq_of_kindOf _ (supportedChip_table_mem_allTables chip hmem)
      (stateChannel (p := p)).toRaw (by simp [sp1Ensemble_channels]))

/-- The `buildHinted` companion, for the seven chips whose witness generation reads a per-row hint
(Bitwise, Lt, the two shifts, Branch, Mul, DivRem). Same three facts; only the table constructor
differs. -/
theorem stateLedger_buildHinted_of_mem (chip : SupportedChip p)
    (hmem : chip ∈ supportedChips (p := p))
    (inputs : List (chip.table.Input (ZMod p) × ProverHint (ZMod p)))
    (data : ProverData (ZMod p)) :
    (tableCleanAccesses (Table.buildHinted chip.table inputs data)).filter
        (fun a => a.1 = InteractionKind.State) =
      inputs.flatMap fun input =>
        rowStateAccesses chip data (chip.table.buildRow input.1 data input.2) := by
  rw [tableCleanAccesses_filterKind _ (stateChannel (p := p)).toRaw InteractionKind.State rfl
      (interactions_channel_eq_of_kindOf _ (supportedChip_table_mem_allTables chip hmem)
        (stateChannel (p := p)).toRaw (by simp [sp1Ensemble_channels])),
    Table.buildHinted_interactions, List.map_flatMap]
  refine congrArg (List.flatMap · inputs) (funext fun input => ?_)
  rw [supportedChip_stateEmissionShape chip hmem data (chip.table.buildRow input.1 data input.2)]
  rfl

end SP1Clean.Soundness
