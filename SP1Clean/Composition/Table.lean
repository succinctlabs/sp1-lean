import SP1Clean.Faithful.ChipOracle
import SP1Clean.Model.CleanLedger
import ToClean.Air.TableBuild

/-! # Transporting an extracted Rust table to a native Clean table

The external PR #110 report's Finding 1: the Rust-faithfulness theorems and the Sail-soundness
capstone are two families that share an endpoint but are never composed inside Lean — `Faithful/`
is a leaf of the dependency graph, so nothing in the repository consumes a `ChipFaithful` proof.
This file is the first half of the composition: it turns a per-row faithfulness statement into a
per-**table** one, so a valid extracted table becomes a valid native `Air.Flat.Table` that the
soundness side can then read.

## What a `ChipFaithful` already gives, and what was missing

`ChipFaithful.constraints` says: for one Rust row, the Rust assertion list is all-zero **iff** the
codec's reconstructed native physical row satisfies the whole native circuit's `ConstraintsHold`.
`ChipFaithful.interactions` says the two active interaction multisets agree. Both are stated one
row at a time, at `NativeRowAssignment.environment` — an environment built from a bare `Array`.

What was missing is only plumbing, but it is the plumbing that makes the composition exist: Clean's
flat-AIR layer consumes a `Table`, whose `Constraints` quantify over `table.environment row`. Since
a transported table's `data` is the codec's `data` and its rows are the codec's rows, those two
environments are *definitionally* the same, and the whole per-table statement falls out row by row.

## Generic, deliberately

Nothing here mentions a chip. `transportTable` and its three theorems are stated over an arbitrary
`ChipRowCodec`/`ChipOracle`/`ChipFaithful` triple, so each of the twenty-five registered chips
instantiates them by supplying its own anchor — no per-chip proof, and no opportunity for
twenty-five copies to drift.

## Why the codec's codimension-1 image needs no repair

The external report's Finding 11 observes that for the six flag-hinted chips the faithfulness
codec covers only a codimension-1 slice of the native row space: `deconfigure` sets `is_real` to
the sum of the one-hot operation flags, so no native row whose `is_real` disagrees with its flag
sum is in the codec's image.

That is the right shape for every theorem stated here, and the reason is directional. Transport
runs extracted → native: it *starts* from a Rust row and *constructs* the native row through
`deconfigure`, so the constructed row satisfies the flag-sum relation by definition and the slice
is not a restriction on anything — it is where the construction lands. An image-forcing lemma
(every native solution equals `deconfigure` of some Rust row) would be needed only for a
native → Rust direction quantified over arbitrary native solutions, and no theorem in this
repository states that direction. `ChipFaithful.constraints` is an `↔` at a *given* row, not a
surjectivity claim, so it does not need one either.

## Scope

This is the table-level half. The ensemble-level transport assembles twenty-five transported
tables plus the provider and boundary segments into an `EnsembleWitness`. Its literal native
consumer recount derives Byte/Program balance; State/Memory balance remains an explicit global
translation obligation. The exact AIR's own ℕ-balance is useful evidence for that later
translation, but it does not directly balance a differently shaped reduced native slice; see
`docs/roadmap.md`.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime]

/-! The Clean access ledger (`tableCleanAccesses`, `tablesCleanAccesses` and their `Table.build`
closed forms) moved to `Model/CleanLedger.lean` in 2026-08 — its vocabulary is Clean tables plus this
repository's bus types, with no chip or oracle in it, so the Model stratum is where the placement law
puts it. Exported here, not redefined, so this file's call sites and the completeness layer's share
one definition. An `export` rather than an `abbrev`: `abbrev` is reducible and unfolds before the
rewrites below can match on the name. -/
export SP1Clean (tableCleanAccesses tablesCleanAccesses tablesCleanAccesses_append
  tableRustOrientedAccesses interactionToAccess_eval interactionToRustOrientedAccess_eval
  tableCleanAccesses_build tableCleanAccesses_build_map_singleton)

/-! ## Rust-facing orientation is only a stable partition

`Faithful.nativeAccesses` presents a row in State/Byte/Memory/Program/unexpected channel order and
dualizes the Memory and Program groups. The literal Clean ledger preserves emission order. The
following two lemmas make the previously implicit seam explicit: after applying the same
Memory/Program dualization to each literal Clean interaction, the two lists differ only by a
permutation. No interaction is added or discarded, including unexpected channels. -/

private theorem nativeAccesses_perm_map_toRustOrientedAccess
    (env : Environment (ZMod p)) (ops : Operations (ZMod p)) :
    (nativeAccesses env ops).Perm
      (ops.interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
  classical
  unfold nativeAccesses unexpectedInteractions Operations.interactionsWith
  generalize ops.interactions = interactions
  induction interactions with
  | nil => simp
  | cons interaction interactions ih =>
      simp only [List.map_map, Function.comp_def] at ih
      simp at ih
      let state := (interactions.filter
        (fun i => i.channel = Channels.stateChannel.toRaw)).map
          (AbstractInteraction.toAccess env)
      let byte := (interactions.filter
        (fun i => i.channel = Channels.byteChannel.toRaw)).map
          (AbstractInteraction.toAccess env)
      let memory := (interactions.filter
        (fun i => i.channel = Channels.memoryChannel.toRaw)).map fun i =>
          LookupAccessList.negMult (AbstractInteraction.toAccess env i)
      let program := (interactions.filter
        (fun i => i.channel = Channels.programChannel.toRaw)).map fun i =>
          LookupAccessList.negMult (AbstractInteraction.toAccess env i)
      let unexpected := (interactions.filter fun i =>
        !decide (i.channel = Channels.stateChannel.toRaw) &&
          (!decide (i.channel = Channels.byteChannel.toRaw) &&
            (!decide (i.channel = Channels.memoryChannel.toRaw) &&
              !decide (i.channel = Channels.programChannel.toRaw)))).map
                (AbstractInteraction.toAccess env)
      have ihNamed : (state ++ byte ++ memory ++ program ++ unexpected).Perm
          (interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
        simpa [state, byte, memory, program, unexpected, List.map_map,
          Function.comp_def] using ih
      by_cases hstate : interaction.channel = Channels.stateChannel.toRaw
      · simpa [hstate, AbstractInteraction.toRustOrientedAccess,
          Channels.stateChannel_eq_byteChannel_false,
          Channels.stateChannel_eq_memoryChannel_false,
          Channels.stateChannel_eq_programChannel_false, List.map_map, Function.comp_def] using
          ihNamed.cons (AbstractInteraction.toAccess env interaction)
      · by_cases hbyte : interaction.channel = Channels.byteChannel.toRaw
        · have ih' : (state ++ (byte ++ memory ++ program ++ unexpected)).Perm
              (interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
            simpa [List.append_assoc] using ihNamed
          simpa [hstate, hbyte, AbstractInteraction.toRustOrientedAccess,
            Channels.byteChannel_eq_stateChannel_false,
            Channels.byteChannel_eq_memoryChannel_false,
            Channels.byteChannel_eq_programChannel_false, state, byte, memory, program,
            unexpected, List.append_assoc, List.map_map, Function.comp_def] using
            ((List.perm_middle (l₁ := state)
              (l₂ := byte ++ memory ++ program ++ unexpected)).trans
              (ih'.cons (AbstractInteraction.toAccess env interaction)))
        · by_cases hmemory : interaction.channel = Channels.memoryChannel.toRaw
          · have ih' : ((state ++ byte) ++ (memory ++ program ++ unexpected)).Perm
                (interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
              simpa [List.append_assoc] using ihNamed
            simpa [hstate, hbyte, hmemory, AbstractInteraction.toRustOrientedAccess,
              Channels.memoryChannel_eq_stateChannel_false,
              Channels.memoryChannel_eq_byteChannel_false,
              Channels.memoryChannel_eq_programChannel_false, state, byte, memory, program,
              unexpected, List.append_assoc, List.map_map, Function.comp_def] using
              ((List.perm_middle (l₁ := state ++ byte)).trans
                (ih'.cons (LookupAccessList.negMult
                  (AbstractInteraction.toAccess env interaction))))
          · by_cases hprogram : interaction.channel = Channels.programChannel.toRaw
            · have ih' : (((state ++ byte) ++ memory) ++ (program ++ unexpected)).Perm
                  (interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
                simpa [List.append_assoc] using ihNamed
              simpa [hstate, hbyte, hmemory, hprogram,
                AbstractInteraction.toRustOrientedAccess,
                Channels.programChannel_eq_stateChannel_false,
                Channels.programChannel_eq_byteChannel_false,
                Channels.programChannel_eq_memoryChannel_false, state, byte, memory, program,
                unexpected, List.append_assoc, List.map_map, Function.comp_def] using
                ((List.perm_middle (l₁ := (state ++ byte) ++ memory)).trans
                  (ih'.cons (LookupAccessList.negMult
                    (AbstractInteraction.toAccess env interaction))))
            · have ih' : ((((state ++ byte) ++ memory) ++ program) ++ unexpected).Perm
                  (interactions.map (AbstractInteraction.toRustOrientedAccess env)) := by
                simpa [List.append_assoc] using ihNamed
              simpa [hstate, hbyte, hmemory, hprogram,
                AbstractInteraction.toRustOrientedAccess, List.append_assoc, List.map_map,
                Function.comp_def, state, byte, memory, program, unexpected] using
                ((List.perm_middle (l₁ := ((state ++ byte) ++ memory) ++ program)).trans
                  (ih'.cons (AbstractInteraction.toAccess env interaction)))

/-- Project all physical rows of a native table through the same complete access vocabulary used
by the whole-chip faithfulness anchors.  This definition is shared by row-for-row chip transports
and by the constructive provider redistributions. -/
noncomputable def tableNativeAccesses (table : Table (ZMod p)) : LookupAccessList :=
  table.table.flatMap fun row =>
    nativeAccesses (table.environment row) table.component.operations

/-- The faithfulness-facing table ledger is the literal evaluated Clean ledger with exactly the
Memory/Program polarity convention applied. `nativeAccesses`' channel grouping changes only order;
in particular, its unexpected tail neither drops nor invents an interaction. -/
theorem tableNativeAccesses_perm_tableRustOrientedAccesses (table : Table (ZMod p)) :
    (tableNativeAccesses table).Perm (tableRustOrientedAccesses table) := by
  classical
  unfold tableNativeAccesses tableRustOrientedAccesses Air.Flat.Table.interactions
  simp only [List.map_flatMap]
  apply List.Perm.flatMap (List.Perm.refl table.table)
  intro row _
  simpa only [Operations.interactionValues, List.map_map, Function.comp_def,
    interactionToRustOrientedAccess_eval] using
    nativeAccesses_perm_map_toRustOrientedAccess
      (table.environment row) table.component.operations

/-- Active filtering distributes over a list of whole-table ledgers while leaving each table's
component and operation tree opaque. -/
theorem active_flatMap_tableNativeAccesses (tables : List (Table (ZMod p))) :
    LookupAccessList.active (tables.flatMap tableNativeAccesses) =
      tables.flatMap fun table => LookupAccessList.active (tableNativeAccesses table) := by
  simp only [LookupAccessList.active, List.filter_flatMap]

/-- Row-wise form of one active whole-table ledger. -/
theorem active_tableNativeAccesses (table : Table (ZMod p)) :
    LookupAccessList.active (tableNativeAccesses table) =
      table.table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (table.environment row) table.component.operations) := by
  simp only [LookupAccessList.active, tableNativeAccesses, List.filter_flatMap]

/-- Erasing zero-multiplicity accesses commutes with the table and row concatenations without
unfolding any component's operation tree.  This folded bridge is the scalable form used by the
twenty-five-table instruction transport: unfolding `tableNativeAccesses` there asks `whnf` to
normalize every chip circuit at once. -/
theorem active_tablesNativeAccesses (tables : List (Table (ZMod p))) :
    LookupAccessList.active (tables.flatMap tableNativeAccesses) =
      tables.flatMap fun table =>
        table.table.flatMap fun row =>
          LookupAccessList.active
            (nativeAccesses (table.environment row) table.component.operations) := by
  simp only [LookupAccessList.active, tableNativeAccesses, List.filter_flatMap]

/-- Closed form for the native access list of an honestly built table.  Keeping this equation
beside `Table.build_table` avoids unfolding the complete witness generator in every provider
transport: only the per-input row projection remains. -/
theorem tableNativeAccesses_build (component : Component (ZMod p))
    (inputs : List (component.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    tableNativeAccesses (Table.build component inputs data hint) =
      inputs.flatMap fun input =>
        nativeAccesses
          (Environment.fromArray (component.buildRow input data hint) data)
          component.operations := by
  simp only [tableNativeAccesses, Table.build_table, List.flatMap_map,
    Table.build_environment, Table.build_component]

/-- Row-wise singleton specialization of `tableNativeAccesses_build`.  Provider components each
emit one bus access, so their whole-table transports reduce to one local access equation per
semantic source row. -/
theorem tableNativeAccesses_build_map_singleton
    {Row : Type} (component : Component (ZMod p)) (rows : List Row)
    (decode : Row → component.Input (ZMod p)) (access : Row → LookupAccess)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (rowAccess : ∀ row ∈ rows,
      nativeAccesses
          (Environment.fromArray (component.buildRow (decode row) data hint) data)
          component.operations = [access row]) :
    tableNativeAccesses (Table.build component (rows.map decode) data hint) =
      rows.map access := by
  rw [tableNativeAccesses_build]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [rowAccess row (by simp), ih (fun r hr => rowAccess r (by simp [hr]))]
    rfl

/-! `buildRow_input_get` and `eval_var_buildRow_input_get` moved to `Model/CleanLedger.lean` in
2026-08. Their vocabulary is Clean's `Component`/`ProvableType` and nothing else — no chip, no
oracle, no extracted row — so the placement law (`docs/layering.md`) puts them at the Model stratum,
where the completeness layer can also reach them. Exported, not redefined. -/
export SP1Clean (buildRow_input_get eval_var_buildRow_input_get)

/-! ## Single-channel access normalization -/

private theorem unexpectedInteractions_rowOperations_eq_nil_of_onlyChannel
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (channel : RawChannel (ZMod p))
    (known : channel = Channels.stateChannel.toRaw ∨
      channel = Channels.byteChannel.toRaw ∨
      channel = Channels.memoryChannel.toRaw ∨
      channel = Channels.programChannel.toRaw)
    (only : ∀ candidate ∈ circuit.channels, candidate = channel) :
    Faithful.unexpectedInteractions
        (⟨circuit⟩ : Component (ZMod p)).rowOperations = [] := by
  unfold Faithful.unexpectedInteractions
  apply List.filter_eq_nil_iff.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  intro unexpected
  have interactionMem' : interaction ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).interactions := by
    simpa only [Component.rowOperations_mk] using interactionMem
  have channelMem : interaction.channel ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem', rfl⟩
  have channelEq := only interaction.channel
    (circuit.channels_subset (varFromOffset Input 0) (size Input) channelMem)
  rcases known with known | known | known | known
  · exact unexpected.1 (channelEq.trans known)
  · exact unexpected.2.1 (channelEq.trans known)
  · exact unexpected.2.2.1 (channelEq.trans known)
  · exact unexpected.2.2.2 (channelEq.trans known)

private theorem interactionsWith_rowOperations_eq_nil_of_onlyChannel
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (onlyChannel channel : RawChannel (ZMod p))
    (only : ∀ candidate ∈ circuit.channels, candidate = onlyChannel)
    (different : channel ≠ onlyChannel) :
    Operations.interactionsWith channel
        (⟨circuit⟩ : Component (ZMod p)).rowOperations = [] := by
  unfold Operations.interactionsWith
  apply List.filter_eq_nil_iff.mpr
  intro interaction interactionMem
  simp only [decide_eq_true_eq]
  intro channelEq
  have interactionMem' : interaction ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).interactions := by
    simpa only [Component.rowOperations_mk] using interactionMem
  have channelMem : interaction.channel ∈
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).channels :=
    List.mem_map.mpr ⟨interaction, interactionMem', rfl⟩
  apply different
  rw [← channelEq]
  exact only interaction.channel
    (circuit.channels_subset (varFromOffset Input 0) (size Input) channelMem)

/-- If a circuit declares only the native Memory channel, its canonical Rust-facing access list is
exactly its Memory interaction list followed by the project-wide Memory polarity dualization.  The
proof uses the circuit's channel declaration rather than reopening interaction-free subcircuits. -/
theorem nativeAccesses_memoryOnly
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit (ZMod p) Input Output)
    (only : ∀ candidate ∈ circuit.channels,
      candidate = Channels.memoryChannel.toRaw)
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨circuit⟩ : Component (ZMod p)).rowOperations =
      (((⟨circuit⟩ : Component (ZMod p)).rowOperations.interactionsWith
        Channels.memoryChannel.toRaw).map (AbstractInteraction.toAccess env)).map
          LookupAccessList.negMult := by
  have stateNil := interactionsWith_rowOperations_eq_nil_of_onlyChannel circuit
    Channels.memoryChannel.toRaw Channels.stateChannel.toRaw only
    (of_eq_false Channels.stateChannel_eq_memoryChannel_false)
  have byteNil := interactionsWith_rowOperations_eq_nil_of_onlyChannel circuit
    Channels.memoryChannel.toRaw Channels.byteChannel.toRaw only
    (of_eq_false Channels.byteChannel_eq_memoryChannel_false)
  have programNil := interactionsWith_rowOperations_eq_nil_of_onlyChannel circuit
    Channels.memoryChannel.toRaw Channels.programChannel.toRaw only
    (of_eq_false Channels.programChannel_eq_memoryChannel_false)
  have unexpected := unexpectedInteractions_rowOperations_eq_nil_of_onlyChannel circuit
    Channels.memoryChannel.toRaw (Or.inr (Or.inr (Or.inl rfl))) only
  unfold Faithful.nativeAccesses
  rw [stateNil, byteNil, programNil, unexpected]
  simp only [List.map_nil, List.nil_append, List.append_nil]

/-- The centered integer representative vanishes exactly on the zero field element.  This is the
small structural fact that lets access transports erase multiplicity-zero padding without making
any bound assumption on nonzero multiplicities. -/
theorem signedVal_eq_zero_iff (value : ZMod p) : signedVal value = 0 ↔ value = 0 := by
  constructor
  · intro h
    have casted := congrArg (fun z : ℤ => (z : ZMod p)) h
    simpa only [intCast_signedVal, Int.cast_zero] using casted
  · rintro rfl
    simp [signedVal, ZMod.val_zero]

variable {Input NativeCols RustCols : TypeMap}
variable [ProvableStruct Input] [ProvableStruct NativeCols]
variable {circuit : GeneralFormalCircuit (ZMod p) Input NativeCols}
variable {codec : ChipRowCodec Input NativeCols circuit}
variable {oracle : ChipOracle (ZMod p) NativeCols RustCols}

/-- The native physical row an extracted Rust row transports to: deconfigure the Rust columns into
the chip's own native row type, then let the codec lay them out in Clean's input-first order. -/
def transportRow (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (rustCols : RustCols (ZMod p))
    (data : ProverData (ZMod p)) : Array (ZMod p) :=
  (codec.assignment (oracle.deconfigure rustCols) data).row

/-- The environment a transported row is read in is the one the faithfulness statement speaks
about. This is the whole bridge between `NativeRowAssignment.environment` and `Table.environment`:
both are `Environment.fromArray` of the same array at the same committed data. -/
theorem environment_transportRow (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (rustCols : RustCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Environment.fromArray (transportRow codec oracle rustCols data) data =
      (codec.assignment (oracle.deconfigure rustCols) data).environment := rfl

/-- **The transported table**: one native physical row per extracted Rust row, at the extracted
AIR's own committed prover data. -/
def transportTable (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) where
  component := ⟨circuit⟩
  width := (⟨circuit⟩ : Component (ZMod p)).width
  table := rustRows.map (transportRow codec oracle · data)
  data := data
  uniform_width := by
    intro row hrow
    obtain ⟨rustCols, -, rfl⟩ := List.mem_map.mp hrow
    exact (codec.assignment (oracle.deconfigure rustCols) data).width_eq

@[simp] theorem transportTable_component (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).component = ⟨circuit⟩ := rfl

@[simp] theorem transportTable_data (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).data = data := rfl

@[simp] theorem transportTable_table (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).table =
      rustRows.map (transportRow codec oracle · data) := rfl

/-- A transported table has exactly as many rows as the extracted table it came from — no padding
is introduced and none is dropped. -/
@[simp] theorem transportTable_length (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).length = rustRows.length :=
  List.length_map ..

/-! ## The two transported facts -/

/--
**A valid extracted table transports to a constraint-satisfying native table.**

The premise is exactly what the extracted AIR asserts of its own rows: every entry of the chip's
complete Rust `assertZeros` list is zero. The conclusion is Clean's `Table.Constraints` for the
native chip circuit — every `assertZero` of the whole flattened native circuit, gadget subcircuits
included, on every transported row.

This is the forward direction of `ChipFaithful.constraints`, lifted row-wise. The reverse direction
is available from the same anchor and is what a completeness-shaped transport would use.
-/
theorem transportTable_constraints
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    (transportTable codec oracle rustRows data).Constraints := by
  intro row hrow
  obtain ⟨rustCols, hmem, rfl⟩ := List.mem_map.mp hrow
  exact (faithful.constraints rustCols data).mp (valid rustCols hmem)

/-- **Per row, the transported table's active interactions are the extracted row's.** The native
circuit's whole interaction multiset — State, Byte, the dualized Memory and Program pulls, and any
unexpected-channel tail — permutes the Rust chip's, after dropping multiplicity-zero entries on
both sides. -/
theorem transportRow_accesses_perm
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustCols : RustCols (ZMod p)) (data : ProverData (ZMod p))
    (valid : List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    List.Perm
      (LookupAccessList.active
        (nativeAccesses (Environment.fromArray (transportRow codec oracle rustCols data) data)
          (⟨circuit⟩ : Component (ZMod p)).operations))
      (LookupAccessList.active (oracle.rustAccesses rustCols)) :=
  faithful.interactions rustCols data valid

/--
**The whole transported table's interaction multiset is the whole extracted table's.**

Concatenating the per-row permutations in row order. This is the form the ensemble-level balance
argument consumes: a channel's balance is a sum over the table's interactions, so a permutation of
the whole table's access list is exactly what transports a `balanceOf = 0` from one side to the
other.
-/
theorem transportTable_accesses_perm
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    List.Perm
      ((transportTable codec oracle rustRows data).table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data)
            (⟨circuit⟩ : Component (ZMod p)).operations))
      (rustRows.flatMap fun rustCols => LookupAccessList.active (oracle.rustAccesses rustCols)) := by
  rw [transportTable_table, List.flatMap_map]
  induction rustRows with
  | nil => simp
  | cons rustCols rest ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append
      (transportRow_accesses_perm faithful rustCols data (valid rustCols List.mem_cons_self))
      (ih fun c hc => valid c (List.mem_cons_of_mem _ hc))

/-- Folded whole-table form of `transportTable_accesses_perm`.  This is the composition-facing
statement: callers can concatenate many transported tables without normalizing their circuits. -/
theorem transportTable_activeAccesses_perm
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols)) :
    List.Perm
      (LookupAccessList.active
        (tableNativeAccesses (transportTable codec oracle rustRows data)))
      (rustRows.flatMap fun rustCols => LookupAccessList.active (oracle.rustAccesses rustCols)) := by
  rw [active_tableNativeAccesses]
  simpa only [Table.environment, transportTable_component, transportTable_data] using
    transportTable_accesses_perm faithful rustRows data valid

/-! ## Composing with the native soundness side

This is the point of the file. Clean's `Table.weakSoundness` turns a table's constraints into its
component's semantic `Spec` — for a chip, the `FormalModel/Contracts/Chips.lean` predicate saying
what the row *means*. Feeding a transported table into it composes the two theorem families the
external report found disconnected: extracted Rust validity on one side, the native chip's semantic
contract on the other, in one kernel-checked implication. -/

/--
**A valid extracted table's rows satisfy the native chip's semantic contract.**

The two extra premises are the ones Clean's soundness statement always carries and this file does
not attempt to discharge: the chip's honest-prover `Assumptions` on each transported row, and the
row's channel `Guarantees`. They are stated at the transported table rather than assumed of the
extracted one deliberately — an ensemble-level transport gets both from the extracted AIR's own
provider segment, which is where the facts actually live, and pushing them down to here would
misplace the obligation.
-/
theorem transportTable_spec
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols))
    (assumptions : (transportTable codec oracle rustRows data).Assumptions)
    (guarantees : (transportTable codec oracle rustRows data).Guarantees) :
    (transportTable codec oracle rustRows data).Spec :=
  (Table.weakSoundness assumptions
    (transportTable_constraints faithful rustRows data valid) guarantees).1

end SP1Clean.Composition
