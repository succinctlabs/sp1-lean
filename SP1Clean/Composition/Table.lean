import SP1Clean.Faithful.ChipOracle
import SP1Clean.Model.CleanLedger
import ToClean.Air.TableBuild

/-! # Transporting extracted Rust rows to native Clean tables

The retained Rust → Lean pipeline supplies migration evidence. `ChipFaithful` relates a complete
Rust assertion list and active interaction multiset to one reconstructed native row. This module
lifts that relation to physical tables and composes it with the native circuit's semantic proof.

A transported table stores rows only. Constraints, channel guarantees and ledgers take explicit
evaluation data; integrating the table into an ensemble must justify agreement with that ensemble's
canonical data. Construction data is not an independently committed table field.

Transport runs Rust → native and asserts no surjectivity onto native rows. The Memory/Program
orientation is a permutation followed by the declared polarity change. Multiplicity-zero entries
are erased only in explicitly active ledgers. Provider redistribution and global State/Memory
balance remain separate ensemble obligations. This evidence can be retired after Rust comparisons
replace its live proof consumers and conformance coverage.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime]

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

/-- Read a table through the whole-chip faithfulness vocabulary at explicit evaluation data. -/
noncomputable def tableNativeAccesses (table : Table (ZMod p))
    (data : ProverData (ZMod p)) : LookupAccessList :=
  table.table.flatMap fun row =>
    nativeAccesses (Environment.fromArray row data) table.component.operations

/-- Faithfulness grouping changes only ledger order, including the unexpected-channel tail. -/
theorem tableNativeAccesses_perm_tableRustOrientedAccesses (table : Table (ZMod p))
    (data : ProverData (ZMod p)) :
    (tableNativeAccesses table data).Perm (tableRustOrientedAccesses table data) := by
  classical
  unfold tableNativeAccesses tableRustOrientedAccesses Air.Flat.Table.interactions
  simp only [List.map_flatMap]
  apply List.Perm.flatMap (List.Perm.refl table.table)
  intro row _
  simpa only [Operations.interactionValues, List.map_map, Function.comp_def,
    interactionToRustOrientedAccess_eval] using
    nativeAccesses_perm_map_toRustOrientedAccess
      (Environment.fromArray row data) table.component.operations

/-- Active filtering distributes without unfolding a component's operation tree. -/
theorem active_flatMap_tableNativeAccesses (tables : List (Table (ZMod p)))
    (data : ProverData (ZMod p)) :
    LookupAccessList.active (tables.flatMap (tableNativeAccesses · data)) =
      tables.flatMap fun table => LookupAccessList.active (tableNativeAccesses table data) := by
  simp only [LookupAccessList.active, List.filter_flatMap]

/-- Row-wise form of one active whole-table ledger. -/
theorem active_tableNativeAccesses (table : Table (ZMod p)) (data : ProverData (ZMod p)) :
    LookupAccessList.active (tableNativeAccesses table data) =
      table.table.flatMap fun row =>
        LookupAccessList.active
          (nativeAccesses (Environment.fromArray row data) table.component.operations) := by
  simp only [LookupAccessList.active, tableNativeAccesses, List.filter_flatMap]

/-- Zero-multiplicity filtering commutes with both table and row concatenation. -/
theorem active_tablesNativeAccesses (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) :
    LookupAccessList.active (tables.flatMap (tableNativeAccesses · data)) =
      tables.flatMap fun table =>
        table.table.flatMap fun row =>
          LookupAccessList.active
            (nativeAccesses (Environment.fromArray row data) table.component.operations) := by
  simp only [LookupAccessList.active, tableNativeAccesses, List.filter_flatMap]

/-- Read constructed rows at evaluation data independent of their witness-generation data. -/
theorem tableNativeAccesses_build (component : Component (ZMod p))
    (inputs : List (component.Input (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p))
    (fixed : component.fixedRowsMatch (inputs.map (component.buildRow · data hint)))
    (evaluationData : ProverData (ZMod p)) :
    tableNativeAccesses (Table.build component inputs data hint fixed) evaluationData =
      inputs.flatMap fun input =>
        nativeAccesses
          (Environment.fromArray (component.buildRow input data hint) evaluationData)
          component.operations := by
  simp only [tableNativeAccesses, Table.build_table, List.flatMap_map, Table.build_component]

/-- Providers emitting one access per source row retain the complete row order and multiplicities. -/
theorem tableNativeAccesses_build_map_singleton
    {Row : Type} (component : Component (ZMod p)) (rows : List Row)
    (decode : Row → component.Input (ZMod p)) (access : Row → LookupAccess)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (fixed : component.fixedRowsMatch ((rows.map decode).map (component.buildRow · data hint)))
    (evaluationData : ProverData (ZMod p))
    (rowAccess : ∀ row ∈ rows,
      nativeAccesses
          (Environment.fromArray (component.buildRow (decode row) data hint) evaluationData)
          component.operations = [access row]) :
    tableNativeAccesses (Table.build component (rows.map decode) data hint fixed) evaluationData =
      rows.map access := by
  rw [tableNativeAccesses_build]
  clear fixed
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [rowAccess row (by simp), ih (fun r hr => rowAccess r (by simp [hr]))]
    rfl

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
        ({ circuit := circuit } : Component (ZMod p)).rowOperations = [] := by
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
        ({ circuit := circuit } : Component (ZMod p)).rowOperations = [] := by
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
        ({ circuit := circuit } : Component (ZMod p)).rowOperations =
      ((({ circuit := circuit } : Component (ZMod p)).rowOperations.interactionsWith
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
about: `Environment.fromArray` reads the same physical cells at the same explicit data. -/
theorem environment_transportRow (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols) (rustCols : RustCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Environment.fromArray (transportRow codec oracle rustCols data) data =
      (codec.assignment (oracle.deconfigure rustCols) data).environment := rfl

/-- **The transported table**: one native physical row per extracted Rust row, at the extracted
codec's generation data; evaluation data is supplied separately. -/
def transportTable (codec : ChipRowCodec Input NativeCols circuit)
    (oracle : ChipOracle (ZMod p) NativeCols RustCols)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p)) : Table (ZMod p) where
  component := { circuit := circuit }
  table := rustRows.map (transportRow codec oracle · data)
  uniform_width := by
    intro row hrow
    obtain ⟨rustCols, -, rfl⟩ := List.mem_map.mp hrow
    exact (codec.assignment (oracle.deconfigure rustCols) data).width_eq

@[simp] theorem transportTable_component (rustRows : List (RustCols (ZMod p)))
    (data : ProverData (ZMod p)) :
    (transportTable codec oracle rustRows data).component = { circuit := circuit } := rfl

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
    (transportTable codec oracle rustRows data).Constraints data := by
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
          ({ circuit := circuit } : Component (ZMod p)).operations))
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
            ({ circuit := circuit } : Component (ZMod p)).operations))
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
        (tableNativeAccesses (transportTable codec oracle rustRows data) data))
      (rustRows.flatMap fun rustCols => LookupAccessList.active (oracle.rustAccesses rustCols)) := by
  rw [active_tableNativeAccesses]
  simpa only [transportTable_component] using
    transportTable_accesses_perm faithful rustRows data valid

/-- Valid Rust rows satisfy the native semantic contract under the original circuit assumptions
and channel guarantees. These ordinary components use the circuit's assumptions directly, so
row soundness needs no separate fixed-column or data-consistency premise. -/
theorem transportTable_spec
    (faithful : ChipFaithful Input NativeCols RustCols circuit codec oracle)
    (rustRows : List (RustCols (ZMod p))) (data : ProverData (ZMod p))
    (valid : ∀ rustCols ∈ rustRows, List.Forall (· = 0) (oracle.assertZeros rustCols))
    (assumptions : (transportTable codec oracle rustRows data).Assumptions data)
    (guarantees : (transportTable codec oracle rustRows data).Guarantees data) :
    (transportTable codec oracle rustRows data).Spec data :=
by
  intro row member
  exact (Component.weakSoundness (assumptions row member)
    (transportTable_constraints faithful rustRows data valid row member) (guarantees row member)).1

end SP1Clean.Composition
