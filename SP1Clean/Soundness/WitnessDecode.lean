import SP1Clean.Soundness.ChipRegistry
import SP1Clean.Soundness.TypedInteractions
import Clean.Air.FlatComponent

/-! # Deterministic decoding of heterogeneous chip tables

The old whole-machine seam existentially chose a `List ChipRow` after flattening the Clean witness.
That made table order, dependent input/output types, and the selected prover data part of one opaque
proof obligation.  This module makes the data transformation executable and leaves only propositions
about the resulting rows to later grounding lemmas.

The typed circuit retained by `SupportedChip` is the key invariant: a decoded row is built directly
from that circuit's `Input` and `Output`, so no cast from an unrelated flat `Component` is involved.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

namespace SupportedChip

/-- Decode one physical table row with the descriptor's typed circuit and the ensemble's shared
prover data.  Width and constraint validity are propositions about this value, not preconditions to
constructing it. -/
noncomputable def decodeRow (chip : SupportedChip p) (data : ProverData (ZMod p))
    (row : Array (ZMod p)) : ChipRow p := by
  letI := chip.kind.provableInputs
  letI := chip.kind.provableCols
  let env := Environment.fromArray row data
  exact
    { kind := chip.kind
      inputs := chip.table.rowInput env
      cols := chip.table.rowOutput env }

/-- Decode every physical row of one chip table. -/
noncomputable def decodeTable (chip : SupportedChip p) (data : ProverData (ZMod p))
    (table : Table (ZMod p)) : List (ChipRow p) :=
  table.table.map (chip.decodeRow data)

@[simp] theorem decodeTable_length (chip : SupportedChip p) (data : ProverData (ZMod p))
    (table : Table (ZMod p)) :
    (chip.decodeTable data table).length = table.table.length := by
  simp [decodeTable]

@[simp] theorem decodeRow_kind (chip : SupportedChip p) (data : ProverData (ZMod p))
    (row : Array (ZMod p)) :
    (chip.decodeRow data row).kind = chip.kind := rfl

/-- The input projection of a decoded row is the retained component's typed input projection.
Keeping this theorem generic avoids reducing a concrete completed circuit at dependent call sites. -/
theorem decodeRow_inputs (chip : SupportedChip p) (data : ProverData (ZMod p))
    (row : Array (ZMod p)) :
    (chip.decodeRow data row).inputs =
      chip.table.rowInput (Environment.fromArray row data) := rfl

/-- Output companion to `decodeRow_inputs`. -/
theorem decodeRow_cols (chip : SupportedChip p) (data : ProverData (ZMod p))
    (row : Array (ZMod p)) :
    (chip.decodeRow data row).cols =
      chip.table.rowOutput (Environment.fromArray row data) := rfl

/-- The decoded row's semantic predicate is definitionally the typed circuit predicate registered by
the descriptor. -/
theorem decodeRow_chipSpec_iff (chip : SupportedChip p) (data : ProverData (ZMod p))
    (row : Array (ZMod p)) :
    (chip.decodeRow data row).chipSpec data ↔
      @GeneralFormalCircuit.Spec (ZMod p) chip.kind.Inputs chip.kind.Cols inferInstance
        chip.kind.provableInputs chip.kind.provableCols chip.circuit
        (chip.decodeRow data row).inputs (chip.decodeRow data row).cols data := by
  change chip.kind.chipSpec _ _ data ↔ _
  rw [← chip.spec_eq]

end SupportedChip

/-- One physical instruction-table row with its dependent supported-chip descriptor retained.  The
row's semantic `ChipRow` and its channel interactions are both evaluated from this single source, so
later grounding cannot pair a semantic row with emissions from another circuit or physical row. -/
structure DecodedInstructionRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  chip : SupportedChip p
  physical : Array (ZMod p)

namespace DecodedInstructionRow

/-- The environment used by both the typed decoder and the circuit's actual interactions. -/
def environment (row : DecodedInstructionRow p) (data : ProverData (ZMod p)) :
    Environment (ZMod p) :=
  Environment.fromArray row.physical data

/-- The heterogeneous semantic row decoded by the same dependent circuit. -/
noncomputable def toChipRow (row : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) : ChipRow p :=
  row.chip.decodeRow data row.physical

/-- The exact evaluated interactions of this physical row on a typed channel. -/
noncomputable def interactionsWith {Message : TypeMap} [ProvableType Message]
    (row : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (channel : Channel (ZMod p) Message) : List (TypedInteraction channel) :=
  typedInteractionValuesWith row.chip.table.operations channel (row.environment data)

@[simp] theorem interactionsWith_raw {Message : TypeMap} [ProvableType Message]
    (row : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (channel : Channel (ZMod p) Message) :
    (row.interactionsWith data channel).map TypedInteraction.raw =
      row.chip.table.operations.interactionValuesWith channel.toRaw (row.environment data) := by
  simp [interactionsWith]

@[simp] theorem toChipRow_kind (row : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (row.toChipRow data).kind = row.chip.kind := rfl

/-- The semantic view of a decoded row, exposed without unfolding either the dependent decoder or
the retained circuit at a concrete environment.  Chip-specific grounding proofs rewrite this once
and then use their descriptor's small `kind.view` projection lemmas. -/
theorem toChipRow_view (row : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (row.toChipRow data).view =
      row.chip.kind.view (row.chip.table.rowInput (row.environment data))
        (row.chip.table.rowOutput (row.environment data)) := rfl

/-- The optional RAM projection of a decoded row, exposed through the same folded decoder
interface as `toChipRow_view`. Memory-chip grounding uses this theorem to specialize a concrete
descriptor without forcing Lean to unfold the heterogeneous `decodeRow` value. -/
theorem toChipRow_ramAccess (row : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) :
    (row.toChipRow data).ramAccess =
      row.chip.kind.ramAccess (row.chip.table.rowInput (row.environment data))
        (row.chip.table.rowOutput (row.environment data)) := rfl

end DecodedInstructionRow

/-- Decode corresponding supported-chip/table pairs while retaining each physical row. -/
noncomputable def decodeInstructionTables :
    List (SupportedChip p) → List (Table (ZMod p)) → List (DecodedInstructionRow p)
  | chip :: chips, table :: tables =>
      table.table.map (⟨chip, ·⟩) ++ decodeInstructionTables chips tables
  | _, _ => []

/-- The canonical physical instruction rows of the stable first 25 witness tables. -/
noncomputable def decodedInstructionRows (tables : List (Table (ZMod p))) :
    List (DecodedInstructionRow p) :=
  decodeInstructionTables (supportedChips (p := p)) (tables.take 25)

/-- A positional chip/table alignment strong enough to identify the decoder's emissions with the
actual Clean table emissions.  `EnsembleWitness.same_circuits` and `same_data` establish this for the
first 25 instruction tables. -/
def InstructionTablesAligned (data : ProverData (ZMod p))
    (chips : List (SupportedChip p)) (tables : List (Table (ZMod p))) : Prop :=
  List.Forall₂ (fun chip table => table.component = chip.table ∧ table.data = data) chips tables

/-- A decoded row inherits the constraints of the exact physical table row from which it was built.
The positional alignment pins both the dependent circuit and shared prover data, so this theorem does
not cast between unrelated flat components or reconstruct a second environment. -/
theorem constraints_of_mem_decodeInstructionTables (data : ProverData (ZMod p)) :
    ∀ {chips : List (SupportedChip p)} {tables : List (Table (ZMod p))},
      InstructionTablesAligned data chips tables →
      (∀ table ∈ tables, table.Constraints) →
      ∀ decoded ∈ decodeInstructionTables chips tables,
        decoded.chip.table.operations.ConstraintsHold (decoded.environment data) := by
  intro chips tables aligned tableConstraints decoded decodedMem
  induction aligned with
  | nil => simp [decodeInstructionTables] at decodedMem
  | @cons chip table chips tables head _ ih =>
      rw [decodeInstructionTables, List.mem_append] at decodedMem
      rcases decodedMem with decodedMem | decodedMem
      · simp only [List.mem_map] at decodedMem
        obtain ⟨physical, physicalMem, rfl⟩ := decodedMem
        have holds := tableConstraints table List.mem_cons_self physical physicalMem
        simp only [DecodedInstructionRow.environment]
        rw [← head.1, ← head.2]
        exact holds
      · exact ih
          (fun other otherMem => tableConstraints other (List.mem_cons_of_mem table otherMem))
          decodedMem

/-- A decoded row inherits a channel guarantee from the exact physical table row from which it was
built.  This is the channel-generic twin of `constraints_of_mem_decodeInstructionTables`; Byte and
Program grounding use the same positional decoder rather than reconstructing table indices. -/
theorem channelGuarantees_of_mem_decodeInstructionTables (data : ProverData (ZMod p))
    (channel : RawChannel (ZMod p)) :
    ∀ {chips : List (SupportedChip p)} {tables : List (Table (ZMod p))},
      InstructionTablesAligned data chips tables →
      (∀ table ∈ tables, table.ChannelGuarantees channel) →
      ∀ decoded ∈ decodeInstructionTables chips tables,
        decoded.chip.table.operations.ChannelGuarantees channel (decoded.environment data) := by
  intro chips tables aligned tableGuarantees decoded decodedMem
  induction aligned with
  | nil => simp [decodeInstructionTables] at decodedMem
  | @cons chip table chips tables head _ ih =>
      rw [decodeInstructionTables, List.mem_append] at decodedMem
      rcases decodedMem with decodedMem | decodedMem
      · simp only [List.mem_map] at decodedMem
        obtain ⟨physical, physicalMem, rfl⟩ := decodedMem
        have guarantees := tableGuarantees table List.mem_cons_self physical physicalMem
        simp only [DecodedInstructionRow.environment]
        rw [← head.1, ← head.2]
        exact guarantees
      · exact ih
          (fun other otherMem => tableGuarantees other (List.mem_cons_of_mem table otherMem))
          decodedMem

/-- All typed interactions emitted by a positionally decoded instruction-table batch. -/
noncomputable def decodedInstructionInteractionsWith {Message : TypeMap} [ProvableType Message]
    (data : ProverData (ZMod p)) (chips : List (SupportedChip p))
    (tables : List (Table (ZMod p))) (channel : Channel (ZMod p) Message) :
    List (TypedInteraction channel) :=
  (decodeInstructionTables chips tables).flatMap fun row => row.interactionsWith data channel

/-- Aligned decoded rows emit exactly the actual typed interactions of their Clean tables. -/
theorem decodedInstructionInteractionsWith_eq_tables {Message : TypeMap} [ProvableType Message]
    (data : ProverData (ZMod p)) (channel : Channel (ZMod p) Message) :
    ∀ {chips : List (SupportedChip p)} {tables : List (Table (ZMod p))},
      InstructionTablesAligned data chips tables →
      decodedInstructionInteractionsWith data chips tables channel =
        tables.flatMap (typedTableInteractionsWith · channel) := by
  intro chips tables aligned
  induction aligned with
  | nil => rfl
  | @cons chip table chips tables head _ ih =>
      have headEq :
          table.table.flatMap (fun physical =>
            (DecodedInstructionRow.mk chip physical).interactionsWith data channel) =
            typedTableInteractionsWith table channel := by
        unfold typedTableInteractionsWith
        apply List.flatMap_congr
        intro physical physicalMem
        simp only [DecodedInstructionRow.interactionsWith,
          DecodedInstructionRow.environment]
        rw [← head.1, ← head.2]
        rfl
      simp only [decodedInstructionInteractionsWith, decodeInstructionTables,
        List.flatMap_append, List.flatMap_map]
      rw [headEq]
      change typedTableInteractionsWith table channel ++
          decodedInstructionInteractionsWith data chips tables channel = _
      rw [ih]
      rfl

/-- The stable 25-table specialization used by the native capstone. -/
noncomputable def decodedWitnessInstructionInteractionsWith {Message : TypeMap}
    [ProvableType Message] (data : ProverData (ZMod p)) (tables : List (Table (ZMod p)))
    (channel : Channel (ZMod p) Message) : List (TypedInteraction channel) :=
  decodedInstructionInteractionsWith data (supportedChips (p := p)) (tables.take 25) channel

/-- Decode corresponding descriptor/table pairs.  The ensemble witness proves that the two lists have
the same length; defining the transformation by recursion keeps it total and deterministic even before
that proof is supplied. -/
noncomputable def decodeChipTables (data : ProverData (ZMod p)) :
    List (SupportedChip p) → List (Table (ZMod p)) → List (ChipRow p)
  | chips, tables => (decodeInstructionTables chips tables).map (·.toChipRow data)

/-- The canonical heterogeneous instruction-row list decoded from an ensemble witness.  Provider and
boundary tables begin after the first 25 entries and intentionally produce no `ChipRow`. -/
noncomputable def decodedChipRows (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) : List (ChipRow p) :=
  (decodedInstructionRows (p := p) tables).map (·.toChipRow data)

@[simp] theorem decodedInstructionRows_toChipRows (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) :
    (decodedInstructionRows (p := p) tables).map (·.toChipRow data) =
      decodedChipRows data tables := rfl

/-- The active instruction rows of the canonical decode.  Padding remains part of the AIR table but
does not denote a Sail step; the ordering engine permutes exactly this filtered list. -/
noncomputable def realDecodedInstructionRows (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) : List (DecodedInstructionRow p) :=
  (decodedInstructionRows (p := p) tables).filter fun row => (row.toChipRow data).is_real = 1

/-- The active semantic rows after erasing the typed descriptors. -/
noncomputable def realDecodedChipRows (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) : List (ChipRow p) :=
  (decodedChipRows data tables).filter fun row => row.is_real = 1

/-- Erasing the retained descriptor after filtering active physical rows is exactly the old active
`ChipRow` decode.  Machine grounding should keep the left-hand representation until circuit
soundness has fired; this lemma is the explicit, lossless erasure boundary used by local execution. -/
@[simp] theorem realDecodedInstructionRows_toChipRows (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) :
    (realDecodedInstructionRows data tables).map (·.toChipRow data) =
      realDecodedChipRows data tables := by
  classical
  unfold realDecodedInstructionRows realDecodedChipRows decodedChipRows
  induction decodedInstructionRows (p := p) tables with
  | nil => rfl
  | cons decoded rows ih =>
      simp only [List.filter_cons, List.map_cons]
      split <;> simp_all

theorem mem_realDecodedChipRows_iff (data : ProverData (ZMod p))
    (tables : List (Table (ZMod p))) (row : ChipRow p) :
    row ∈ realDecodedChipRows data tables ↔
      row ∈ decodedChipRows data tables ∧ row.is_real = 1 := by
  simp [realDecodedChipRows]

theorem mem_kind_of_mem_decodeChipTables (data : ProverData (ZMod p)) :
    ∀ {chips : List (SupportedChip p)} {tables : List (Table (ZMod p))} {row : ChipRow p},
      row ∈ decodeChipTables data chips tables → row.kind ∈ chips.map (·.kind) := by
  intro chips tables row hrow
  simp only [decodeChipTables, List.mem_map] at hrow
  obtain ⟨decoded, decoded_mem, rfl⟩ := hrow
  induction chips generalizing tables with
  | nil => simp [decodeInstructionTables] at decoded_mem
  | cons chip chips ih =>
      cases tables with
      | nil => simp [decodeInstructionTables] at decoded_mem
      | cons table tables =>
          rw [decodeInstructionTables, List.mem_append] at decoded_mem
          rcases decoded_mem with decoded_mem | decoded_mem
          · simp only [List.map_cons, List.mem_cons]
            left
            simp only [List.mem_map] at decoded_mem
            obtain ⟨physical, -, rfl⟩ := decoded_mem
            rfl
          · exact List.mem_cons_of_mem _ (ih decoded_mem)

/-- A typed decoded row retains the exact descriptor from the corresponding input list.  Unlike the
`ChipRow.kind` projection below, this theorem preserves the circuit and routing metadata needed by
channel-emission contracts. -/
theorem mem_chip_of_mem_decodeInstructionTables :
    ∀ {chips : List (SupportedChip p)} {tables : List (Table (ZMod p))}
      {decoded : DecodedInstructionRow p},
      decoded ∈ decodeInstructionTables chips tables → decoded.chip ∈ chips := by
  intro chips tables decoded decodedMem
  induction chips generalizing tables with
  | nil => simp [decodeInstructionTables] at decodedMem
  | cons chip chips ih =>
      cases tables with
      | nil => simp [decodeInstructionTables] at decodedMem
      | cons table tables =>
          rw [decodeInstructionTables, List.mem_append] at decodedMem
          rcases decodedMem with decodedMem | decodedMem
          · simp only [List.mem_cons]
            left
            simp only [List.mem_map] at decodedMem
            obtain ⟨physical, -, rfl⟩ := decodedMem
            rfl
          · exact List.mem_cons_of_mem _ (ih decodedMem)

/-- Every row of the canonical typed decode carries one of the stable supported descriptors. -/
theorem decodedInstructionRows_chip_mem
    (tables : List (Table (ZMod p))) {decoded : DecodedInstructionRow p}
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) tables) :
    decoded.chip ∈ supportedChips (p := p) := by
  exact mem_chip_of_mem_decodeInstructionTables decodedMem

/-- Every deterministically decoded instruction row belongs to the audited semantic registry. -/
theorem decodedChipRows_kind_mem
    (data : ProverData (ZMod p)) (tables : List (Table (ZMod p))) {row : ChipRow p}
    (hrow : row ∈ decodedChipRows data tables) : row.kind ∈ allChipKinds (p := p) := by
  exact mem_kind_of_mem_decodeChipTables data hrow

/-- Active decoded rows inherit registry membership without a second routing list. -/
theorem realDecodedChipRows_kind_mem
    (data : ProverData (ZMod p)) (tables : List (Table (ZMod p))) {row : ChipRow p}
    (hrow : row ∈ realDecodedChipRows data tables) : row.kind ∈ allChipKinds (p := p) := by
  exact decodedChipRows_kind_mem data tables (mem_realDecodedChipRows_iff data tables row |>.mp hrow).1

end SP1Clean.Soundness
