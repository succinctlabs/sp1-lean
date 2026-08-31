import SP1Clean.Soundness.AIRCompleteness
import SP1CleanTest.Audit.JointNonVacuity

/-! # Non-vacuity of the machine-completeness hypothesis

`supported_core_generated_trace_complete` (`Soundness/AIRCompleteness.lean`) says every well-formed,
balanced, boundary-bound generated trace has a native ensemble witness satisfying
`SupportedCoreNativeRelation`. A completeness theorem is worth exactly as much as its hypothesis is
satisfiable, so this file exhibits a trace
that satisfies `SupportedCoreGeneratedTraceRelation` in full — the same question
`Audit/JointNonVacuity.lean` answers for the soundness side, asked of the converse relation.

## The trace

The **boundary-only shard**, generated: every instruction chip has zero events and zero padding,
most of the 29 provider tables are empty, and the shard's public endpoints are equal
(clk `(0, 1)`, pc `0x10000` at both ends), so the verifier's final-state pull and initial-state
push are the same State message and cancel.

Since W3's split-limb public values the verifier also pulls twelve Byte-bus range checks, so two
provider tables carry occurrences: the width-16 entry list supplies four `⟨1⟩` and six `⟨0⟩`
unit-count entries, and `providerOccurrences (.byte .u8Range)` supplies two `⟨0, 0⟩`
unit-count entries. Provider counts are now
explicit inputs, so this per-occurrence representation is a choice of this regression; the
hand-built sibling in `JointNonVacuity.lean` exercises the equivalent aggregated representation.

The Halt table is never empty: `ProviderTableId.Occurrence .halt = Empty`, so its occurrence list is
`[]` and `HaltChip.haltTraceInputs [] = [paddingInputs]` — the mandatory one padding row, whose
anti-gated `⟨0⟩` Exit push balances the verifier's ungated `⟨exit_code⟩` pull.  The generated table
is literally the hand-built `JointNonVacuity.haltPaddingTable` (`haltBuilt_eq`).

## What this witnesses, and what it does not

It witnesses that the hypothesis bundle of `supported_core_generated_trace_complete` is jointly satisfiable
— well-formedness, five-bus balance, the public-value match, and the semantic boundary binding, all
at the concrete prime with the committed one-instruction program. It does **not** witness a
non-empty generated shard itself. The sibling `ActiveTraceNonVacuity.lean` supplies one
hand-assembled JAL event with circuit-built physical rows and a balanced ledger; deriving such rows
from an arbitrary Sail execution, and a general trace generator that handles every event and bump
crossing, remain future work (`docs/roadmap.md`).
-/

namespace SP1Clean.Audit.TraceNonVacuity

open Air.Flat Circuit
open SP1Clean SP1Clean.TraceGenTests SP1Clean.Soundness
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel)
open SP1Clean.Audit.JointNonVacuity

/-! ## The generated boundary-only trace -/

/-- The prover hint the unhinted tables witness at. No table of this shard has a row that reads a
hint, so it is arbitrary. -/
def anchorHint : ProverHint (ZMod SP1Prime) := ProverHint.empty _

def width16 : RangeChip.Width := ⟨16, by norm_num⟩

def anchorRangeEntries (width : RangeChip.Width) : List TraceGen.RangeEntry :=
  if width = width16 then
    [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]
  else []

/-- The boundary-only shard routes no semantic event to any instruction table. -/
def anchorInstructionEvents : (id : InstructionChipId) → List id.Event := fun _ => []

/-- The boundary-only shard's provider occurrences, indexed by the physical provider registry. -/
def anchorProviderOccurrences : (id : ProviderTableId) → List id.Occurrence
  | .byte .u8Range => [⟨0, 0, 1⟩, ⟨0, 0, 1⟩]
  | .byte .msb => []
  | .byte .andByte => []
  | .byte .orByte => []
  | .byte .xorByte => []
  | .byte .ltu => []
  | .range width => anchorRangeEntries width
  | .program => []
  | .memoryInit => []
  | .memoryFinalize => []
  | .memoryBump => []
  | .stateBump => []
  | .halt => []

/--
**The boundary-only generated trace.** Twenty-five empty instruction tables, twenty-six empty
provider/boundary tables, the mandatory one-padding-row Halt table, and the two byte providers
whose occurrences cancel the verifier's
twelve range-check pulls exactly: four `⟨1⟩` and six `⟨0⟩` sixteen-bit occurrences (the split
public limbs — `init_clk_0_16 = final_clk_0_16 = 1`, `init_pc1 = final_pc1 = 1`, and the six
remaining limbs zero), and two `⟨0, 0⟩` byte-pair occurrences (the two `⟨3, 0, x, y⟩` pulls of the
middle clock limbs, both zero).
-/
def anchorTrace : SupportedCoreTraceWitness SP1Prime where
  instructionEvents := anchorInstructionEvents
  providerOccurrences := anchorProviderOccurrences
  data := anchorData
  hint := anchorHint
  boundary := boundaryInputs 1 65536 1 65536

theorem anchorTrace_rangeOccurrences (width : RangeChip.Width) :
    anchorTrace.providerOccurrences (.range width) = anchorRangeEntries width := rfl

/-- The trace's public boundary row is the joint anchor's public values: limbing clock `1` and pc
`0x10000` at both ends reproduces `pv` cell for cell. -/
theorem anchorTrace_publicValues : anchorTrace.publicValues = pv := by
  show boundaryInputs 1 65536 1 65536 = pv
  simp only [boundaryInputs, pv, SP1StateBoundary.mk.injEq]
  norm_num

/-! ## Well-formedness

Twenty-five vacuous conjuncts (no events), the unused provider widths, and the two byte
providers' occurrences: `⟨0, 0, 1⟩` is a byte pair and `⟨1, 1⟩`/`⟨0, 1⟩` fit in sixteen bits. -/

theorem anchorTrace_wellFormed : anchorTrace.WellFormed := by
  constructor
  · intro id e he
    cases id <;> simp [anchorTrace, anchorInstructionEvents] at he
  · intro id e he
    cases id with
    | byte provider =>
        cases provider <;>
          simp_all [anchorTrace, anchorProviderOccurrences, ProviderTableId.Valid,
            TraceGen.ByteEntry.WellFormed]
    | range width =>
        by_cases hwidth : width = width16
        · subst width
          simp only [anchorTrace, anchorProviderOccurrences, anchorRangeEntries] at he
          fin_cases he <;>
            norm_num [ProviderTableId.Valid, TraceGen.RangeEntry.WellFormed, width16]
        · have hocc : anchorTrace.providerOccurrences (.range width) = [] := by
            rw [anchorTrace_rangeOccurrences, anchorRangeEntries, if_neg hwidth]
            rfl
          rw [hocc] at he
          exact absurd he List.not_mem_nil
    | program | memoryInit | memoryFinalize | memoryBump | stateBump =>
        simp [anchorTrace, anchorProviderOccurrences] at he
    | halt => exact e.elim
  · exact boundaryInputs_limbBounds _ _ _ _

/-! ## The assembled tables

Fifty-one of the 54 are built from an empty occurrence list, so their row lists — and hence
their channel views — are literally `[]`. The two byte providers and the Halt table are named so
the balance argument can speak about them. -/

/-- The built `U8Range` table: two unit-count rows checking the byte pair `(0, 0)`. -/
def u8RangeBuilt : Table (ZMod SP1Prime) :=
  Table.build ByteChip.U8Range.component
    (ByteChip.U8Range.traceInputs
      (anchorTrace.providerOccurrences (.byte .u8Range))) anchorData anchorHint

/-- The built 16-bit `RangeChip` table: ten unit-count rows, four checking `a = 1` and six `a = 0`. -/
def range16Built : Table (ZMod SP1Prime) :=
  Table.build (RangeChip.componentFor width16)
    (RangeChip.traceInputs (anchorTrace.providerOccurrences (.range width16))) anchorData anchorHint

/-- The built Halt table: the mandatory single padding row (`Occurrence .halt = Empty`, so the
compiler emits no real halt rows and `haltTraceInputs [] = [paddingInputs]`). -/
def haltBuilt : Table (ZMod SP1Prime) :=
  Table.build HaltChip.component
    (HaltChip.haltTraceInputs (anchorTrace.providerOccurrences .halt)) anchorData anchorHint

/-- The generated Halt table **is** the soundness-side anchor's hand-built padding table: same
component, same width, and the same single all-zero row.  Every Halt fact proved there therefore
transfers verbatim. -/
theorem haltBuilt_eq : haltBuilt = haltPaddingTable :=
  Table.ext_iff.mpr ⟨rfl, rfl, by native_decide, rfl⟩

/-- One indexed range table is the named width-16 table or is physically empty. Keeping the
dependent occurrence projection folded makes this a stable rewrite boundary for `rangeTables`. -/
theorem anchorRangeBuilt_interactionsWith (width : RangeChip.Width)
    (ch : RawChannel (ZMod SP1Prime)) :
    (Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (anchorTrace.providerOccurrences (.range width)))
      anchorTrace.data anchorTrace.hint).interactionsWith ch =
        if width = width16 then range16Built.interactionsWith ch else [] := by
  by_cases hwidth : width = width16
  · subst width
    rfl
  · rw [if_neg hwidth]
    have hocc : anchorTrace.providerOccurrences (.range width) = [] := by
      rw [anchorTrace_rangeOccurrences, anchorRangeEntries, if_neg hwidth]
      rfl
    rw [hocc]
    rfl

/-- The same rewrite after the registry projection has reduced to its semantic range list. -/
theorem anchorRangeEntriesBuilt_interactionsWith (width : RangeChip.Width)
    (ch : RawChannel (ZMod SP1Prime)) :
    (Table.build (RangeChip.componentFor width)
      (RangeChip.traceInputs (anchorRangeEntries width)) anchorTrace.data anchorTrace.hint).interactionsWith
        ch = if width = width16 then range16Built.interactionsWith ch else [] := by
  by_cases hwidth : width = width16
  · subst width
    rfl
  · rw [if_neg hwidth]
    have hentries : anchorRangeEntries width = [] := by
      simp [anchorRangeEntries, hwidth]
    rw [hentries]
    rfl

/-- A table built from no occurrences contributes nothing to any channel. -/
theorem nilTable (c : Component (ZMod SP1Prime)) (ch : RawChannel (ZMod SP1Prime)) :
    (Table.build c [] anchorData anchorHint).interactionsWith ch = [] := rfl

/-- The dependent input type of an empty indexed Range table stays folded at the component
boundary, avoiding an unnecessary transparency conversion through `componentFor`. -/
theorem nilRangeTable (width : RangeChip.Width) (ch : RawChannel (ZMod SP1Prime)) :
    (Table.build (RangeChip.componentFor width) (RangeChip.traceInputs [])
      anchorData anchorHint).interactionsWith ch = [] := rfl

/-- The hinted sibling of `nilTable`. -/
theorem nilTableHinted (c : Component (ZMod SP1Prime)) (ch : RawChannel (ZMod SP1Prime)) :
    (Table.buildHinted c [] anchorData).interactionsWith ch = [] := rfl

/-- The assembled table list with every empty occurrence list already reduced to `[]` — one `rfl`,
which is what lets the channel split below be a single `simp only`. -/
theorem anchorTrace_tables_eq :
    anchorTrace.tables =
      [Table.build AddChip.component [] anchorData anchorHint,
       Table.build AddiChip.component [] anchorData anchorHint,
       Table.build AddwChip.component [] anchorData anchorHint,
       Table.build SubChip.component [] anchorData anchorHint,
       Table.build SubwChip.component [] anchorData anchorHint,
       Table.buildHinted BitwiseChip.component [] anchorData,
       Table.buildHinted LtChip.component [] anchorData,
       Table.buildHinted ShiftLeftChip.component [] anchorData,
       Table.buildHinted ShiftRightChip.component [] anchorData,
       Table.build JalChip.component [] anchorData anchorHint,
       Table.build JalrChip.component [] anchorData anchorHint,
       Table.buildHinted BranchChip.component [] anchorData,
       Table.build UTypeChip.component [] anchorData anchorHint,
       Table.build LoadByteChip.component [] anchorData anchorHint,
       Table.build LoadHalfChip.component [] anchorData anchorHint,
       Table.build LoadWordChip.component [] anchorData anchorHint,
       Table.build LoadDoubleChip.component [] anchorData anchorHint,
       Table.build LoadX0Chip.component [] anchorData anchorHint,
       Table.build StoreByteChip.component [] anchorData anchorHint,
       Table.build StoreHalfChip.component [] anchorData anchorHint,
       Table.build StoreWordChip.component [] anchorData anchorHint,
       Table.build StoreDoubleChip.component [] anchorData anchorHint,
       Table.buildHinted MulChip.component [] anchorData,
       Table.buildHinted DivRemChip.component [] anchorData,
       Table.build AluX0Chip.component [] anchorData anchorHint,
       u8RangeBuilt,
       Table.build ByteChip.MSB.component [] anchorData anchorHint,
       Table.build ByteChip.AndByte.component [] anchorData anchorHint,
       Table.build ByteChip.OrByte.component [] anchorData anchorHint,
       Table.build ByteChip.XorByte.component [] anchorData anchorHint,
       Table.build ByteChip.Ltu.component [] anchorData anchorHint
       ] ++ anchorTrace.rangeTables ++ [Table.build ProgramProviderChip.component [] anchorData anchorHint,
       Table.build MemoryProviderChip.component [] anchorData anchorHint,
       Table.build MemoryFinalizeChip.component [] anchorData anchorHint,
       Table.build MemoryBumpChip.component [] anchorData anchorHint,
       Table.build StateBumpChip.component [] anchorData anchorHint,
       haltBuilt] := rfl

/-- **The whole shard's channel view**: the verifier row followed by the two byte providers and the
Halt padding table, the fifty-one empty tables contributing nothing. -/
theorem anchorTrace_interactionsWith_split (ch : RawChannel (ZMod SP1Prime)) :
    anchorTrace.witness.interactionsWith ch =
      anchorTrace.witness.verifierTable.interactionsWith ch ++
        (u8RangeBuilt.interactionsWith ch ++
          (range16Built.interactionsWith ch ++ haltPaddingTable.interactionsWith ch)) := by
  show (anchorTrace.witness.verifierTable :: anchorTrace.tables).flatMap
    (·.interactionsWith ch) = _
  rw [List.flatMap_cons, anchorTrace_tables_eq]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, nilTable, nilTableHinted,
    haltBuilt_eq, List.nil_append, List.append_nil]
  simp [SupportedCoreTraceWitness.rangeTables, RangeChip.allWidths, List.finRange_succ,
    anchorRangeBuilt_interactionsWith, width16]

/-! ## The verifier row

The generated shard and the hand-built one of `JointNonVacuity.lean` commit the same public values
at the same prover data, and an ensemble's verifier row is determined by exactly those two — so the
two shards' verifier rows are the *same table*, and its four per-channel views transfer verbatim. -/

theorem anchorTrace_verifierTable : anchorTrace.witness.verifierTable = jointWitness.verifierTable :=
  Ensemble.verifierTable_ext rfl anchorTrace_publicValues rfl

/-! ## Five-bus balance -/

theorem u8RangeBuilt_channels :
    ∀ c ∈ u8RangeBuilt.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (ByteChip.U8Range.circuit (p := SP1Prime)).channels, c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, circuit_norm]

theorem range16Built_channels :
    ∀ c ∈ range16Built.component.circuit.channels, c = byteChannel.toRaw := by
  show ∀ c ∈ (RangeChip.circuitFor width16 (p := SP1Prime)).channels,
    c = byteChannel.toRaw
  simp [GeneralFormalCircuit.channels, RangeChip.circuitFor, RangeChip.circuit, circuit_norm]

theorem u8RangeBuilt_interactionsWith_nil {ch : RawChannel (ZMod SP1Prime)}
    (hne : ch ≠ byteChannel.toRaw) : u8RangeBuilt.interactionsWith ch = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hmem
  exact hne (u8RangeBuilt_channels _ hmem)

theorem range16Built_interactionsWith_nil {ch : RawChannel (ZMod SP1Prime)}
    (hne : ch ≠ byteChannel.toRaw) : range16Built.interactionsWith ch = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hmem
  exact hne (range16Built_channels _ hmem)

/-- The evaluated Byte-channel contribution of the generated shard, as one executable list: the
verifier row's twelve pulls, then the two providers' twelve unit-count pushes. -/
def byteInteractions : List (Interaction (ZMod SP1Prime)) :=
  (verifierBytePulls (varFromOffset SP1PublicIO 0)).map
      (AbstractInteraction.eval (Environment.fromInput pv anchorData)) ++
    (u8RangeBuilt.interactions ++ range16Built.interactions)

theorem anchorTrace_byteInteractions :
    anchorTrace.witness.interactionsWith byteChannel.toRaw =
      byteInteractions ++ haltPaddingTable.interactionsWith byteChannel.toRaw := by
  rw [anchorTrace_interactionsWith_split, anchorTrace_verifierTable, jointWitness_verifierByte,
    table_interactionsWith_eq_interactions u8RangeBuilt_channels,
    table_interactionsWith_eq_interactions range16Built_channels]
  simp only [byteInteractions, List.append_assoc]

/-- The shard's State view: the boundary pull/push pair, the byte providers silent, the Halt
padding row gated off. -/
theorem anchorTrace_stateInteractions :
    anchorTrace.witness.interactionsWith stateChannel.toRaw =
      [stateChannel.pulledIfValue 1
         ⟨pv.final_clk_high, pv.final_clk_low, pv.final_pc0, pv.final_pc1, pv.final_pc2⟩,
       stateChannel.pushedIfValue 1
         ⟨pv.init_clk_high, pv.init_clk_low, pv.init_pc0, pv.init_pc1, pv.init_pc2⟩] ++
        haltPaddingTable.interactionsWith stateChannel.toRaw := by
  rw [anchorTrace_interactionsWith_split, anchorTrace_verifierTable, jointWitness_verifierState,
    u8RangeBuilt_interactionsWith_nil (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    range16Built_interactionsWith_nil (of_eq_false Channels.stateChannel_eq_byteChannel_false),
    List.nil_append, List.nil_append]

theorem anchorTrace_programInteractions :
    anchorTrace.witness.interactionsWith programChannel.toRaw =
      haltPaddingTable.interactionsWith programChannel.toRaw := by
  rw [anchorTrace_interactionsWith_split, anchorTrace_verifierTable,
    jointWitness_verifierProgram_nil,
    u8RangeBuilt_interactionsWith_nil (of_eq_false Channels.programChannel_eq_byteChannel_false),
    range16Built_interactionsWith_nil (of_eq_false Channels.programChannel_eq_byteChannel_false),
    List.nil_append, List.nil_append, List.nil_append]

theorem anchorTrace_memoryInteractions :
    anchorTrace.witness.interactionsWith memoryChannel.toRaw =
      haltPaddingTable.interactionsWith memoryChannel.toRaw := by
  rw [anchorTrace_interactionsWith_split, anchorTrace_verifierTable,
    jointWitness_verifierMemory_nil,
    u8RangeBuilt_interactionsWith_nil (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    range16Built_interactionsWith_nil (of_eq_false Channels.memoryChannel_eq_byteChannel_false),
    List.nil_append, List.nil_append, List.nil_append]

/-- The shard's Exit view: the verifier's ungated `⟨0⟩` pull against the Halt padding row's two
pushes — the very list the hand-built anchor balances. -/
theorem anchorTrace_exitInteractions :
    anchorTrace.witness.interactionsWith exitChannel.toRaw = exitInteractions := by
  rw [anchorTrace_interactionsWith_split, anchorTrace_verifierTable, jointWitness_verifierExit,
    u8RangeBuilt_interactionsWith_nil (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    range16Built_interactionsWith_nil (of_eq_false Channels.exitChannel_eq_byteChannel_false),
    haltPaddingTable_exit, List.nil_append, List.nil_append]
  rfl

/-! ### Discharging the Halt padding row's gated-off tail

On the four non-Exit buses the Halt padding row appends only multiplicity-zero entries, which are
signed bits, are excluded from both `pushedMessages` and `pulledMessages`, and are at most nineteen
in number — so the ledger conditions reduce to the ones the shard already satisfied. -/

theorem pushedMessages_nil_of_mult_zero {l : List (Interaction (ZMod SP1Prime))}
    (h : ∀ i ∈ l, i.mult = 0) : Ledger.pushedMessages l = [] := by
  have hfilter : (l.filter fun i => decide (i.mult = 1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi hdec
    exact zero_ne_one (h i hi ▸ of_decide_eq_true hdec)
  rw [Ledger.pushedMessages, hfilter, List.map_nil]

theorem pulledMessages_nil_of_mult_zero {l : List (Interaction (ZMod SP1Prime))}
    (h : ∀ i ∈ l, i.mult = 0) : Ledger.pulledMessages l = [] := by
  have hfilter : (l.filter fun i => decide (i.mult = -1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi hdec
    exact (neg_ne_zero.mpr (one_ne_zero (α := ZMod SP1Prime))).symm
      (h i hi ▸ of_decide_eq_true hdec)
  rw [Ledger.pulledMessages, hfilter, List.map_nil]

/-- The shard's ledger conditions survive appending the Halt padding row's gated-off channel
view. -/
theorem balancedOn_append_halt {ch : RawChannel (ZMod SP1Prime)}
    {l : List (Interaction (ZMod SP1Prime))}
    (heq : anchorTrace.witness.interactionsWith ch = l ++ haltPaddingTable.interactionsWith ch)
    (hname : ch.name ≠ "SP1Exit") (hlen : l.length < 100) (hbin : Ledger.SignedMults l)
    (hperm : (Ledger.pushedMessages l).Perm (Ledger.pulledMessages l)) :
    anchorTrace.BalancedOn ch := by
  have hzero := haltPaddingTable_mult_zero hname
  refine anchorTrace.balancedOn_of_signed_perm ch ?_ ?_ ?_ <;> rw [heq]
  · have h19 := haltPaddingTable_interactionsWith_length ch
    have hp : (119 : ℕ) < SP1Prime := by norm_num [SP1Prime]
    rw [List.length_append]
    omega
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hbin i h
    · exact Or.inl (hzero i h)
  · rw [Ledger.pushedMessages_append, Ledger.pulledMessages_append,
      pushedMessages_nil_of_mult_zero hzero, pulledMessages_nil_of_mult_zero hzero,
      List.append_nil, List.append_nil]
    exact hperm

/-- **The generated shard's ledger balances on all five buses.**
LEDGERMARKState cancels because the public
endpoints are equal; Program and Memory carry only the Halt padding row's gated-off entries; Byte
and Exit are checked message-for-message on the concrete evaluated lists. -/
theorem anchorTrace_balanced : anchorTrace.Balanced := by
  intro channel hchannel
  rw [sp1Ensemble_channels] at hchannel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
  rcases hchannel with rfl | rfl | rfl | rfl | rfl
  · refine balancedOn_append_halt anchorTrace_stateInteractions
      (by simp only [Channel.toRaw_name, Channels.stateChannel]; decide) (by norm_num) ?_ ?_
    · intro i hi
      fin_cases hi <;> native_decide
    · native_decide
  · refine balancedOn_append_halt anchorTrace_byteInteractions
      (by simp only [Channel.toRaw_name, Channels.byteChannel]; decide) ?_ ?_ ?_
    · rw [show byteInteractions.length = 24 from by native_decide]
      norm_num
    · exact (by native_decide : ∀ i ∈ byteInteractions,
        i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)
    · native_decide
  · refine balancedOn_append_halt (l := [])
      (by rw [anchorTrace_programInteractions, List.nil_append])
      (by simp only [Channel.toRaw_name, Channels.programChannel]; decide) (by norm_num)
      (fun _ hi => absurd hi List.not_mem_nil) (List.Perm.refl _)
  · refine balancedOn_append_halt (l := [])
      (by rw [anchorTrace_memoryInteractions, List.nil_append])
      (by simp only [Channel.toRaw_name, Channels.memoryChannel]; decide) (by norm_num)
      (fun _ hi => absurd hi List.not_mem_nil) (List.Perm.refl _)
  · refine anchorTrace.balancedOn_of_signed_perm exitChannel.toRaw ?_ ?_ ?_ <;>
      rw [anchorTrace_exitInteractions]
    · rw [show exitInteractions.length = 3 from by native_decide]
      norm_num [SP1Prime]
    · exact (by native_decide : ∀ i ∈ exitInteractions,
        i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1)
    · native_decide


/-! ## The semantic boundary binding

The generated shard's Program-ROM and two memory-boundary tables are built from empty occurrence
lists, so the three provider bindings hold vacuously exactly as they do for the hand-built shard;
the remaining fields depend only on the committed prover data, the public values, and the concrete
initial Sail state, all of which the two shards share. -/

theorem anchorTrace_programProviderTable_nil :
    (programProviderTable (p := SP1Prime) anchorTrace.witness).table = [] := rfl

theorem anchorTrace_memoryInitProviderTable_nil :
    (memoryInitProviderTable (p := SP1Prime) anchorTrace.witness).table = [] := rfl

theorem anchorTrace_memoryFinalizeProviderTable_nil :
    (memoryFinalizeProviderTable (p := SP1Prime) anchorTrace.witness).table = [] := rfl

theorem anchorTrace_programProviderBound :
    ProgramProviderBound (p := SP1Prime) anchorTrace.witness := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, anchorTrace_programProviderTable_nil,
    List.flatMap_nil] at member
  exact absurd member List.not_mem_nil

theorem anchorTrace_memoryInitProviderBound :
    MemoryInitProviderBound (p := SP1Prime) anchorTrace.witness anchorState
      (Commit.initClkNat anchorData) := by
  intro interaction member _
  exfalso
  simp only [Table.interactionsWith, anchorTrace_memoryInitProviderTable_nil,
    List.flatMap_nil] at member
  exact absurd member List.not_mem_nil

theorem anchorTrace_memoryInitProviderUnique :
    MemoryInitProviderUnique (p := SP1Prime) anchorTrace.witness := by
  show (typedTableInteractionsWith (memoryInitProviderTable anchorTrace.witness)
    memoryChannel).Pairwise _
  rw [typedTableInteractionsWith, anchorTrace_memoryInitProviderTable_nil, List.flatMap_nil]
  exact List.Pairwise.nil

theorem anchorTrace_memoryFinalizeProviderUnique :
    MemoryFinalizeProviderUnique (p := SP1Prime) anchorTrace.witness := by
  show (typedTableInteractionsWith (memoryFinalizeProviderTable anchorTrace.witness)
    memoryChannel).Pairwise _
  rw [typedTableInteractionsWith, anchorTrace_memoryFinalizeProviderTable_nil, List.flatMap_nil]
  exact List.Pairwise.nil

/-- The generated shard's boundary bundle at the same concrete initial Sail state as the
soundness-side anchor. -/
theorem anchorTrace_boundaryFacts : InitialBoundaryFacts stmt anchorTrace.witness anchorState where
  programWellFormed := anchorProgram_wellFormed
  programCommitted := ⟨anchorData_canonicalEncoding, rfl⟩
  initialPc := anchorBoundaryFacts.initialPc
  initialClock := anchorBoundaryFacts.initialClock
  romLoaded := anchorState_romLoaded
  configured := anchorState_configured
  codeMemoryCompatible := anchor_codeMemoryCompatible
  programProvider := anchorTrace_programProviderBound
  memoryProvider := anchorTrace_memoryInitProviderBound
  memoryProviderUnique := anchorTrace_memoryInitProviderUnique
  memoryFinalizeProviderUnique := anchorTrace_memoryFinalizeProviderUnique

/-! ## The witness -/

/--
**Non-vacuity of the machine-completeness hypothesis.** The boundary-only generated shard satisfies
`SupportedCoreGeneratedTraceRelation` in full: every occurrence is well-formed, the five
buses balance (State by equal public endpoints, Byte message-for-message against the two built
providers, Exit against the mandatory Halt padding row, Program and Memory carrying only that row's
gated-off entries), the public boundary row is the statement's, and the
boundary tables bind to the committed one-instruction program and the concrete configured initial
Sail state.

So `supported_core_generated_trace_complete` is not vacuously true of an unsatisfiable relation, and
applying it to this trace yields a `SupportedCoreNativeRelation` witness — the generated twin of
`Audit/JointNonVacuity.lean`'s hand-built one.
-/
theorem generatedTraceRelation_nonvacuous :
    SupportedCoreGeneratedTraceRelation (p := SP1Prime) stmt anchorTrace :=
  ⟨anchorTrace_wellFormed, anchorTrace.witness_balancedChannels anchorTrace_balanced,
   anchorTrace_publicValues,
   anchorTrace_boundaryFacts.binding⟩

/-- The completeness capstone applied to the generated shard: a valid AIR witness exists. -/
theorem anchorTrace_yields_airWitness :
    ∃ airWitness, SupportedCoreNativeRelation (p := SP1Prime) stmt airWitness :=
  supported_core_generated_trace_complete stmt anchorTrace generatedTraceRelation_nonvacuous

end SP1Clean.Audit.TraceNonVacuity
