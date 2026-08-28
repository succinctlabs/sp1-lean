import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.ProviderBindings
import SP1Clean.Soundness.TimedGrounding
import SP1Clean.Soundness.LocalExecution
import SP1Clean.Soundness.RowSoundness
import SP1Clean.Soundness.TypedProgram
import SP1Clean.Soundness.TypedTimeContracts
import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.RefreshWiring

/-! # AIR witness relations and the semantic capstone

This module is the naming boundary the old trail capstone lacked:

* `SupportedCoreEnsembleRelation` is exactly the algebra checked by the 53-table Clean ensemble;
* `SP1SemanticBoundaryRelation` separately binds its preprocessed/provider rows to the committed
  program and a concrete local initial Sail state;
* `SupportedCoreNativeRelation` is their conjunction; and
* `SupportedCoreLocalExecutionRelation` is the finite official-Sail target for that slice.

The names `supported_core_air_sound` and `sp1_air_sound` are reserved for extracted upstream AIR
relations.  They are not declared over the native ensemble because doing so would conflate a Clean
implementation with its Rust-faithfulness theorem. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The private native-Clean witness currently implemented by this repository. -/
abbrev SupportedCoreNativeWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] :=
  EnsembleWitness (sp1Ensemble (p := p))

/-- The finite rollout surface left after the generic timed-grounding assembly is proved.  Every
field is a physical AIR fact: one contract bundle per registered chip, signed-binary Memory
multiplicities, and absence of active Memory messages on padding rows. -/
structure SupportedCoreGroundingObligations
    (witness : SupportedCoreNativeWitness p) : Prop where
  chipContracts : ∀ chip ∈ supportedChips (p := p), ChipGroundingContracts chip
  memoryMultiplicityBinary :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness Channels.memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1
  paddingMemoryEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
    (decoded.toChipRow witness.data).is_real ≠ 1 →
      decoded.producedMemoryMessages witness.data = [] ∧
        decoded.consumedMemoryMessages witness.data = []

/-- The finite rollout of the physical grounding contracts for all 25 entries of
`supportedChips`. The two structural Memory facts are derived from physical constraints, and every
chip case is discharged by its registry-facing `ChipGroundingContracts` bundle. -/
theorem supportedCore_groundingObligations_of_constraints
    (witness : SupportedCoreNativeWitness p) (constraints : witness.Constraints) :
    SupportedCoreGroundingObligations witness := by
  refine
    { chipContracts := ?_
      memoryMultiplicityBinary := witness_memoryMultiplicityBinary witness constraints
      paddingMemoryEmpty := witness_paddingMemoryEmpty witness constraints }
  intro chip chipMem
  fin_cases chipMem <;>
    first
    | exact addChip_groundingContracts
    | exact addiChip_groundingContracts
    | exact addwChip_groundingContracts
    | exact subChip_groundingContracts
    | exact subwChip_groundingContracts
    | exact bitwiseChip_groundingContracts
    | exact ltChip_groundingContracts
    | exact shiftLeftChip_groundingContracts
    | exact shiftRightChip_groundingContracts
    | exact mulChip_groundingContracts
    | exact divRemChip_groundingContracts
    | exact jalChip_groundingContracts
    | exact jalrChip_groundingContracts
    | exact branchChip_groundingContracts
    | exact uTypeChip_groundingContracts
    | exact loadByteChip_groundingContracts
    | exact loadHalfChip_groundingContracts
    | exact loadWordChip_groundingContracts
    | exact loadDoubleChip_groundingContracts
    | exact loadX0Chip_groundingContracts
    | exact storeByteChip_groundingContracts
    | exact storeHalfChip_groundingContracts
    | exact storeWordChip_groundingContracts
    | exact storeDoubleChip_groundingContracts
    | exact aluX0Chip_groundingContracts

/-- The raw algebraic relation checked by today's Clean ensemble.  It intentionally says nothing
about which program/provider contents the rows represent. -/
def SupportedCoreEnsembleRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    witness.publicInput = statement.publicValues ∧
    witness.Constraints ∧
    witness.BalancedChannels

/-- The non-execution companion relation: the program commitment and provider/boundary tables really
describe the caller's program and one concrete local initial Sail state. -/
def SP1SemanticBoundaryRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  SemanticBoundaryBinding

/-- The honest native relation used by semantic soundness. Provider truth is an explicit companion
predicate, not an implication smuggled out of raw interaction balance.

There is deliberately **no** third conjunct. The physical range premise SP1's generic RAM
access-timestamp comparison needs — a genuine 24-bit high limb on every pulled Memory record — used
to travel here as `SupportedCoreMemoryTimestampRangeRelation`, because the per-chip aligned-carrier
contract demanded it before producing the touch lists that the capstone's per-location memory
balance is built from. Moving that demand into the per-touch antecedent of the contract's slot
conjunct broke the cycle: `supportedCore_orderedRows_dynamic_of_obligations` now *derives* both
timestamp facts for every pulled record from the produced side of the widened balance
(`pushGood`/`pullGood`), so the capstone's remaining premises are exactly the ensemble algebra and
the semantic boundary binding. -/
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness

/-- The capacity-bounded native shard relation.

This is the ordinary native relation restricted in place; it does not introduce another native
witness or copy any constraint/boundary field.  It projects the physical active-row count into the
same `CoreProfile.WithinOrdinaryRowLimit` predicate used by the semantic relation. -/
def SupportedCoreNativeShardRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  SupportedCoreNativeRelation.restrict fun _ witness =>
    CoreProfile.WithinOrdinaryRowLimit
      (realDecodedInstructionRows witness.data witness.tables).length

/-! ## Native grounding and the local-execution capstone -/

/-- The exact output expected from the remaining witness-grounding proof.

This record cannot choose a convenient unrelated trace: `orderedRows` is a permutation of precisely
the active physical rows produced by the deterministic typed decoder.  Retaining each dependent
descriptor is essential: circuit soundness fires on that exact row before the local-execution engine
observes its semantic `ChipRow` projection.  The remaining fields order those rows between the public
PC endpoints, ground every row against the evolving official-Sail state, and bind the table row count
to the currently supported eight-tick clock window. -/
structure SupportedCoreGrounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (orderedRows : List (DecodedInstructionRow p)) : Prop where
  exhaustive : orderedRows.Perm (realDecodedInstructionRows witness.data witness.tables)
  walk : PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
    (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
      statement.publicValues.init_pc2)
    (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
      statement.publicValues.final_pc2)
    orderedRows
  grounded : RowsGrounded (fun decoded : DecodedInstructionRow p =>
      decoded.toChipRow witness.data)
    witness.data statement.program initial orderedRows
  clockCount :
    Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low +
        8 * orderedRows.length =
      Semantics.clkNat statement.publicValues.final_clk_high statement.publicValues.final_clk_low
  /-- The public **final** State message is semantically true: a real Sail chain from `initial`
  reaches a state at exactly the committed final clock whose PC is the committed final pc, with the
  ROM still loaded and the platform configuration intact.  This is `TimedGrounding.walk`'s second
  conclusion, previously proved and discarded (external report, Finding 4); the ROM/configuration
  persistence at the endpoint is what a cross-shard composition step consumes. -/
  finalStateTruth :
    Semantics.LocalStateTruth statement.program initial (Commit.initClkNat witness.data)
      (finalBoundaryStateMessage statement.publicValues)
  /-- Every memory-finalize provider record is true of the constructed run: some record at the same
  location with the same value and a no-later timestamp is genuinely the content of that location at
  its time (`TimedGrounding.walk`'s third conclusion, previously discarded — Finding 4).  Stated in
  the ∃-witness form deliberately: with MemoryBump timestamp-refresh rows in the ensemble the walk
  concludes truth for the *refresh-eliminated* record (same location and value, earlier time), and
  this statement absorbs that without changing shape.  On a shard with no active refresh row the
  witness is the record itself. -/
  memoryFinalizeTruth : ∀ loc m, memoryFinalizeFrontier witness loc = some m →
    ∃ m', Semantics.MemoryMsg.locOf m' = Semantics.MemoryMsg.locOf m ∧
      m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
      Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m'

/-- The committed-decode field of every statically grounded ordered row is already discharged.
This theorem deliberately sits beside the remaining grounding seam: Program truth comes entirely
from the exact chip pulls, Clean balance, the canonical Program provider at position 48, and the
statement binding;
it is not an assumption of the timed State/Memory induction. -/
theorem supportedCore_orderedRows_programDecoded
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {initial : SailState} (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables)) :
    ∀ decoded ∈ orderedRows,
      Target.decodedInROM statement.program
        (programAccess (decoded.toChipRow witness.data).view).toRow := by
  intro decoded decodedMem
  have sourceMem := exhaustive.mem_iff.mp decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at sourceMem
  simp only [decide_eq_true_eq] at sourceMem
  have truth := decoded.programTruth_of_active witness constraints balanced boundary.programProvider
    sourceMem.1 sourceMem.2
  have decodedTruth := truth.2
  rw [boundary.programCommitted.2] at decodedTruth
  simpa only [rowOfMsg_programMessageOfView] using decodedTruth

/-- Assemble every state-independent grounding field once per ordered row.  Activity and registry
membership follow from exhaustive deterministic decoding, while committed decode follows from the
Program provider and channel balance.  The semantic chip `Spec` is deliberately absent: its proof can
depend on the current Memory operands and therefore belongs to `DynamicGroundedRow`. -/
theorem supportedCore_orderedRows_static
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {initial : SailState} (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables)) :
    ∀ decoded ∈ orderedRows,
      StaticGroundedRow statement.program (decoded.toChipRow witness.data) := by
  intro decoded decodedMem
  have sourceMem := exhaustive.mem_iff.mp decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at sourceMem
  simp only [decide_eq_true_eq] at sourceMem
  exact {
    real := sourceMem.2
    registered := by
      change decoded.chip.kind ∈ allChipKinds (p := p)
      exact List.mem_map_of_mem
        (decodedInstructionRows_chip_mem witness.tables sourceMem.1)
    decoded := supportedCore_orderedRows_programDecoded statement witness constraints balanced
      boundary orderedRows exhaustive decoded decodedMem }

/-- A walk of **canonicalized** State edges projects to the pc-only walk consumed by local
execution: on rows whose edge endpoints carry genuine 16-bit upper pc limbs (the W3 goodness pack),
each endpoint's canonical image has the same 64-bit pc as the row's own columns
(`pcBits_canonState`), so the chaining transports verbatim onto `rcvPcOf`/`sndPcOf`. -/
theorem pcWalk_of_canonStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (fun decoded =>
        (canonState (decodedStateEdge data decoded).1,
         canonState (decodedStateEdge data decoded).2)) initial final rows →
      (∀ decoded ∈ rows,
        ((decodedStateEdge data decoded).1.pc1.val < 2 ^ 16 ∧
          (decodedStateEdge data decoded).1.pc2.val < 2 ^ 16) ∧
        ((decodedStateEdge data decoded).2.pc1.val < 2 ^ 16 ∧
          (decodedStateEdge data decoded).2.pc2.val < 2 ^ 16)) →
        PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow data)
          (Semantics.StateMsg.pcBits initial) (Semantics.StateMsg.pcBits final) rows := by
  intro initial final rows walk good
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      obtain ⟨⟨gp1, gp2⟩, hp1, hp2⟩ := good decoded List.mem_cons_self
      constructor
      · have hsrc := congrArg Semantics.StateMsg.pcBits source
        rw [pcBits_canonState gp1 gp2] at hsrc
        simpa [decodedStateEdge] using hsrc
      · have tailWalk := ih tail (fun d hd => good d (List.mem_cons_of_mem _ hd))
        rw [pcBits_canonState hp1 hp2] at tailWalk
        simpa [decodedStateEdge] using tailWalk

/-- A State-message walk with a row-dependent positive-width schedule has the expected endpoint
clock count.  No instruction class, fixed divisor, or concrete edge map is baked into this
telescoping theorem; the capstone instantiates it at the canonicalized decoded edge. -/
theorem clockCount_of_stateWalk_durations
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p))
    (duration : DecodedInstructionRow p → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + duration decoded) →
      Semantics.StateMsg.timeNat initial + (rows.map duration).sum =
        Semantics.StateMsg.timeNat final := by
  intro initial final rows walk steps
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      simp
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      have rowStep := steps decoded List.mem_cons_self
      have tailCount := ih tail (fun other otherMem =>
        steps other (List.mem_cons_of_mem decoded otherMem))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A State-message walk whose rows each advance eight ticks has the expected endpoint clock
count.  This is the ordinary-slice specialization of the row-dependent theorem above. -/
theorem clockCount_of_stateWalk
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + 8) →
      Semantics.StateMsg.timeNat initial + 8 * rows.length =
        Semantics.StateMsg.timeNat final := fun walk steps => by
  simpa [Nat.mul_comm] using clockCount_of_stateWalk_durations edge (fun _ => 8) walk steps

/-- The telescoping endpoint-multiset balance of a State walk: the head plus each row's push equals the
final plus each row's pull, as multisets.  The `List`-level companion of
`RankedGrounding.endpointBalanced_of_balanced`, derived directly from `IsWalk` so it carries the
`statement.publicValues` endpoints natively — the exact State-balance hypothesis `TimedGrounding.walk`
consumes (after mapping the canonicalized edge onto the walk carrier's `statePush`/`statePull`). -/
theorem endpointBalance_of_stateWalk
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      initial ::ₘ (↑(rows.map (fun d => (edge d).2)) :
          Multiset (Channels.StateMsg (ZMod p)))
        = final ::ₘ ↑(rows.map (fun d => (edge d).1)) := by
  intro initial final rows walk
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have ihEq := ih tail
      simp only [List.map_cons, Multiset.cons_coe, Multiset.coe_eq_coe] at ihEq ⊢
      rw [source]
      exact (List.Perm.cons initial ihEq).trans (List.Perm.swap final initial _)

/-- Locate a row in a State walk by the sum of all preceding row-dependent durations. -/
theorem statePullTime_of_stateWalk_durations
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p))
    (duration : DecodedInstructionRow p → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + duration decoded) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (edge decoded).1 =
          Semantics.StateMsg.timeNat initial + (done.map duration).sum := by
  intro initial final rows walk steps done
  induction done generalizing initial rows with
  | nil =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, -⟩ := walk
      simpa using congrArg Semantics.StateMsg.timeNat source
  | cons head done ih =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, tail⟩ := walk
      have headStep := steps head List.mem_cons_self
      have tailSteps : ∀ row ∈ done ++ decoded :: suffix,
          Semantics.StateMsg.timeNat (edge row).2 =
            Semantics.StateMsg.timeNat (edge row).1 + duration row := by
        intro row rowMem
        exact steps row (List.mem_cons_of_mem head rowMem)
      have position := ih tail tailSteps decoded suffix rfl
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The State walk and each chip's proved `+8` clock contract locate every exact decoded row at its
prefix length. This is the ordinary-slice specialization consumed by shard-local Memory currency. -/
theorem statePullTime_of_stateWalk
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + 8) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (edge decoded).1 =
          Semantics.StateMsg.timeNat initial + 8 * done.length :=
  fun walk steps done decoded suffix rowsEq => by
    simpa [Nat.mul_comm] using
      statePullTime_of_stateWalk_durations edge (fun _ => 8) walk steps done decoded suffix
        rowsEq

/-- Every row of the eight-tick State walk begins in the same residue class modulo eight as the
public initial State record.  This is the `RowOK.align8` input of the timed Memory walk. -/
theorem statePullAlign8_of_stateWalk
    (edge : DecodedInstructionRow p → Channels.StateMsg (ZMod p) × Channels.StateMsg (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk edge initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).2 =
          Semantics.StateMsg.timeNat (edge decoded).1 + 8) →
      ∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (edge decoded).1 % 8 =
          Semantics.StateMsg.timeNat initial % 8 := by
  intro initial final rows walk steps decoded decodedMem
  obtain ⟨done, suffix, rowsEq⟩ := List.append_of_mem decodedMem
  have position := statePullTime_of_stateWalk edge walk steps done decoded suffix rowsEq
  rw [position]
  omega

/-- Generic closure of the ordered-row dynamic seam.  The proof chooses each chip's aligned carrier,
eliminates the MemoryBump refresh edges from the widened memory balance (rewriting each affected
pull to its value-equal pre-refresh ancestor), canonicalizes the carrier's State edge, feeds the
seven explicit inputs of `TimedGrounding.walk`, transports its result back to the ordinary
physical-row carrier at value level, and invokes the chip's retained Clean soundness/Sail bridge.
What remains after this theorem is the finite `SupportedCoreGroundingObligations` rollout, not
another semantic premise.

`publicInputEq` is what identifies the walked State endpoints with the *verifier row's* public
values, whose limbs `witness_publicInput_limbBounds` range-checks: that is where the `< 2 ^ 48`
shard-time ceiling comes from, and hence every pushed Memory record's genuine 24-bit `clk_high` —
one of the two facts `memoryBump_isRefresh` consumes.  Its only caller,
`supported_core_witness_grounding`, already carries the same hypothesis. -/
theorem supportedCore_orderedRows_dynamic_of_obligations
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (publicInputEq : witness.publicInput = statement.publicValues)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (obligations : SupportedCoreGroundingObligations witness)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables))
    (stateWalk : Walk.IsWalk (fun decoded =>
        (canonState (decodedStateEdge witness.data decoded).1,
         canonState (decodedStateEdge witness.data decoded).2))
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows) :
    (∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state) ∧
      Semantics.LocalStateTruth statement.program initial (Commit.initClkNat witness.data)
        (finalBoundaryStateMessage statement.publicValues) ∧
      (∀ loc m, memoryFinalizeFrontier witness loc = some m →
        ∃ m', Semantics.MemoryMsg.locOf m' = Semantics.MemoryMsg.locOf m ∧
          m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
          Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m') := by
  classical
  have sourceFacts : ∀ decoded ∈ orderedRows,
      decoded ∈ decodedInstructionRows (p := p) witness.tables ∧
        (decoded.toChipRow witness.data).is_real = 1 := by
    intro decoded decodedMem
    have sourceMem := exhaustive.mem_iff.mp decodedMem
    simpa only [realDecodedInstructionRows, List.mem_filter, decide_eq_true_eq] using sourceMem
  have contractAt : ∀ decoded ∈ orderedRows, ChipGroundingContracts decoded.chip := by
    intro decoded decodedMem
    exact obligations.chipContracts decoded.chip
      (decodedInstructionRows_chip_mem witness.tables (sourceFacts decoded decodedMem).1)
  have decodeAt : ∀ decoded ∈ orderedRows,
      Target.decodedInROM statement.program
        (programAccess (decoded.toChipRow witness.data).view).toRow :=
    supportedCore_orderedRows_programDecoded statement witness constraints balanced boundary
      orderedRows exhaustive
  have alignedExists : ∀ decoded ∈ orderedRows, ∃ touches : List (TimedGrounding.Touch p),
      TimedGrounding.AlignsWith
          (TimedGrounding.alignedOf (decoded.ordinaryRowFacts witness.data) touches)
          (decoded.ordinaryRowFacts witness.data) ∧
        (∀ tc ∈ touches,
          TimedGrounding.TouchOK
            (Semantics.StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull)
            tc.1 tc.2) ∧
        (∀ loc : Semantics.MemLoc, List.IsChain
          (fun a b : TimedGrounding.Touch p =>
            Semantics.MemoryMsg.timeNat a.2 < Semantics.MemoryMsg.timeNat b.2)
          (touches.filter (fun pq => Semantics.MemoryMsg.locOf pq.2 = loc))) ∧
        (∀ tc ∈ touches, Channels.MemoryMsg.ClkBound tc.2) ∧
        (∀ tc ∈ touches, Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 →
          (tc : TimedGrounding.Touch p).1.1.clk_high.val < 2 ^ 24 →
            Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).1.1 <
              Semantics.MemoryMsg.timeNat tc.2) := by
    intro decoded decodedMem
    exact (contractAt decoded decodedMem).rowAligned witness constraints balanced decoded rfl
      (sourceFacts decoded decodedMem).1 (sourceFacts decoded decodedMem).2 statement.program
      (decodeAt decoded decodedMem)
  let touchesOf : DecodedInstructionRow p → List (TimedGrounding.Touch p) := fun decoded =>
    if decodedMem : decoded ∈ orderedRows then Classical.choose (alignedExists decoded decodedMem)
    else []
  have touchesOf_spec : ∀ decoded ∈ orderedRows,
      TimedGrounding.AlignsWith
          (TimedGrounding.alignedOf (decoded.ordinaryRowFacts witness.data) (touchesOf decoded))
          (decoded.ordinaryRowFacts witness.data) ∧
        (∀ tc ∈ touchesOf decoded,
          TimedGrounding.TouchOK
            (Semantics.StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull)
            tc.1 tc.2) ∧
        (∀ loc : Semantics.MemLoc, List.IsChain
          (fun a b : TimedGrounding.Touch p =>
            Semantics.MemoryMsg.timeNat a.2 < Semantics.MemoryMsg.timeNat b.2)
          ((touchesOf decoded).filter (fun pq => Semantics.MemoryMsg.locOf pq.2 = loc))) ∧
        (∀ tc ∈ touchesOf decoded, Channels.MemoryMsg.ClkBound tc.2) ∧
        (∀ tc ∈ touchesOf decoded,
          Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 →
            (tc : TimedGrounding.Touch p).1.1.clk_high.val < 2 ^ 24 →
              Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).1.1 <
                Semantics.MemoryMsg.timeNat tc.2) := by
    intro decoded decodedMem
    simp only [touchesOf, dif_pos decodedMem]
    exact Classical.choose_spec (alignedExists decoded decodedMem)
  let alignedRow : DecodedInstructionRow p → Semantics.RowFacts p := fun decoded =>
    TimedGrounding.alignedOf (decoded.ordinaryRowFacts witness.data) (touchesOf decoded)
  have aligns : ∀ decoded ∈ orderedRows,
      TimedGrounding.AlignsWith (alignedRow decoded)
        (decoded.ordinaryRowFacts witness.data) := by
    intro decoded decodedMem
    exact (touchesOf_spec decoded decodedMem).1
  have timeStep : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2 =
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 + 8 := by
    intro decoded decodedMem
    exact witness_realDecodedInstructionRows_timeStep witness constraints balanced decoded
      (exhaustive.mem_iff.mp decodedMem)
  -- The W3 goodness pack: on every active instruction edge both endpoints carry a genuine 24-bit
  -- `clk_high` and genuine 16-bit upper pc limbs, so canonical re-limbing preserves the ℕ time and
  -- the 64-bit pc image.  That is exactly what lets the canonicalized State trail drive a carrier
  -- built from the physical row's own columns.
  have goodness := (witness_stateEdges_goodness witness constraints balanced).1
  have canonTimePull : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).1) =
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).1 := fun d hd =>
    timeNat_canonState (goodness d (exhaustive.mem_iff.mp hd)).1.1
  have canonTimePush : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).2) =
        Semantics.StateMsg.timeNat (decodedStateEdge witness.data decoded).2 := fun d hd =>
    timeNat_canonState (goodness d (exhaustive.mem_iff.mp hd)).1.2
  have canonPcPull : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.pcBits (canonState (decodedStateEdge witness.data decoded).1) =
        Semantics.StateMsg.pcBits (decodedStateEdge witness.data decoded).1 := fun d hd =>
    pcBits_canonState (goodness d (exhaustive.mem_iff.mp hd)).2.1.1
      (goodness d (exhaustive.mem_iff.mp hd)).2.1.2
  have canonPcPush : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.pcBits (canonState (decodedStateEdge witness.data decoded).2) =
        Semantics.StateMsg.pcBits (decodedStateEdge witness.data decoded).2 := fun d hd =>
    pcBits_canonState (goodness d (exhaustive.mem_iff.mp hd)).2.2.1
      (goodness d (exhaustive.mem_iff.mp hd)).2.2.2
  have timeStepCanon : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).2) =
        Semantics.StateMsg.timeNat (canonState (decodedStateEdge witness.data decoded).1) + 8 := by
    intro d hd
    rw [canonTimePull d hd, canonTimePush d hd]
    exact timeStep d hd
  -- The public boundary clock limbs are range-checked by the verifier row, so the whole shard sits
  -- below `2 ^ 48`.  That ceiling turns a pushed record's `TouchOK` window bound into a genuine
  -- 24-bit `clk_high`, which is one of the two facts the MemoryBump refresh evidence consumes.
  have limbBounds : SP1StateBoundary.LimbBounds statement.publicValues := by
    rw [← publicInputEq]
    exact witness_publicInput_limbBounds witness constraints balanced
  have initTimeLt : Semantics.StateMsg.timeNat
      (initialBoundaryStateMessage statement.publicValues) < 2 ^ 48 :=
    clkNat_lt_of_limbs (initialBoundaryStateMessage_bounds _ limbBounds).1
      (initialBoundaryStateMessage_bounds _ limbBounds).2.1
  have finalTimeLt : Semantics.StateMsg.timeNat
      (finalBoundaryStateMessage statement.publicValues) < 2 ^ 48 :=
    clkNat_lt_of_limbs (finalBoundaryStateMessage_bounds _ limbBounds).1
      (finalBoundaryStateMessage_bounds _ limbBounds).2.1
  have clockCount := clockCount_of_stateWalk _ stateWalk timeStepCanon
  have rowWindowLt : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull + 8 ≤
        Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues) := by
    intro decoded decodedMem
    obtain ⟨done, suffix, rowsEq⟩ := List.append_of_mem decodedMem
    have position := statePullTime_of_stateWalk _ stateWalk timeStepCanon done decoded suffix
      rowsEq
    rw [canonTimePull decoded decodedMem] at position
    have hpos : Semantics.StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull =
      Semantics.StateMsg.timeNat (initialBoundaryStateMessage statement.publicValues) +
        8 * done.length := position
    have hlen : done.length + 1 ≤ orderedRows.length := by
      rw [rowsEq, List.length_append, List.length_cons]
      omega
    omega
  have liveAtHead : TimedGrounding.LiveOK initial (Commit.initClkNat witness.data)
      (Semantics.StateMsg.timeNat (initialBoundaryStateMessage statement.publicValues))
      (memoryInitFrontier witness) := by
    have headTime : Semantics.StateMsg.timeNat
        (initialBoundaryStateMessage statement.publicValues) = Commit.initClkNat witness.data := by
      simpa only [initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using
        boundary.initialClock.symm
    rw [headTime]
    exact memoryInit_liveOK constraints boundary
  -- The widened per-location Memory balance: the aligned rows' touches against the two boundary
  -- frontiers, plus the MemoryBump table's own refresh pairs.
  have widened := memoryBalance_of_alignsWith witness balanced
    obligations.memoryMultiplicityBinary
    (initPure witness constraints) (finPure witness constraints) boundary.memoryProviderUnique
    boundary.memoryFinalizeProviderUnique obligations.paddingMemoryEmpty orderedRows exhaustive
    alignedRow aligns
  have pushGood : ∀ loc : Semantics.MemLoc, ∀ m ∈
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          TimedGrounding.pushesAt (orderedRows.map alignedRow) loc +
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))),
      Channels.MemoryMsg.ClkBound m ∧ m.clk_high.val < 2 ^ 24 := by
    intro loc m memberM
    rcases Multiset.mem_add.mp memberM with frontierOrRow | bumpPush
    · rcases Multiset.mem_add.mp frontierOrRow with genesis | rowPush
      · -- the genesis frontier record: its bus guarantee and its `≤ initClk` boundary time
        obtain ⟨-, memTruth, -, htime⟩ :=
          liveAtHead loc m (TimedGrounding.mem_optMS.mp genesis)
        exact ⟨memTruth.2.1, clkHigh_lt_of_timeNat_le htime initTimeLt⟩
      · -- one instruction row's own push: its reader's `clk_low` range check and the `t + 4` window
        obtain ⟨r, rowMem, pushMem, -⟩ := mem_pushesAt.mp rowPush
        obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
        have pushMem' : m ∈ (touchesOf decoded).map Prod.snd := pushMem
        obtain ⟨tc, touchMem, rfl⟩ := List.mem_map.mp pushMem'
        have evidence := touchesOf_spec decoded decodedMem
        refine ⟨evidence.2.2.2.1 tc touchMem, clkHigh_lt_of_timeNat_le ?_ finalTimeLt⟩
        have windowHi := (evidence.2.1 tc touchMem).push_hi
        have windowLt := rowWindowLt decoded decodedMem
        omega
    · -- one MemoryBump row's refreshed push: range-checked in-circuit
      rw [Multiset.mem_filter, Multiset.mem_coe,
        memoryBump_producedMessages_eq witness constraints] at bumpPush
      obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp bumpPush.1
      exact memoryBump_pushedMessage_clkFacts witness constraints balanced row rowMem
  have pullGood : ∀ loc : Semantics.MemLoc, ∀ m ∈
      TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          TimedGrounding.pullsAt (orderedRows.map alignedRow) loc +
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))),
      Channels.MemoryMsg.ClkBound m ∧ m.clk_high.val < 2 ^ 24 :=
    fun loc => forall_mem_of_balance (widened loc) (pushGood loc)
  have alignedPullGood : ∀ decoded ∈ orderedRows, ∀ tc ∈ touchesOf decoded,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 ∧
        (tc : TimedGrounding.Touch p).1.1.clk_high.val < 2 ^ 24 := by
    intro decoded decodedMem tc touchMem
    refine pullGood _ _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr
      (mem_pullsAt.mpr ⟨⟨alignedRow decoded, List.mem_map_of_mem decodedMem, tc.1, ?_, rfl⟩,
        rfl⟩)))))
    exact List.mem_map_of_mem touchMem
  have ordinaryPullGood : ∀ decoded ∈ orderedRows,
      ∀ mp ∈ (decoded.ordinaryRowFacts witness.data).memPulls,
        Channels.MemoryMsg.ClkBound (mp : Channels.MemoryMsg (ZMod p) × ℕ).1 := by
    intro decoded decodedMem mp pullMem
    obtain ⟨mp', alignedMem, priorEq⟩ := List.mem_map.mp
      ((aligns decoded decodedMem).pulls.mem_iff.mpr (List.mem_map_of_mem pullMem))
    exact (pullGood (Semantics.MemoryMsg.locOf mp.1) mp.1 (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inr (mem_pullsAt.mpr
        ⟨⟨alignedRow decoded, List.mem_map_of_mem decodedMem, mp', alignedMem, priorEq⟩,
          rfl⟩)))))).1
  -- Every active MemoryBump row is a genuine refresh: its pulled record's two timestamp facts come
  -- from the produced side of the very balance the row contributes to.
  have bumpRefresh : ∀ row ∈ realMemoryBumpRows witness,
      RefreshElimination.IsRefresh
        (fun m : Channels.MemoryMsg (ZMod p) => (Semantics.MemoryMsg.locOf m, m.value))
        Semantics.MemoryMsg.timeNat
        (MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row),
          MemoryBumpChip.pushedMessage (memoryBumpRow (memoryBumpTable witness) row)) := by
    intro row rowMem
    have pulledMem : MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row) ∈
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = Semantics.MemoryMsg.locOf
            (MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row)))
          (↑(consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))) := by
      rw [Multiset.mem_filter, Multiset.mem_coe,
        memoryBump_consumedMessages_eq witness constraints]
      exact ⟨List.mem_map_of_mem rowMem, rfl⟩
    have good := pullGood _ _ (Multiset.mem_add.mpr (Or.inr pulledMem))
    exact memoryBump_isRefresh witness constraints balanced row rowMem good.1 good.2
  -- The refresh pairs as one list, and its two projections against the bump table's messages.
  set bump : List (Channels.MemoryMsg (ZMod p) × Channels.MemoryMsg (ZMod p)) :=
    (realMemoryBumpRows witness).map (fun row =>
      (MemoryBumpChip.pulledMessage (memoryBumpRow (memoryBumpTable witness) row),
        MemoryBumpChip.pushedMessage (memoryBumpRow (memoryBumpTable witness) row))) with bumpDef
  have bumpSnd : bump.map Prod.snd =
      producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
        Channels.memoryChannel) := by
    rw [memoryBump_producedMessages_eq witness constraints, bumpDef, List.map_map]
    rfl
  have bumpFst : bump.map Prod.fst =
      consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
        Channels.memoryChannel) := by
    rw [memoryBump_consumedMessages_eq witness constraints, bumpDef, List.map_map]
    rfl
  have bumpRefresh' : ∀ b ∈ bump, RefreshElimination.IsRefresh
      (fun m : Channels.MemoryMsg (ZMod p) => (Semantics.MemoryMsg.locOf m, m.value))
      Semantics.MemoryMsg.timeNat b := by
    intro b memberB
    rw [bumpDef] at memberB
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp memberB
    exact bumpRefresh row rowMem
  have bumpLoc : ∀ b ∈ bump, Semantics.MemoryMsg.locOf
      (b : Channels.MemoryMsg (ZMod p) × Channels.MemoryMsg (ZMod p)).1 =
        Semantics.MemoryMsg.locOf b.2 :=
    fun b memberB => congrArg Prod.fst (bumpRefresh' b memberB).1
  -- The widened balance in the per-location touch-pair form both generic engines speak.
  have touchBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          (touchPairsAt (orderedRows.map touchesOf) loc).map Prod.snd +
          Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
            (↑(bump.map Prod.snd) : Multiset (Channels.MemoryMsg (ZMod p))) =
        TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          (touchPairsAt (orderedRows.map touchesOf) loc).map Prod.fst +
          Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
            (↑(bump.map Prod.fst) : Multiset (Channels.MemoryMsg (ZMod p))) := by
    intro loc
    have alignedPushEq : ∀ decoded ∈ orderedRows,
        (alignedRow decoded).memPushes = (touchesOf decoded).map Prod.snd := fun _ _ => rfl
    have alignedPullEq : ∀ decoded ∈ orderedRows,
        (alignedRow decoded).memPulls = (touchesOf decoded).map Prod.fst := fun _ _ => rfl
    have pushBridge := pushesAt_of_touchLists orderedRows alignedRow touchesOf alignedPushEq loc
    have pullBridge := pullsAt_of_touchLists orderedRows alignedRow touchesOf alignedPullEq
      (fun d hd tc htc => ((touchesOf_spec d hd).2.1 tc htc).loc_eq) loc
    rw [bumpSnd, bumpFst, ← pushBridge, ← pullBridge]
    exact widened loc
  -- Eliminate the refresh pairs and realize the rewritten pulls row by row.
  obtain ⟨ts', finalFrontier, rewritten, refreshFreeBalance, finalRewrite⟩ :=
    exists_refreshFreeTouchLists
      (fun m : Channels.MemoryMsg (ZMod p) => (Semantics.MemoryMsg.locOf m, m.value))
      Semantics.MemoryMsg.timeNat (orderedRows.map touchesOf) (memoryInitFrontier witness)
      (memoryFinalizeFrontier witness) bump bumpRefresh' bumpLoc touchBalance
  have lengthEq : orderedRows.length = ts'.length := by
    have := rewritten.length_eq
    rwa [List.length_map] at this
  set pairs : List (DecodedInstructionRow p × List (TimedGrounding.Touch p)) :=
    orderedRows.zip ts' with pairsDef
  have pairsFst : pairs.map Prod.fst = orderedRows := List.map_fst_zip (le_of_eq lengthEq)
  have pairsSnd : pairs.map Prod.snd = ts' := List.map_snd_zip (le_of_eq lengthEq.symm)
  have pairFacts : ∀ q ∈ pairs, q.1 ∈ orderedRows ∧
      List.Forall₂ PullRewrite (touchesOf q.1) q.2 := by
    intro q memberQ
    refine ⟨pairsFst ▸ List.mem_map_of_mem memberQ, ?_⟩
    have zipMem : ((touchesOf q.1, q.2) :
        List (TimedGrounding.Touch p) × List (TimedGrounding.Touch p)) ∈
        (orderedRows.map touchesOf).zip ts' := by
      rw [List.zip_map_left, ← pairsDef]
      exact List.mem_map_of_mem memberQ
    exact (List.forall₂_zip rewritten zipMem).imp fun _ _ h => pullRewrite_of_touchRewrite h
  have rewrittenLoc : ∀ q ∈ pairs, ∀ tc ∈ q.2,
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2 =
        Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1 := by
    intro q memberQ tc touchMem
    obtain ⟨rowMem, rewrite⟩ := pairFacts q memberQ
    obtain ⟨tc₀, touchMem₀, hread, hpush, hloc, -, -⟩ :=
      TimedGrounding.forall₂_exists_left rewrite tc touchMem
    rw [hpush, hloc]
    exact ((touchesOf_spec q.1 rowMem).2.1 tc₀ touchMem₀).loc_eq
  -- The carrier actually fed to the walk: the rewritten touches, with the State edge re-spelled in
  -- the canonical limbs the trail walks.
  set walkRow : DecodedInstructionRow p × List (TimedGrounding.Touch p) → Semantics.RowFacts p :=
    fun q => TimedGrounding.stateRespell
      (TimedGrounding.alignedOf (q.1.ordinaryRowFacts witness.data) q.2)
      (canonState (decodedStateEdge witness.data q.1).1)
      (canonState (decodedStateEdge witness.data q.1).2) with walkRowDef
  have valueAligned : ∀ q ∈ pairs,
      TimedGrounding.ValueAligned (walkRow q) (q.1.ordinaryRowFacts witness.data) := by
    intro q memberQ
    obtain ⟨rowMem, rewrite⟩ := pairFacts q memberQ
    exact valueAligned_stateRespell
      (valueAligned_alignedOf_pullRewrite _ _ _ rewrite ((touchesOf_spec q.1 rowMem).1)
        (ordinaryPullGood q.1 rowMem))
      (canonTimePull q.1 rowMem) (canonPcPull q.1 rowMem) (canonTimePush q.1 rowMem)
      (canonPcPush q.1 rowMem)
  have engineFacts : ∀ decoded ∈ orderedRows,
      Semantics.LocalStepFact statement.program initial (Commit.initClkNat witness.data)
          (decoded.ordinaryRowFacts witness.data) ∧
        TimedGrounding.FrameFact statement.program initial (Commit.initClkNat witness.data)
          (decoded.ordinaryRowFacts witness.data) := by
    intro decoded decodedMem
    exact (contractAt decoded decodedMem).engineFacts witness constraints balanced decoded rfl
      (sourceFacts decoded decodedMem).1 (sourceFacts decoded decodedMem).2 statement.program
      (decodeAt decoded decodedMem) initial (Commit.initClkNat witness.data)
      boundary.codeMemoryCompatible
  have stepFacts : ∀ row ∈ pairs.map walkRow,
      Semantics.LocalStepFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨q, memberQ, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.localStepFact_valueAligned_of_ordinary (valueAligned q memberQ)
      (engineFacts q.1 (pairFacts q memberQ).1).1
  have frameFacts : ∀ row ∈ pairs.map walkRow,
      TimedGrounding.FrameFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨q, memberQ, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.frameFact_valueAligned_of_ordinary (valueAligned q memberQ)
      (engineFacts q.1 (pairFacts q memberQ).1).2
  have rowOK : ∀ row ∈ pairs.map walkRow,
      TimedGrounding.RowOK (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨q, memberQ, rfl⟩ := List.mem_map.mp rowMem
    obtain ⟨decodedMem, rewrite⟩ := pairFacts q memberQ
    have evidence := touchesOf_spec q.1 decodedMem
    refine TimedGrounding.rowOK_stateRespell (canonTimePull q.1 decodedMem)
      (canonTimePush q.1 decodedMem) ?_
    refine rowOK_alignedOf_pullRewrite (Commit.initClkNat witness.data)
      (q.1.ordinaryRowFacts witness.data) (touchesOf q.1) q.2 rewrite ?_ ?_ evidence.2.1
      evidence.2.2.1 evidence.2.2.2.1 ?_
    · simpa only [DecodedInstructionRow.ordinaryRowFacts_statePull,
        DecodedInstructionRow.ordinaryRowFacts_statePush, decodedStateEdge] using
        timeStep q.1 decodedMem
    · have aligned := statePullAlign8_of_stateWalk _ stateWalk timeStepCanon q.1 decodedMem
      rw [canonTimePull q.1 decodedMem] at aligned
      rw [boundary.initialClock]
      simpa only [DecodedInstructionRow.ordinaryRowFacts_statePull, decodedStateEdge,
        initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using aligned
    · intro tc touchMem
      exact evidence.2.2.2.2 tc touchMem (alignedPullGood q.1 decodedMem tc touchMem).1
        (alignedPullGood q.1 decodedMem tc touchMem).2
  have stateBalance :
      initialBoundaryStateMessage statement.publicValues ::ₘ
          (↑((pairs.map walkRow).map (·.statePush)) :
            Multiset (Channels.StateMsg (ZMod p))) =
        finalBoundaryStateMessage statement.publicValues ::ₘ
          ↑((pairs.map walkRow).map (·.statePull)) := by
    have pushMap : (pairs.map walkRow).map (·.statePush) =
        orderedRows.map (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2).2) := by
      rw [← pairsFst, List.map_map, List.map_map]
      rfl
    have pullMap : (pairs.map walkRow).map (·.statePull) =
        orderedRows.map (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2).1) := by
      rw [← pairsFst, List.map_map, List.map_map]
      rfl
    rw [pushMap, pullMap]
    exact endpointBalance_of_stateWalk _ stateWalk
  have memoryBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          TimedGrounding.pushesAt (pairs.map walkRow) loc =
        TimedGrounding.optMS (finalFrontier loc) +
          TimedGrounding.pullsAt (pairs.map walkRow) loc := by
    intro loc
    have walkPushEq : ∀ q ∈ pairs, (walkRow q).memPushes = (Prod.snd q).map Prod.snd :=
      fun _ _ => rfl
    have walkPullEq : ∀ q ∈ pairs, (walkRow q).memPulls = (Prod.snd q).map Prod.fst :=
      fun _ _ => rfl
    have pushBridge := pushesAt_of_touchLists pairs walkRow Prod.snd walkPushEq loc
    have pullBridge := pullsAt_of_touchLists pairs walkRow Prod.snd walkPullEq rewrittenLoc loc
    rw [pushBridge, pullBridge, pairsSnd]
    exact refreshFreeBalance loc
  have walked := TimedGrounding.walk statement.program initial (Commit.initClkNat witness.data)
    (finalBoundaryStateMessage statement.publicValues) finalFrontier
    (pairs.map walkRow).length (pairs.map walkRow)
    (initialBoundaryStateMessage statement.publicValues) (memoryInitFrontier witness)
    rfl stepFacts frameFacts rowOK boundary.localStateTruth
    liveAtHead stateBalance memoryBalance
  refine ⟨?_, walked.2.1, fun loc m finEq => ?_⟩
  · intro done decoded suffix rowsEq state chain
    have decodedMem : decoded ∈ orderedRows := by
      rw [rowsEq]
      exact List.mem_append_right done List.mem_cons_self
    obtain ⟨q, memberQ, rfl⟩ : ∃ q ∈ pairs, q.1 = decoded := by
      obtain ⟨q, memberQ, hq⟩ := List.mem_map.mp (pairsFst ▸ decodedMem :
        decoded ∈ pairs.map Prod.fst)
      exact ⟨q, memberQ, hq⟩
    have weak := TimedGrounding.weakGrounded_ordinary_of_valueAligned (valueAligned q memberQ)
      (walked.1 (walkRow q) (List.mem_map_of_mem memberQ))
    have rowTimeRaw := statePullTime_of_stateWalk _ stateWalk timeStepCanon done q.1
      suffix rowsEq
    rw [canonTimePull q.1 decodedMem] at rowTimeRaw
    have rowTime : Semantics.StateMsg.timeNat
        (statePullMessage (q.1.toChipRow witness.data)) =
          Commit.initClkNat witness.data + 8 * done.length := by
      rw [boundary.initialClock]
      simpa only [decodedStateEdge, initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using
        rowTimeRaw
    exact q.1.dynamicGrounded_of_weakCurrency witness constraints balanced
      (sourceFacts q.1 decodedMem).1 (contractAt q.1 decodedMem) statement.program initial state
      (Commit.initClkNat witness.data) done.length (decodeAt q.1 decodedMem) weak.2 chain
      (sourceFacts q.1 decodedMem).2 rowTime
  · obtain ⟨m', frontierEq, valueEq, timeLe⟩ := finalRewrite loc m finEq
    exact ⟨m', congrArg Prod.fst valueEq, congrArg Prod.snd valueEq, timeLe,
      walked.2.2 loc m' frontierEq⟩

/-- Dynamic grounding over the exact ordered physical rows.

Ordering, activity, registry membership, Program decode, and clock accounting are all proved outside
this theorem.  The timed walk and physical-row bridge are fully proved by
`supportedCore_orderedRows_dynamic_of_obligations`; the only admitted dependency is the explicitly
finite `supportedCore_groundingObligations_of_constraints` rollout above. -/
theorem supportedCore_orderedRows_dynamic
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (publicInputEq : witness.publicInput = statement.publicValues)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables))
    (stateWalk : Walk.IsWalk (fun decoded =>
        (canonState (decodedStateEdge witness.data decoded).1,
         canonState (decodedStateEdge witness.data decoded).2))
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows) :
    (∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state) ∧
      Semantics.LocalStateTruth statement.program initial (Commit.initClkNat witness.data)
        (finalBoundaryStateMessage statement.publicValues) ∧
      (∀ loc m, memoryFinalizeFrontier witness loc = some m →
        ∃ m', Semantics.MemoryMsg.locOf m' = Semantics.MemoryMsg.locOf m ∧
          m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
          Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m') := by
  exact supportedCore_orderedRows_dynamic_of_obligations statement witness initial publicInputEq
    constraints balanced boundary
    (supportedCore_groundingObligations_of_constraints witness constraints)
    orderedRows exhaustive stateWalk

/-- The sole semantic grounding seam for the supported native slice.

Program-provider commitment is no longer part of this seam:
`supportedCore_orderedRows_programDecoded` supplies the exact static decode field for every exhaustive
ordering, and `supportedCore_orderedRows_static` packages the whole static layer without pretending
that row `Spec`s are state-independent.  Ranked State-bus ordering and clock counting are now closed;
`supportedCore_orderedRows_dynamic` is the remaining timed Memory/spec/readiness argument. -/
theorem supported_core_witness_grounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (publicInputEq : witness.publicInput = statement.publicValues)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial) :
    ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows := by
  obtain ⟨orderedRows, stateWalk, exhaustiveMultiset⟩ :=
    witness_realDecodedState_canonExhaustiveTrail witness constraints balanced
  rw [publicInputEq] at stateWalk
  have exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables) :=
    Multiset.coe_eq_coe.mp exhaustiveMultiset
  have goodness := (witness_stateEdges_goodness witness constraints balanced).1
  have dyn := supportedCore_orderedRows_dynamic statement witness initial publicInputEq constraints
    balanced boundary orderedRows exhaustive stateWalk
  refine ⟨orderedRows, exhaustive, ?_, ?_, ?_, dyn.2.1, dyn.2.2⟩
  · simpa [initialBoundaryStateMessage, finalBoundaryStateMessage,
      Semantics.StateMsg.pcBits, supportedPcBits] using
      pcWalk_of_canonStateWalk witness.data stateWalk (fun decoded decodedMem =>
        ⟨(goodness decoded (exhaustive.mem_iff.mp decodedMem)).2.1,
          (goodness decoded (exhaustive.mem_iff.mp decodedMem)).2.2⟩)
  · exact {
      static := supportedCore_orderedRows_static statement witness constraints balanced boundary
        orderedRows exhaustive
      dynamic := dyn.1 }
  · have clockCount := clockCount_of_stateWalk _ stateWalk
      (fun decoded decodedMem => by
        rw [timeNat_canonState (goodness decoded (exhaustive.mem_iff.mp decodedMem)).1.1,
          timeNat_canonState (goodness decoded (exhaustive.mem_iff.mp decodedMem)).1.2]
        exact witness_realDecodedInstructionRows_timeStep witness constraints balanced decoded
          (exhaustive.mem_iff.mp decodedMem))
    change
      Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low +
          8 * orderedRows.length =
        Semantics.clkNat statement.publicValues.final_clk_high statement.publicValues.final_clk_low
      at clockCount
    exact clockCount

/-- Export the complete semantic grounding certificate from the honest native relation.

Unlike the local-execution soundness projection below, this theorem retains the initial boundary
facts together with the grounding record's final-State and memory-finalize truths.  It is therefore
the reusable native endpoint for shard composition and for later exact-Core/ArkLib transport: callers
do not have to reopen the relation or reconstruct facts that the timed grounding walk already proved. -/
theorem supported_core_native_grounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (valid : SupportedCoreNativeRelation statement witness) :
    ∃ initial orderedRows, InitialBoundaryFacts statement witness initial ∧
      SupportedCoreGrounding statement witness initial orderedRows := by
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, ⟨initial, boundary⟩⟩ := valid
  obtain ⟨orderedRows, grounding⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary
  exact ⟨initial, orderedRows, boundary, grounding⟩

/-- **Supported native-Clean soundness.** A satisfying, channel-balanced witness whose provider
tables are semantically bound produces a genuine local official-Sail execution between its public
endpoints.  Those two conjuncts are the *whole* premise: the RAM access-timestamp range fact the
generic underflow argument needs is derived inside the capstone from the per-location Memory
balance, not assumed here.  This deliberately concludes a shard-local segment; boot reachability is
supplied later by `supportedCoreLocalExecution_anchors` when consecutive shards are composed. -/
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model) := by
  intro statement witness valid
  obtain ⟨initial, rows, boundary, grounding⟩ :=
    supported_core_native_grounding statement witness valid
  apply groundedRows_localExecution model statement witness.data initial
    (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data) rows
    boundary.programWellFormed boundary.initialPc boundary.romLoaded boundary.configured
    boundary.codeMemoryCompatible grounding.walk grounding.grounded
  rw [Machine.localExecutionClock_eq_ordinary ordinary]
  exact grounding.clockCount

/-- **Supported native-Clean soundness, plain-Sail form.**  The same two-conjunct premise as
`supported_core_native_sound`, with the conclusion stated directly on the official Sail machine:
a normally-retiring interpreter run between the committed public pc endpoints, taking exactly the
committed number of eight-tick instructions.  No machine-model parameter and no schedule
hypothesis — the model-scheduled form is recovered by
`supportedCoreLocalExecution_of_sailRelation`. -/
theorem supported_core_native_sail_sound :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreSailRelation (p := p)) := by
  intro statement witness valid
  obtain ⟨initial, rows, boundary, grounding⟩ :=
    supported_core_native_grounding statement witness valid
  exact groundedRows_sailRelation statement witness.data initial
    (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data) rows
    boundary.programWellFormed boundary.initialPc boundary.romLoaded boundary.configured
    boundary.codeMemoryCompatible grounding.walk grounding.grounded grounding.clockCount

/-- Construct the common semantic witness while retaining its exact active-row count.

The witness stores only the grounded initial state and ordinary event transcript.  Its transition
targets are recovered by the shared evaluator, so native soundness does not publish a second
trace-shaped semantic relation. -/
theorem supported_core_native_shard_execution
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (valid : SupportedCoreNativeShardRelation statement witness) :
    ∃ semanticWitness : Machine.CoreShardSemanticWitness,
      SupportedCoreShardExecutionRelation statement semanticWitness ∧
        (semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))).steps =
          (realDecodedInstructionRows witness.data witness.tables).length := by
  obtain ⟨nativeValid, rowLimit⟩ := valid
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, ⟨initial, boundary⟩⟩ := nativeValid
  obtain ⟨rows, grounding⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary
  obtain ⟨execution, initialEq, stepsEq, finalPc, executionValid, clocked, finalClock,
      ordinary, supported⟩ :=
    eventExecution_of_groundedRows Machine.ExecutableSyscallHandler.none.relation
      (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
      witness.data statement.program initial rows
      (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
        statement.publicValues.init_pc2)
      (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
        statement.publicValues.final_pc2)
      grounding.walk grounding.grounded boundary.codeMemoryCompatible boundary.initialPc
      boundary.romLoaded boundary.configured
      (Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low)
  let semanticWitness := Machine.CoreShardSemanticWitness.ofOrdinaryTrace
    statement.program ⟨[]⟩ execution
  have publicValuesWellFormed : statement.publicValues.LimbBounds := by
    rw [← publicInputEq]
    exact witness_publicInput_limbBounds witness constraints balanced
  have evaluated := Machine.CoreShardSemanticWitness.trace?_ofOrdinaryTrace
    (supportedCoreShardModel (p := p)) statement.program ⟨[]⟩ execution executionValid ordinary
  refine ⟨semanticWitness, {
    statementValid := publicValuesWellFormed
    programWellFormed := boundary.programWellFormed
    programBound := rfl
    programValid := boundary.programCommitted.encodable
    contractValid := trivial
    romLoaded := ?_
    configured := ?_
    codeMemoryCompatible := ?_
    memoryWellFormed := ?_
    memoryAgrees := ?_
    shardCase := ?_ }, ?_⟩
  · change Target.RomLoaded statement.program execution.initialState
    rw [initialEq]
    exact boundary.romLoaded
  · change Target.SailConfigured execution.initialState
    rw [initialEq]
    exact boundary.configured
  · change Target.SailCodeMemoryCompatible statement.program execution.initialState
    rw [initialEq]
    exact boundary.codeMemoryCompatible
  · exact ⟨List.nodup_nil, fun cell member => absurd member List.not_mem_nil⟩
  · intro cell member
    exact absurd member List.not_mem_nil
  · refine .execution execution.events execution rfl rfl evaluated executionValid clocked
      (finalClock.trans grounding.clockCount) ?_ finalPc ?_
    · simpa only [initialEq, supportedCoreShardModel, supportedCoreShardBoundary] using
        boundary.initialPc
    · refine ⟨ordinary, supported, ?_⟩
      rw [stepsEq, grounding.exhaustive.length_eq]
      exact rowLimit
  · rw [Machine.CoreShardSemanticWitness.evaluatedTrace_eq_of_trace? evaluated]
    exact stepsEq.trans grounding.exhaustive.length_eq

/-- **Capacity-aligned native soundness into the one canonical shard relation.**

The intermediate `EventExecutionTrace` is immediately embedded by its initial state and event
transcript; its target states are then recovered by the shared evaluator.  The canonical witness's
Memory boundary is empty on this projection because the native relation already carries its
provider binding separately; exact Core fills the same field from the paired six-table cluster. -/
theorem supported_core_native_shard_sound :
    WitnessRelation.Sound (SupportedCoreNativeShardRelation (p := p))
      (SupportedCoreShardExecutionRelation (p := p)) := by
  intro statement witness valid
  obtain ⟨semanticWitness, semantic, -⟩ :=
    supported_core_native_shard_execution statement witness valid
  exact ⟨semanticWitness, semantic⟩

/-! ## Completeness boundary

Whole-machine completeness is intentionally not inferred from the `completeness` field embedded in
each `GeneralFormalCircuit`. `Soundness/AIRCompleteness.lean` proves
`supported_core_generated_trace_complete` for `SupportedCoreGeneratedTraceRelation`: a canonical
trace record whose per-table routing facts, canonical nonnegative provider-count encodings, four
exact centered-integer channel balances, public equality, and semantic boundary binding are
supplied. It constructs every physical table row with the circuits' own witness generators. This is
generator-relative AIR assembly completeness, not yet the stronger theorem that every supported
Sail execution produces such a trace; the latter still requires a verified Sail-execution-to-trace
generator. Using the broader `SupportedCoreLocalExecutionRelation` directly would be false for
unsupported Sail executions. -/

/-! ## Full extracted target

`Soundness/CoreAIR.lean` owns the conditional
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` combinators.  Their source is the
concrete paired 34+6-table Rust relation in `Faithful/CoreAIR.lean`, not this smaller native ensemble.
The required field-by-field proof bundle is not yet instantiated, so the unqualified
`sp1_air_refinement`/`sp1_air_sound` names remain reserved for that closed result.  Its COMMIT
conclusion is deliberately limited to correctness of rows that exist.  The base composed execution
relation preserves that distinction; complete eight-row coverage appears only in the optional
`SP1CommitCoveredExecutionRelation`, derived from the explicit program contract
`UsesStandardHaltWrapper`.  This file continues to own only the 25-chip proof-oriented Clean slice. -/

/-! Shard AIR soundness is not itself a halting theorem.  After recursion authenticates an ordered
ledger and all companion integrity relations, the composed target has the separate shape:

```lean
theorem sp1_execution_sound :
    WitnessRelation.Sound SP1RecursiveAIRRelation
      (Execution.SP1ExecutionRelation layout model programBinding shardIntegrity) := by
  -- proof deferred
```

The segment layout in `SP1ExecutionRelation` begins at step zero, consumes consecutive execution
shards, permits non-execution shards only when pc/timestamp are unchanged, and ends in `SP1Halted`. -/

end SP1Clean.Soundness
