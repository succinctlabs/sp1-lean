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

/-! # AIR witness relations and the semantic capstone

This module is the naming boundary the old trail capstone lacked:

* `SupportedCoreEnsembleRelation` is exactly the algebra checked by the 38-table Clean ensemble;
* `SP1SemanticBoundaryRelation` separately binds its preprocessed/provider rows to the committed
  program and a concrete local initial Sail state;
* `SupportedCoreMemoryTimestampRangeRelation` exposes the one physical range premise used by the
  generic RAM-access underflow argument;
* `SupportedCoreNativeRelation` is their conjunction; and
* `SupportedCoreLocalExecutionRelation` is the finite official-Sail target for that slice.

The names `supported_core_air_sound` and `sp1_air_sound` are reserved for extracted upstream AIR
relations.  They are not declared over the native ensemble because doing so would conflate a Clean
implementation with its Rust-faithfulness theorem. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The public statement type of the currently supported core slice. -/
abbrev SupportedCoreStatement (p : ℕ) :=
  ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))

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

/-- **The MemoryBump scope restriction of the native capstone (W3, explicitly disclosed).**

SP1's MemoryBump table *refreshes* a register record — pull it at its old timestamp, push the same
value at a strictly later canonical one — so that a record untouched for `≥ 2^24` ticks stays
reachable by the accessing rows' bounded-difference timestamp checks.  The per-location Memory
balance therefore carries those extra pull/push pairs
(`ChipContracts.memoryBalance_of_alignsWith`), while `TimedGrounding.walk` consumes the
**refresh-free** balance.

Closing that gap in general means running the proved generic engine
`RefreshElimination.eliminate` (with the proved per-row inputs
`ChipContracts.memoryBump_producedMessages_eq` / `memoryBump_consumedMessages_eq` /
`memoryBump_isRefresh`) and re-feeding the walk a carrier whose affected pulls are rewritten to
their value-equal pre-refresh ancestors — for which
`TimedGrounding.ValueAligned` and `weakGrounded_ordinary_of_valueAligned` are already proved.  The
missing piece is the *list-level* redistribution of the eliminated multiset back onto individual
rows; until it lands, this relation restricts the native capstone to shards whose MemoryBump table
carries **no active row**, in which case the bump contributions to the balance are literally empty
and no rewriting is needed.

This is a scope restriction on the witness, not a vacuous hypothesis: every shard short enough that
no register record needs a timestamp refresh (an all-padding MemoryBump table) satisfies it. -/
def SupportedCoreNoMemoryRefreshRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun _statement witness => realMemoryBumpRows witness = []

/-- The explicit physical range premise needed by SP1's generic RAM access-timestamp comparison.
The local `MemoryAccess` AIR constrains the selected difference to two byte-range-checked limbs, but
its Rust soundness argument additionally requires both compared components to be `< 2^24`. Low
components already carry `MemoryMsg.ClkBound`; this companion supplies the pulled high component.

This is intentionally a witness relation rather than an unconditional axiom or an ordering
assumption. The load/store contracts still derive strict order from the actual AIR equations. The
eventual exact extracted-AIR layer should prove this relation from SP1's public timestamp range
checks plus Memory permutation, or continue to disclose it as an external verifier premise.

⚠ **It also carries the second, separately documented Memory-side premise**
`SupportedCoreNoMemoryRefreshRelation` — read that definition before citing this one.  Both are
Memory-timestamp premises of the same argument, so they travel together through
`SupportedCoreNativeRelation`; neither is derived from the AIR today. -/
def SupportedCoreMemoryTimestampRangeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    (∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      MemoryPullTimestampHighBound (decoded.ordinaryRowFacts witness.data)) ∧
    SupportedCoreNoMemoryRefreshRelation statement witness

/-- The honest native relation used by semantic soundness. Provider truth and the RAM timestamp
range fact are explicit companion predicates, not implications smuggled out of raw interaction
balance. -/
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness ∧
        SupportedCoreMemoryTimestampRangeRelation statement witness

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
  the ∃-witness form deliberately: once the ensemble gains MemoryBump timestamp-refresh rows, the
  walk concludes truth for the *refresh-eliminated* record (same location and value, earlier time),
  and this statement absorbs that without changing shape.  Today the witness is the record itself. -/
  memoryFinalizeTruth : ∀ loc m, memoryFinalizeFrontier witness loc = some m →
    ∃ m', Semantics.MemoryMsg.locOf m' = Semantics.MemoryMsg.locOf m ∧
      m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
      Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m'

/-- The committed-decode field of every statically grounded ordered row is already discharged.
This theorem deliberately sits beside the remaining grounding seam: Program truth comes entirely
from the exact chip pulls, Clean balance, the canonical table-35 provider, and the statement binding;
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
another semantic premise. -/
theorem supportedCore_orderedRows_dynamic_of_obligations
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (memoryTimestampRange :
      SupportedCoreMemoryTimestampRangeRelation statement witness)
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
          Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).1.1 <
            Semantics.MemoryMsg.timeNat tc.2) := by
    intro decoded decodedMem
    exact (contractAt decoded decodedMem).rowAligned witness constraints balanced decoded rfl
      (sourceFacts decoded decodedMem).1 (sourceFacts decoded decodedMem).2 statement.program
      (decodeAt decoded decodedMem)
      (memoryTimestampRange.1 decoded (exhaustive.mem_iff.mp decodedMem))
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
  -- The carrier actually fed to the walk: the aligned row with its State edge re-spelled in the
  -- canonical limbs the trail walks.  Everything on the memory side is untouched.
  let walkRow : DecodedInstructionRow p → Semantics.RowFacts p := fun decoded =>
    TimedGrounding.stateRespell (alignedRow decoded)
      (canonState (decodedStateEdge witness.data decoded).1)
      (canonState (decodedStateEdge witness.data decoded).2)
  have rowOK : ∀ row ∈ orderedRows.map alignedRow,
      TimedGrounding.RowOK (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    have evidence := touchesOf_spec decoded decodedMem
    apply TimedGrounding.rowOK_alignedOf (Commit.initClkNat witness.data)
      (decoded.ordinaryRowFacts witness.data) (touchesOf decoded)
    · simpa only [TimedGrounding.alignedOf, DecodedInstructionRow.ordinaryRowFacts_statePull,
        DecodedInstructionRow.ordinaryRowFacts_statePush, decodedStateEdge] using
        timeStep decoded decodedMem
    · have aligned := statePullAlign8_of_stateWalk _ stateWalk timeStepCanon decoded decodedMem
      rw [canonTimePull decoded decodedMem] at aligned
      rw [boundary.initialClock]
      simpa only [TimedGrounding.alignedOf, DecodedInstructionRow.ordinaryRowFacts_statePull,
        decodedStateEdge, initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using aligned
    · exact evidence.2.1
    · exact evidence.2.2.1
    · exact evidence.2.2.2.1
    · exact evidence.2.2.2.2
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
  have stepFacts : ∀ row ∈ orderedRows.map walkRow,
      Semantics.LocalStepFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.localStepFact_stateRespell (canonTimePull decoded decodedMem)
      (canonPcPull decoded decodedMem) (canonTimePush decoded decodedMem)
      (canonPcPush decoded decodedMem)
      (TimedGrounding.localStepFact_align_of_ordinary (aligns decoded decodedMem)
        (engineFacts decoded decodedMem).1)
  have frameFacts : ∀ row ∈ orderedRows.map walkRow,
      TimedGrounding.FrameFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.frameFact_stateRespell (canonTimePull decoded decodedMem)
      (canonPcPull decoded decodedMem) (canonTimePush decoded decodedMem)
      (TimedGrounding.frameFact_align_of_ordinary (aligns decoded decodedMem)
        (engineFacts decoded decodedMem).2)
  have rowOKcanon : ∀ row ∈ orderedRows.map walkRow,
      TimedGrounding.RowOK (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.rowOK_stateRespell (canonTimePull decoded decodedMem)
      (canonTimePush decoded decodedMem) (rowOK _ (List.mem_map_of_mem decodedMem))
  have stateBalance :
      initialBoundaryStateMessage statement.publicValues ::ₘ
          (↑((orderedRows.map walkRow).map (·.statePush)) :
            Multiset (Channels.StateMsg (ZMod p))) =
        finalBoundaryStateMessage statement.publicValues ::ₘ
          ↑((orderedRows.map walkRow).map (·.statePull)) := by
    have pushMap : (orderedRows.map walkRow).map (·.statePush) =
        orderedRows.map (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2).2) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro decoded decodedMem
      rfl
    have pullMap : (orderedRows.map walkRow).map (·.statePull) =
        orderedRows.map (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2).1) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro decoded decodedMem
      rfl
    rw [pushMap, pullMap]
    exact endpointBalance_of_stateWalk _ stateWalk
  have memoryBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          TimedGrounding.pushesAt (orderedRows.map walkRow) loc =
        TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          TimedGrounding.pullsAt (orderedRows.map walkRow) loc := by
    intro loc
    have widened := memoryBalance_of_alignsWith witness balanced
      obligations.memoryMultiplicityBinary
      (initPure witness constraints) (finPure witness constraints) boundary.memoryProviderUnique
      boundary.memoryFinalizeProviderUnique obligations.paddingMemoryEmpty orderedRows exhaustive
      alignedRow aligns loc
    -- The MemoryBump contributions are the active bump rows' refreshed pushes and old-record
    -- pulls; under the disclosed `SupportedCoreNoMemoryRefreshRelation` scope restriction there are
    -- no active bump rows, so both filtered multisets are empty and the widened balance is already
    -- the refresh-free one the walk consumes.
    rw [memoryBump_producedMessages_eq witness constraints,
      memoryBump_consumedMessages_eq witness constraints,
      show realMemoryBumpRows witness = [] from memoryTimestampRange.2] at widened
    simp only [List.map_nil, Multiset.coe_nil, Multiset.filter_zero, add_zero] at widened
    -- Re-spelling the State edge leaves every memory projection untouched.
    have hpush : TimedGrounding.pushesAt (orderedRows.map walkRow) loc =
        TimedGrounding.pushesAt (orderedRows.map alignedRow) loc := by
      simp only [TimedGrounding.pushesAt, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun decoded _ => rfl)
    have hpull : TimedGrounding.pullsAt (orderedRows.map walkRow) loc =
        TimedGrounding.pullsAt (orderedRows.map alignedRow) loc := by
      simp only [TimedGrounding.pullsAt, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun decoded _ => rfl)
    rw [hpush, hpull]
    exact widened
  have liveAtHead : TimedGrounding.LiveOK initial (Commit.initClkNat witness.data)
      (Semantics.StateMsg.timeNat (initialBoundaryStateMessage statement.publicValues))
      (memoryInitFrontier witness) := by
    have headTime : Semantics.StateMsg.timeNat
        (initialBoundaryStateMessage statement.publicValues) = Commit.initClkNat witness.data := by
      simpa only [initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using
        boundary.initialClock.symm
    rw [headTime]
    exact memoryInit_liveOK constraints boundary
  have walked := TimedGrounding.walk statement.program initial (Commit.initClkNat witness.data)
    (finalBoundaryStateMessage statement.publicValues) (memoryFinalizeFrontier witness)
    orderedRows.length (orderedRows.map walkRow)
    (initialBoundaryStateMessage statement.publicValues) (memoryInitFrontier witness)
    (by simp only [List.length_map]) stepFacts frameFacts rowOKcanon boundary.localStateTruth
    liveAtHead stateBalance memoryBalance
  refine ⟨?_, walked.2.1, fun loc m finEq => ⟨m, rfl, rfl, Nat.le_refl _, walked.2.2 loc m finEq⟩⟩
  intro done decoded suffix rowsEq state chain
  have decodedMem : decoded ∈ orderedRows := by
    rw [rowsEq]
    exact List.mem_append_right done List.mem_cons_self
  have groundedAligned : TimedGrounding.Grounded statement.program initial
      (Commit.initClkNat witness.data) (alignedRow decoded) :=
    TimedGrounding.grounded_of_stateRespell (canonTimePull decoded decodedMem)
      (canonPcPull decoded decodedMem)
      (walked.1 (walkRow decoded) (List.mem_map_of_mem decodedMem))
  have groundedOrdinary := TimedGrounding.grounded_ordinary_of_aligned
    (aligns decoded decodedMem) groundedAligned
  have rowTimeRaw := statePullTime_of_stateWalk _ stateWalk timeStepCanon done decoded
    suffix rowsEq
  rw [canonTimePull decoded decodedMem] at rowTimeRaw
  have rowTime : Semantics.StateMsg.timeNat
      (statePullMessage (decoded.toChipRow witness.data)) =
        Commit.initClkNat witness.data + 8 * done.length := by
    rw [boundary.initialClock]
    simpa only [decodedStateEdge, initialBoundaryStateMessage, Semantics.StateMsg.timeNat] using rowTimeRaw
  exact decoded.dynamicGrounded_of_contracts witness constraints balanced
    (sourceFacts decoded decodedMem).1 (contractAt decoded decodedMem) statement.program initial state
    (Commit.initClkNat witness.data) done.length (decodeAt decoded decodedMem) groundedOrdinary chain
    (sourceFacts decoded decodedMem).2 rowTime

/-- Dynamic grounding over the exact ordered physical rows.

Ordering, activity, registry membership, Program decode, and clock accounting are all proved outside
this theorem.  The timed walk and physical-row bridge are fully proved by
`supportedCore_orderedRows_dynamic_of_obligations`; the only admitted dependency is the explicitly
finite `supportedCore_groundingObligations_of_constraints` rollout above. -/
theorem supportedCore_orderedRows_dynamic
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (memoryTimestampRange :
      SupportedCoreMemoryTimestampRangeRelation statement witness)
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
  exact supportedCore_orderedRows_dynamic_of_obligations statement witness initial constraints balanced
    boundary memoryTimestampRange (supportedCore_groundingObligations_of_constraints witness constraints)
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
    (boundary : InitialBoundaryFacts statement witness initial)
    (memoryTimestampRange :
      SupportedCoreMemoryTimestampRangeRelation statement witness) :
    ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows := by
  obtain ⟨orderedRows, stateWalk, exhaustiveMultiset⟩ :=
    witness_realDecodedState_canonExhaustiveTrail witness constraints balanced
  rw [publicInputEq] at stateWalk
  have exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables) :=
    Multiset.coe_eq_coe.mp exhaustiveMultiset
  have goodness := (witness_stateEdges_goodness witness constraints balanced).1
  have dyn := supportedCore_orderedRows_dynamic statement witness initial constraints balanced
    boundary memoryTimestampRange orderedRows exhaustive stateWalk
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

/-- **Supported native-Clean soundness.** A satisfying, channel-balanced witness whose provider
tables are semantically bound and whose memory timestamps satisfy the
`SupportedCoreMemoryTimestampRangeRelation` bound (the third conjunct of
`SupportedCoreNativeRelation`) produces a genuine local official-Sail execution between its public
endpoints.  This deliberately concludes a shard-local segment; boot reachability is supplied later by
`supportedCoreLocalExecution_anchors` when consecutive shards are composed. -/
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model) := by
  intro statement witness valid
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, ⟨initial, boundary⟩,
    memoryTimestampRange⟩ := valid
  obtain ⟨rows, -, walk, grounded, clockCount, -, -⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary memoryTimestampRange
  apply groundedRows_localExecution model statement witness.data initial
    (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data) rows
    boundary.programWellFormed boundary.initialPc boundary.romLoaded boundary.configured
    boundary.codeMemoryCompatible walk grounded
  rw [Machine.localExecutionClock_eq_ordinary ordinary]
  exact clockCount

/-! ## Completeness boundary

Whole-machine completeness is intentionally not inferred from the `completeness` field embedded in
each `GeneralFormalCircuit`.  The real converse must start from a *supported, trace-generatable*
semantic execution, construct all table witnesses, and prove the four global channel balances.  Its
eventual shape is:

```lean
theorem supported_core_native_complete :
    WitnessRelation.Complete SupportedCoreNativeRelation
      SupportedCoreTraceGeneratableExecutionRelation := by
  -- proof deferred
```

`SupportedCoreTraceGeneratableExecutionRelation` must include decoded-opcode support, canonical witness
generation inputs, memory initialization, and provider-table obligations; using the broader
`SupportedCoreLocalExecutionRelation` would make the claim false for unsupported Sail executions.  No
placeholder theorem is declared until that relation and trace generator are verified.  This does not
require changing Clean's `GeneralFormalCircuit` representation. -/

/-! ## Full extracted target

`Soundness/CoreAIR.lean` owns the conditional
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` combinators.  Their source is the
concrete 34-table/6-table Rust relation in `Faithful/CoreAIR.lean`, not this smaller native ensemble.
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
