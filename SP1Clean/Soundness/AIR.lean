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

/-- The explicit physical range premise needed by SP1's generic RAM access-timestamp comparison.
The local `MemoryAccess` AIR constrains the selected difference to two byte-range-checked limbs, but
its Rust soundness argument additionally requires both compared components to be `< 2^24`. Low
components already carry `MemoryMsg.ClkBound`; this companion supplies the pulled high component.

This is intentionally a witness relation rather than an unconditional axiom or an ordering
assumption. The load/store contracts still derive strict order from the actual AIR equations. The
eventual exact extracted-AIR layer should prove this relation from SP1's public timestamp range
checks plus Memory permutation, or continue to disclose it as an external verifier premise. -/
def SupportedCoreMemoryTimestampRangeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun _statement witness =>
    ∀ decoded ∈ realDecodedInstructionRows witness.data witness.tables,
      MemoryPullTimestampHighBound (decoded.ordinaryRowFacts witness.data)

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

/-- The committed-decode field of every statically grounded ordered row is already discharged.
This theorem deliberately sits beside the remaining grounding seam: Program truth comes entirely
from the exact chip pulls, Clean balance, the canonical table-33 provider, and the statement binding;
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

/-- A walk of full State messages projects to the pc-only walk consumed by local execution.  The
projection is lossless for this purpose because the decoded edge is definitionally the row's State
pull/push pair. -/
theorem pcWalk_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
        PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow data)
          (Semantics.StateMsg.pcBits initial) (Semantics.StateMsg.pcBits final) rows := by
  intro initial final rows walk
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      constructor
      · rw [← congrArg Semantics.StateMsg.pcBits source]
        simp [decodedStateEdge]
      · simpa [decodedStateEdge] using ih tail

/-- A State-message walk with a row-dependent positive-width schedule has the expected endpoint
clock count.  No instruction class or fixed divisor is baked into this telescoping theorem. -/
theorem clockCount_of_decodedStateWalk_durations (data : ProverData (ZMod p))
    (duration : DecodedInstructionRow p → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + duration decoded) →
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

/-- A full State-message walk whose rows each advance eight ticks has the expected endpoint clock
count.  This is the ordinary-slice specialization of the row-dependent theorem above. -/
theorem clockCount_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8) →
      Semantics.StateMsg.timeNat initial + 8 * rows.length =
        Semantics.StateMsg.timeNat final := fun walk steps => by
  simpa [Nat.mul_comm] using clockCount_of_decodedStateWalk_durations data (fun _ => 8) walk steps

/-- The telescoping endpoint-multiset balance of a State walk: the head plus each row's push equals the
final plus each row's pull, as multisets.  The `List`-level companion of
`RankedGrounding.endpointBalanced_of_balanced`, derived directly from `IsWalk` so it carries the
`statement.publicValues` endpoints natively — the exact State-balance hypothesis `TimedGrounding.walk`
consumes (after mapping `decodedStateEdge` onto the aligned carrier's `statePush`/`statePull`). -/
theorem endpointBalance_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      initial ::ₘ (↑(rows.map (fun d => (decodedStateEdge data d).2)) :
          Multiset (Channels.StateMsg (ZMod p)))
        = final ::ₘ ↑(rows.map (fun d => (decodedStateEdge data d).1)) := by
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
theorem statePullTime_of_decodedStateWalk_durations (data : ProverData (ZMod p))
    (duration : DecodedInstructionRow p → ℕ) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + duration decoded) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 =
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
          Semantics.StateMsg.timeNat (decodedStateEdge data row).2 =
            Semantics.StateMsg.timeNat (decodedStateEdge data row).1 + duration row := by
        intro row rowMem
        exact steps row (List.mem_cons_of_mem head rowMem)
      have position := ih tail tailSteps decoded suffix rfl
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The State walk and each chip's proved `+8` clock contract locate every exact decoded row at its
prefix length. This is the ordinary-slice specialization consumed by shard-local Memory currency. -/
theorem statePullTime_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 =
          Semantics.StateMsg.timeNat initial + 8 * done.length :=
  fun walk steps done decoded suffix rowsEq => by
    simpa [Nat.mul_comm] using
      statePullTime_of_decodedStateWalk_durations data (fun _ => 8) walk steps done decoded suffix
        rowsEq

/-- Every row of the eight-tick State walk begins in the same residue class modulo eight as the
public initial State record.  This is the `RowOK.align8` input of the timed Memory walk. -/
theorem statePullAlign8_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8) →
      ∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 % 8 =
          Semantics.StateMsg.timeNat initial % 8 := by
  intro initial final rows walk steps decoded decodedMem
  obtain ⟨done, suffix, rowsEq⟩ := List.append_of_mem decodedMem
  have position := statePullTime_of_decodedStateWalk data walk steps done decoded suffix rowsEq
  rw [position]
  omega

/-- Generic closure of the ordered-row dynamic seam.  The proof chooses each chip's aligned carrier,
feeds the seven explicit inputs of `TimedGrounding.walk`, transports its result back to the ordinary
physical-row carrier, and invokes the chip's retained Clean soundness/Sail bridge.  What remains after
this theorem is the finite `SupportedCoreGroundingObligations` rollout, not another semantic premise. -/
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
    (stateWalk : Walk.IsWalk (decodedStateEdge witness.data)
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows) :
    ∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state := by
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
      (memoryTimestampRange decoded (exhaustive.mem_iff.mp decodedMem))
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
    · have aligned := statePullAlign8_of_decodedStateWalk witness.data stateWalk timeStep decoded
          decodedMem
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
  have stepFacts : ∀ row ∈ orderedRows.map alignedRow,
      Semantics.LocalStepFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.localStepFact_align_of_ordinary (aligns decoded decodedMem)
      (engineFacts decoded decodedMem).1
  have frameFacts : ∀ row ∈ orderedRows.map alignedRow,
      TimedGrounding.FrameFact statement.program initial (Commit.initClkNat witness.data) row := by
    intro row rowMem
    obtain ⟨decoded, decodedMem, rfl⟩ := List.mem_map.mp rowMem
    exact TimedGrounding.frameFact_align_of_ordinary (aligns decoded decodedMem)
      (engineFacts decoded decodedMem).2
  have stateBalance :
      initialBoundaryStateMessage statement.publicValues ::ₘ
          (↑((orderedRows.map alignedRow).map (·.statePush)) :
            Multiset (Channels.StateMsg (ZMod p))) =
        finalBoundaryStateMessage statement.publicValues ::ₘ
          ↑((orderedRows.map alignedRow).map (·.statePull)) := by
    have pushMap : (orderedRows.map alignedRow).map (·.statePush) =
        orderedRows.map (fun decoded => (decodedStateEdge witness.data decoded).2) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro decoded decodedMem
      rfl
    have pullMap : (orderedRows.map alignedRow).map (·.statePull) =
        orderedRows.map (fun decoded => (decodedStateEdge witness.data decoded).1) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro decoded decodedMem
      rfl
    rw [pushMap, pullMap]
    exact endpointBalance_of_decodedStateWalk witness.data stateWalk
  have memoryBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          TimedGrounding.pushesAt (orderedRows.map alignedRow) loc =
        TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          TimedGrounding.pullsAt (orderedRows.map alignedRow) loc := by
    intro loc
    exact memoryBalance_of_alignsWith witness balanced obligations.memoryMultiplicityBinary
      (initPure witness constraints) (finPure witness constraints) boundary.memoryProviderUnique
      boundary.memoryFinalizeProviderUnique obligations.paddingMemoryEmpty orderedRows exhaustive
      alignedRow aligns loc
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
    orderedRows.length (orderedRows.map alignedRow)
    (initialBoundaryStateMessage statement.publicValues) (memoryInitFrontier witness)
    (by simp only [List.length_map]) stepFacts frameFacts rowOK boundary.localStateTruth
    liveAtHead stateBalance memoryBalance
  intro done decoded suffix rowsEq state chain
  have decodedMem : decoded ∈ orderedRows := by
    rw [rowsEq]
    exact List.mem_append_right done List.mem_cons_self
  have groundedAligned : TimedGrounding.Grounded statement.program initial
      (Commit.initClkNat witness.data) (alignedRow decoded) :=
    walked.1 (alignedRow decoded) (List.mem_map_of_mem decodedMem)
  have groundedOrdinary := TimedGrounding.grounded_ordinary_of_aligned
    (aligns decoded decodedMem) groundedAligned
  have rowTimeRaw := statePullTime_of_decodedStateWalk witness.data stateWalk timeStep done decoded
    suffix rowsEq
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
    (stateWalk : Walk.IsWalk (decodedStateEdge witness.data)
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows) :
    ∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state := by
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
    witness_realDecodedState_exhaustiveTrail witness constraints balanced
  rw [publicInputEq] at stateWalk
  have exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables) :=
    Multiset.coe_eq_coe.mp exhaustiveMultiset
  refine ⟨orderedRows, exhaustive, ?_, ?_, ?_⟩
  · simpa [initialBoundaryStateMessage, finalBoundaryStateMessage,
      Semantics.StateMsg.pcBits, supportedPcBits] using
      pcWalk_of_decodedStateWalk witness.data stateWalk
  · exact {
      static := supportedCore_orderedRows_static statement witness constraints balanced boundary
        orderedRows exhaustive
      dynamic := supportedCore_orderedRows_dynamic statement witness initial constraints balanced
        boundary memoryTimestampRange orderedRows exhaustive stateWalk }
  · have clockCount := clockCount_of_decodedStateWalk witness.data stateWalk
      (fun decoded decodedMem =>
        witness_realDecodedInstructionRows_timeStep witness constraints balanced decoded
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
  obtain ⟨rows, -, walk, grounded, clockCount⟩ :=
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
