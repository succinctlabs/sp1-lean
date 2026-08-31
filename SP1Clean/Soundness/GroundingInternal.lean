import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.ProviderBindings
import SP1Clean.Soundness.TimedGrounding
import SP1Clean.Soundness.LocalExecution
import SP1Clean.Soundness.MemoryBoundaryTruth
import SP1Clean.Soundness.RowSoundness
import SP1Clean.Soundness.TypedProgram
import SP1Clean.Soundness.TypedTimeContracts
import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.FetchDiscriminant
import SP1Clean.Soundness.ExitAccounting
import SP1Clean.Soundness.RefreshWiring

/-! # The timed-grounding interior

Proof-transport machinery between the physical AIR witness and the semantic grounding
certificate: the finite per-chip obligations rollout, the `SupportedCoreGrounding` record, the
canonical State-walk lemmas, and the two `supportedCore_orderedRows_*` assembly theorems
culminating in `supported_core_witness_grounding`.

Everything here is **proof-layer shape, not audit surface**: `SupportedCoreGrounding`'s
`exhaustive`/`walk`/`grounded` fields are the ordered-rows transport the induction needs, while
its `finalStateTruth`/`memoryFinalizeTruth` fields are the consumer-facing content that
`Soundness/AIR.lean`'s public `supported_core_native_grounding` re-exports.  The public relations
and capstones live in `Soundness/AIR.lean`; read that file first. -/

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


private theorem mapFilterComm {α β : Type*} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).filter q = (l.filter fun a => q (f a)).map f := by
  rw [List.filter_map]
  rfl

/-- Membership in a `List.sum` of per-element multisets (a local copy of `RefreshWiring`'s private
helper). -/
private theorem memListSumMap {α : Type*} {β : Type} (f : α → Multiset β) :
    ∀ (l : List α) (b : β), b ∈ (l.map f).sum ↔ ∃ a ∈ l, b ∈ f a
  | [], b => by simp
  | a :: l, b => by
      rw [List.map_cons, List.sum_cons, Multiset.mem_add, memListSumMap f l b]
      constructor
      · rintro (h | ⟨a', h1, h2⟩)
        · exact ⟨a, List.mem_cons_self, h⟩
        · exact ⟨a', List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨a', h1, h2⟩
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inl h2
        · exact Or.inr ⟨a', h1, h2⟩

/-- A Memory record with the literal `x5` register address shape decodes to that register.
Stated per halt-row index over an **opaque** message so the numeral cast never runs inside the
halted assembly's (very large) local context. -/
private theorem locOf_reg5 (m : Channels.MemoryMsg (ZMod p))
    (h0 : m.addr0 = 5) (h1 : m.addr1 = 0) (h2 : m.addr2 = 0) :
    Semantics.MemoryMsg.locOf m = Semantics.MemLoc.reg (5 : BitVec 5) := by
  refine Semantics.MemoryMsg.locOf_register m (5 : BitVec 5) ?_ h1 h2
  rw [h0, show ((5 : BitVec 5).toNat : ℕ) = (5 : ℕ) from rfl]
  norm_cast

/-- A Memory record with the literal `x10` register address shape decodes to that register.
Stated per halt-row index over an **opaque** message so the numeral cast never runs inside the
halted assembly's (very large) local context. -/
private theorem locOf_reg10 (m : Channels.MemoryMsg (ZMod p))
    (h0 : m.addr0 = 10) (h1 : m.addr1 = 0) (h2 : m.addr2 = 0) :
    Semantics.MemoryMsg.locOf m = Semantics.MemLoc.reg (10 : BitVec 5) := by
  refine Semantics.MemoryMsg.locOf_register m (10 : BitVec 5) ?_ h1 h2
  rw [h0, show ((10 : BitVec 5).toNat : ℕ) = (10 : ℕ) from rfl]
  norm_cast

/-- A Memory record with the literal `x11` register address shape decodes to that register.
Stated per halt-row index over an **opaque** message so the numeral cast never runs inside the
halted assembly's (very large) local context. -/
private theorem locOf_reg11 (m : Channels.MemoryMsg (ZMod p))
    (h0 : m.addr0 = 11) (h1 : m.addr1 = 0) (h2 : m.addr2 = 0) :
    Semantics.MemoryMsg.locOf m = Semantics.MemLoc.reg (11 : BitVec 5) := by
  refine Semantics.MemoryMsg.locOf_register m (11 : BitVec 5) ?_ h1 h2
  rw [h0, show ((11 : BitVec 5).toNat : ℕ) = (11 : ℕ) from rfl]
  norm_cast


omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Unpack one member of a batched per-location touch-pair aggregate. -/
private theorem mem_touchPairsAt {ts : List (List (TimedGrounding.Touch p))}
    {loc : Semantics.MemLoc}
    {q : Channels.MemoryMsg (ZMod p) × Channels.MemoryMsg (ZMod p)}
    (h : q ∈ touchPairsAt ts loc) :
    ∃ l ∈ ts, ∃ tc ∈ l,
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2 = loc ∧
        ((tc : TimedGrounding.Touch p).1.1, (tc : TimedGrounding.Touch p).2) = q := by
  rw [touchPairsAt] at h
  obtain ⟨l, lMem, hin⟩ := (memListSumMap _ ts q).mp h
  obtain ⟨tc, tcMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hin)
  exact ⟨l, lMem, tc, List.mem_of_mem_filter tcMem,
    by simpa using List.of_mem_filter tcMem, rfl⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- A per-touch rewrite keeps every pushed record, hence the whole pushed-location inventory. -/
private theorem touchRewrite_snd_map {β γ : Type} (f : Channels.MemoryMsg (ZMod p) → γ)
    (value : Channels.MemoryMsg (ZMod p) → β) (time : Channels.MemoryMsg (ZMod p) → ℕ) :
    ∀ (l l' : List (TimedGrounding.Touch p)),
      List.Forall₂ (TouchRewrite value time) l l' →
        l'.map (fun tc => f (tc : TimedGrounding.Touch p).2) =
          l.map (fun tc => f (tc : TimedGrounding.Touch p).2)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l, b :: l', h => by
      cases h with
      | cons hab htail =>
          rw [List.map_cons, List.map_cons, touchRewrite_snd_map f value time l l' htail, hab.2.1]

/-! ## The semantic grounding certificate and its assembly -/

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
  /-- Every memory-finalize provider record is true of the constructed run.  The two direct
  conjuncts are the boundary-facing content: the record sits at its key, and its committed value is
  the execution's **current content of that location at the committed final clock**
  (`Semantics.LocalValueAt` at the final State time — the walk invariant's value currency,
  previously discarded at the end of the walk).  The ∃-witness tail is the timed form: with
  MemoryBump timestamp-refresh rows in the ensemble the walk concludes record-level truth for the
  *refresh-eliminated* record (same location and value, earlier time, bounded by the committed
  final clock); on a shard with no active refresh row the witness is the record itself.  The
  committed record's own timestamp is deliberately **not** claimed to be shard-bounded — the
  native MemoryBump table does not tie its refreshed clock to the public final clock, and the
  populated memory boundary stores the refresh-eliminated time instead. -/
  memoryFinalizeTruth : ∀ loc m, memoryFinalizeFrontier witness loc = some m →
    Semantics.MemoryMsg.locOf m = loc ∧
    Semantics.LocalValueAt initial (Commit.initClkNat witness.data) loc
      (Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues)) m.value ∧
    ∃ m', Semantics.MemoryMsg.locOf m' = loc ∧
      m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
      Semantics.MemoryMsg.timeNat m' ≤
        Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues) ∧
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
  have truth := decoded.programTruth_of_active witness constraints balanced
    boundary.programProvider sourceMem.1 sourceMem.2
    (witness_realDecodedInstructionRows_opcodeNeEcall witness constraints balanced decoded
      sourceMem.1 sourceMem.2)
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
    (initial : SailState) (fin : Channels.StateMsg (ZMod p))
    (initTimeLt : Semantics.StateMsg.timeNat
      (initialBoundaryStateMessage statement.publicValues) < 2 ^ 48)
    (finalTimeLt : Semantics.StateMsg.timeNat fin < 2 ^ 48)
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
      fin orderedRows)
    (haltTouches : List (TimedGrounding.Touch p))
    (haltProducedEq : producedMessages (typedTableInteractionsWith (haltTable witness)
      Channels.memoryChannel) =
        haltTouches.map (fun tc => (tc : TimedGrounding.Touch p).2))
    (haltConsumedEq : consumedMessages (typedTableInteractionsWith (haltTable witness)
      Channels.memoryChannel) =
        haltTouches.map (fun tc => (tc : TimedGrounding.Touch p).1.1))
    (haltLocEq : ∀ tc ∈ haltTouches,
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1 =
        Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2)
    (haltValEq : ∀ tc ∈ haltTouches,
      ((tc : TimedGrounding.Touch p).1.1).value = ((tc : TimedGrounding.Touch p).2).value)
    (haltLocsNodup : (haltTouches.map (fun tc =>
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2)).Nodup)
    (haltPushGood : ∀ tc ∈ haltTouches,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).2 ∧
        ((tc : TimedGrounding.Touch p).2).clk_high.val < 2 ^ 24)
    (haltPushLate : ∀ tc ∈ haltTouches,
      Semantics.StateMsg.timeNat fin <
        Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).2)
    (haltSlot : ∀ tc ∈ haltTouches,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 →
        ((tc : TimedGrounding.Touch p).1.1).clk_high.val < 2 ^ 24 →
          Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).1.1 <
            Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).2) :
    (∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state) ∧
      Semantics.LocalStateTruth statement.program initial (Commit.initClkNat witness.data)
        fin ∧
      (∀ loc m, memoryFinalizeFrontier witness loc = some m →
        Semantics.MemoryMsg.locOf m = loc ∧
        Semantics.LocalValueAt initial (Commit.initClkNat witness.data) loc
          (Semantics.StateMsg.timeNat fin) m.value ∧
        ∃ m', Semantics.MemoryMsg.locOf m' = loc ∧
          m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
          Semantics.MemoryMsg.timeNat m' ≤
            Semantics.StateMsg.timeNat fin ∧
          Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m') ∧
      (∀ tc ∈ haltTouches,
        Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 ∧
        ((tc : TimedGrounding.Touch p).1.1).clk_high.val < 2 ^ 24 ∧
        Word.isU64 ((tc : TimedGrounding.Touch p).1.1).value ∧
        Semantics.LocalValueAt initial (Commit.initClkNat witness.data)
          (Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1)
          (Semantics.StateMsg.timeNat fin)
          ((tc : TimedGrounding.Touch p).1.1).value) := by
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
  have clockCount := clockCount_of_stateWalk _ stateWalk timeStepCanon
  have rowWindowLt : ∀ decoded ∈ orderedRows,
      Semantics.StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull + 8 ≤
        Semantics.StateMsg.timeNat fin := by
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
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))) +
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (haltTable witness)
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))),
      Channels.MemoryMsg.ClkBound m ∧ m.clk_high.val < 2 ^ 24 := by
    intro loc m memberM
    rcases Multiset.mem_add.mp memberM with frontierRowOrBump | haltPush
    swap
    · -- the halt row's own read-back: its access clock is in the syscall window
      rw [Multiset.mem_filter, Multiset.mem_coe, haltProducedEq] at haltPush
      obtain ⟨tc, tcMem, rfl⟩ := List.mem_map.mp haltPush.1
      exact haltPushGood tc tcMem
    rcases Multiset.mem_add.mp frontierRowOrBump with frontierOrRow | bumpPush
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
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))) +
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (haltTable witness)
            Channels.memoryChannel)) : Multiset (Channels.MemoryMsg (ZMod p))),
      Channels.MemoryMsg.ClkBound m ∧ m.clk_high.val < 2 ^ 24 :=
    fun loc => forall_mem_of_balance (widened loc) (pushGood loc)
  have haltPullGood : ∀ tc ∈ haltTouches,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 ∧
        ((tc : TimedGrounding.Touch p).1.1).clk_high.val < 2 ^ 24 := by
    intro tc tcMem
    refine pullGood (Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1) _
      (Multiset.mem_add.mpr (Or.inr ?_))
    rw [Multiset.mem_filter, Multiset.mem_coe, haltConsumedEq]
    exact ⟨List.mem_map_of_mem tcMem, rfl⟩
  have alignedPullGood : ∀ decoded ∈ orderedRows, ∀ tc ∈ touchesOf decoded,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 ∧
        (tc : TimedGrounding.Touch p).1.1.clk_high.val < 2 ^ 24 := by
    intro decoded decodedMem tc touchMem
    refine pullGood _ _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inr
        (mem_pullsAt.mpr ⟨⟨alignedRow decoded, List.mem_map_of_mem decodedMem, tc.1, ?_,
          rfl⟩, rfl⟩)))))))
    exact List.mem_map_of_mem touchMem
  have ordinaryPullGood : ∀ decoded ∈ orderedRows,
      ∀ mp ∈ (decoded.ordinaryRowFacts witness.data).memPulls,
        Channels.MemoryMsg.ClkBound (mp : Channels.MemoryMsg (ZMod p) × ℕ).1 := by
    intro decoded decodedMem mp pullMem
    obtain ⟨mp', alignedMem, priorEq⟩ := List.mem_map.mp
      ((aligns decoded decodedMem).pulls.mem_iff.mpr (List.mem_map_of_mem pullMem))
    exact (pullGood (Semantics.MemoryMsg.locOf mp.1) mp.1 (Multiset.mem_add.mpr (Or.inl
      (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (mem_pullsAt.mpr
        ⟨⟨alignedRow decoded, List.mem_map_of_mem decodedMem, mp', alignedMem, priorEq⟩,
          rfl⟩)))))))).1
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
    have good := pullGood _ _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
      (Or.inr pulledMem))))
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
  -- Structural facts about batched touch-pair aggregates: the append split and the singleton
  -- block, plus the filter-singleton consequence of per-location uniqueness.
  have touchPairsAt_append : ∀ (ts₁ ts₂ : List (List (TimedGrounding.Touch p)))
      (loc : Semantics.MemLoc),
      touchPairsAt (ts₁ ++ ts₂) loc = touchPairsAt ts₁ loc + touchPairsAt ts₂ loc := by
    intro ts₁ ts₂ loc
    rw [touchPairsAt, touchPairsAt, touchPairsAt, List.map_append, List.sum_append]
  have touchPairsAt_singleton : ∀ (l : List (TimedGrounding.Touch p)) (loc : Semantics.MemLoc),
      touchPairsAt [l] loc =
        ↑((l.filter fun pq => Semantics.MemoryMsg.locOf (pq : TimedGrounding.Touch p).2 =
            loc).map fun tc => ((tc : TimedGrounding.Touch p).1.1, tc.2)) := by
    intro l loc
    simp [touchPairsAt]
  have filterSingleton : ∀ (l : List (TimedGrounding.Touch p)),
      (l.map (fun tc => Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2)).Nodup →
      ∀ a ∈ l,
        (l.filter fun x => Semantics.MemoryMsg.locOf (x : TimedGrounding.Touch p).2 =
          Semantics.MemoryMsg.locOf (a : TimedGrounding.Touch p).2) = [a] := by
    intro l
    induction l with
    | nil =>
        intro _ a ha
        exact absurd ha List.not_mem_nil
    | cons b l ih =>
        intro hnd a ha
        rw [List.map_cons, List.nodup_cons] at hnd
        rcases List.mem_cons.mp ha with rfl | haTail
        · rw [List.filter_cons_of_pos (by simp)]
          have tail : (l.filter fun x =>
              Semantics.MemoryMsg.locOf (x : TimedGrounding.Touch p).2 =
                Semantics.MemoryMsg.locOf (a : TimedGrounding.Touch p).2) = [] := by
            rw [List.filter_eq_nil_iff]
            intro x hx
            simp only [decide_eq_true_eq]
            intro hEq
            exact hnd.1 (hEq ▸ List.mem_map_of_mem hx)
          rw [tail]
        · rw [List.filter_cons_of_neg (by
            simp only [decide_eq_true_eq]
            intro hEq
            exact hnd.1 (hEq ▸ List.mem_map_of_mem haTail)), ih hnd.2 a haTail]
  -- The widened balance in the per-location touch-pair form, with the halt row's touches appended
  -- as one more touch list.
  have touchBalanceAll : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          (touchPairsAt (orderedRows.map touchesOf ++ [haltTouches]) loc).map Prod.snd +
          Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
            (↑(bump.map Prod.snd) : Multiset (Channels.MemoryMsg (ZMod p))) =
        TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          (touchPairsAt (orderedRows.map touchesOf ++ [haltTouches]) loc).map Prod.fst +
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
    have haltSnd : (touchPairsAt [haltTouches] loc).map Prod.snd =
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(haltTouches.map (fun tc => (tc : TimedGrounding.Touch p).2)) :
            Multiset (Channels.MemoryMsg (ZMod p))) := by
      rw [touchPairsAt_singleton, Multiset.map_coe, List.map_map, Multiset.filter_coe,
        mapFilterComm]
      rfl
    have haltFst : (touchPairsAt [haltTouches] loc).map Prod.fst =
        Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(haltTouches.map (fun tc => (tc : TimedGrounding.Touch p).1.1)) :
            Multiset (Channels.MemoryMsg (ZMod p))) := by
      rw [touchPairsAt_singleton, Multiset.map_coe, List.map_map, Multiset.filter_coe,
        mapFilterComm,
        show (haltTouches.filter fun tc =>
            Semantics.MemoryMsg.locOf ((fun tc : TimedGrounding.Touch p =>
              (tc : TimedGrounding.Touch p).1.1) tc) = loc) =
          (haltTouches.filter fun pq =>
            Semantics.MemoryMsg.locOf (pq : TimedGrounding.Touch p).2 = loc) from
          List.filter_congr fun tc htc => by
            rw [haltLocEq tc htc]]
      rfl
    rw [touchPairsAt_append, Multiset.map_add, Multiset.map_add, haltSnd, haltFst,
      bumpSnd, bumpFst, ← pushBridge, ← pullBridge, ← haltProducedEq, ← haltConsumedEq]
    have widenedLoc := widened loc
    calc TimedGrounding.optMS (memoryInitFrontier witness loc) +
          (TimedGrounding.pushesAt (orderedRows.map alignedRow) loc +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(producedMessages (typedTableInteractionsWith (haltTable witness)
                Channels.memoryChannel)))) +
          Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
            (↑(producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              Channels.memoryChannel)))
        = TimedGrounding.optMS (memoryInitFrontier witness loc) +
            TimedGrounding.pushesAt (orderedRows.map alignedRow) loc +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(producedMessages (typedTableInteractionsWith (memoryBumpTable witness)
                Channels.memoryChannel))) +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(producedMessages (typedTableInteractionsWith (haltTable witness)
                Channels.memoryChannel))) := by
          abel
      _ = TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
            TimedGrounding.pullsAt (orderedRows.map alignedRow) loc +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
                Channels.memoryChannel))) +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(consumedMessages (typedTableInteractionsWith (haltTable witness)
                Channels.memoryChannel))) := widenedLoc
      _ = TimedGrounding.optMS (memoryFinalizeFrontier witness loc) +
          (TimedGrounding.pullsAt (orderedRows.map alignedRow) loc +
            Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
              (↑(consumedMessages (typedTableInteractionsWith (haltTable witness)
                Channels.memoryChannel)))) +
          Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
            (↑(consumedMessages (typedTableInteractionsWith (memoryBumpTable witness)
              Channels.memoryChannel))) := by
          abel
  -- Eliminate the refresh pairs and realize the rewritten pulls row by row; then split the
  -- rewritten batch back into the instruction prefix and the halt entry.
  obtain ⟨tsAll', finalFrontier, rewrittenAll, refreshFreeBalance, finalRewrite⟩ :=
    exists_refreshFreeTouchLists
      (fun m : Channels.MemoryMsg (ZMod p) => (Semantics.MemoryMsg.locOf m, m.value))
      Semantics.MemoryMsg.timeNat (orderedRows.map touchesOf ++ [haltTouches])
      (memoryInitFrontier witness)
      (memoryFinalizeFrontier witness) bump bumpRefresh' bumpLoc touchBalanceAll
  have flipAll := List.Forall₂.flip rewrittenAll
  have instrRewFlipped := List.forall₂_take_append _ _ _ flipAll
  have haltRewFlipped := List.forall₂_drop_append _ _ _ flipAll
  obtain ⟨haltTouches', tailT, haltRewritten, tailRel, dropEq⟩ :=
    List.forall₂_cons_right_iff.mp haltRewFlipped
  obtain rfl : tailT = [] := List.forall₂_nil_right_iff.mp tailRel
  have rewritten := List.Forall₂.flip instrRewFlipped
  have tsAllSplit : tsAll' =
      tsAll'.take (orderedRows.map touchesOf).length ++ [haltTouches'] := by
    conv_lhs => rw [← List.take_append_drop (orderedRows.map touchesOf).length tsAll']
    rw [dropEq]
  rw [tsAllSplit] at refreshFreeBalance
  set ts' := tsAll'.take (orderedRows.map touchesOf).length with ts'Def
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
        fin ::ₘ
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
  -- The rewritten halt entry's per-touch data: pushes are kept verbatim, pulls are rewritten to
  -- same-location same-value priors at no-later times.
  have haltRewriteFacts : ∀ tc' ∈ haltTouches', ∃ tc ∈ haltTouches,
      PullRewrite tc tc' := by
    intro tc' tc'Mem
    obtain ⟨tc, tcMem, hrw⟩ := TimedGrounding.forall₂_exists_left haltRewritten tc' tc'Mem
    exact ⟨tc, tcMem, pullRewrite_of_touchRewrite hrw⟩
  -- The push-location inventory of the rewritten halt entry is the original one, hence nodup.
  have haltLocs'Eq : haltTouches'.map (fun tc =>
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2) =
      haltTouches.map (fun tc => Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2) :=
    touchRewrite_snd_map Semantics.MemoryMsg.locOf _ _ haltTouches haltTouches' haltRewritten
  have haltLocs'Nodup : (haltTouches'.map (fun tc =>
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2)).Nodup := by
    rw [haltLocs'Eq]
    exact haltLocsNodup
  -- Every rewritten instruction push and pull stays at or below the committed final time.
  have instrPushLe : ∀ q ∈ pairs, ∀ tc' ∈ (q :
        DecodedInstructionRow p × List (TimedGrounding.Touch p)).2,
      Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).2 ≤
        Semantics.StateMsg.timeNat fin := by
    intro q memberQ tc' touchMem'
    obtain ⟨rowMem, rewrite⟩ := pairFacts q memberQ
    obtain ⟨tc₀, touchMem₀, -, hpush, -, -, -⟩ :=
      TimedGrounding.forall₂_exists_left rewrite tc' touchMem'
    have evidence := touchesOf_spec q.1 rowMem
    have windowHi := (evidence.2.1 tc₀ touchMem₀).push_hi
    have windowLt := rowWindowLt q.1 rowMem
    rw [hpush]
    omega
  have instrPullLe : ∀ q ∈ pairs, ∀ tc' ∈ (q :
        DecodedInstructionRow p × List (TimedGrounding.Touch p)).2,
      Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).1.1 ≤
        Semantics.StateMsg.timeNat fin := by
    intro q memberQ tc' touchMem'
    obtain ⟨rowMem, rewrite⟩ := pairFacts q memberQ
    obtain ⟨tc₀, touchMem₀, -, -, -, -, htime⟩ :=
      TimedGrounding.forall₂_exists_left rewrite tc' touchMem'
    have evidence := touchesOf_spec q.1 rowMem
    have slot := evidence.2.2.2.2 tc₀ touchMem₀
      (alignedPullGood q.1 rowMem tc₀ touchMem₀).1 (alignedPullGood q.1 rowMem tc₀ touchMem₀).2
    have windowHi := (evidence.2.1 tc₀ touchMem₀).push_hi
    have windowLt := rowWindowLt q.1 rowMem
    omega
  -- Every rewritten halt pull is strictly earlier than its own (any halt) read-back at its
  -- location: the rewrite is time-nonincreasing and the original slot fact is discharged by the
  -- balance-derived pulled-record facts.
  have haltPullLt : ∀ tc' ∈ haltTouches',
      Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).1.1 <
        Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).2 := by
    intro tc' tc'Mem
    obtain ⟨tc, tcMem, -, hpush, -, -, htime⟩ := haltRewriteFacts tc' tc'Mem
    have slot := haltSlot tc tcMem (haltPullGood tc tcMem).1 (haltPullGood tc tcMem).2
    rw [hpush]
    omega
  -- **The forcing step**: at each halt-touched location the eliminated finalize frontier is the
  -- halt row's own read-back — it is the unique maximal-time record of the refresh-free balance.
  have haltForced : ∀ tc' ∈ haltTouches',
      finalFrontier (Semantics.MemoryMsg.locOf (tc' : TimedGrounding.Touch p).2) =
        some (tc' : TimedGrounding.Touch p).2 := by
    intro tc' tc'Mem
    obtain ⟨tc, tcMem, -, hpushEq, -, -, -⟩ := haltRewriteFacts tc' tc'Mem
    have lateFin : Semantics.StateMsg.timeNat
        fin <
        Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).2 := by
      rw [hpushEq]
      exact haltPushLate tc tcMem
    set loc := Semantics.MemoryMsg.locOf (tc' : TimedGrounding.Touch p).2 with locDef
    have pushMem : (tc' : TimedGrounding.Touch p).2 ∈
        TimedGrounding.optMS (memoryInitFrontier witness loc) +
          (touchPairsAt (ts' ++ [haltTouches']) loc).map Prod.snd := by
      refine Multiset.mem_add.mpr (Or.inr ?_)
      rw [touchPairsAt_append, Multiset.map_add]
      refine Multiset.mem_add.mpr (Or.inr ?_)
      rw [touchPairsAt_singleton, Multiset.map_coe, List.map_map]
      refine Multiset.mem_coe.mpr (List.mem_map.mpr ⟨tc', List.mem_filter.mpr ⟨tc'Mem, ?_⟩, rfl⟩)
      simp [locDef]
    rw [refreshFreeBalance loc] at pushMem
    rcases Multiset.mem_add.mp pushMem with finMem | pullMem
    · exact (TimedGrounding.mem_optMS.mp finMem).symm ▸ rfl
    · exfalso
      rw [touchPairsAt_append, Multiset.map_add] at pullMem
      rcases Multiset.mem_add.mp pullMem with instrMem | haltMem
      · -- an instruction pull can never sit past the committed final time
        obtain ⟨pair, pairMem, pairEq⟩ := Multiset.mem_map.mp instrMem
        obtain ⟨l, lMem, tc₁, tc₁Mem, -, tcEq⟩ := mem_touchPairsAt pairMem
        obtain ⟨q, qMem, rfl⟩ : ∃ q ∈ pairs,
            (q : DecodedInstructionRow p × List (TimedGrounding.Touch p)).2 = l := by
          rw [← pairsSnd] at lMem
          obtain ⟨q, qMem, hq⟩ := List.mem_map.mp lMem
          exact ⟨q, qMem, hq⟩
        have hle := instrPullLe q qMem tc₁ tc₁Mem
        have hEq : (tc₁ : TimedGrounding.Touch p).1.1 = (tc' : TimedGrounding.Touch p).2 := by
          rw [← pairEq, ← tcEq]
        rw [hEq] at hle
        omega
      · -- another halt pull at this location shares the original touch, so it is strictly earlier
        obtain ⟨pair, pairMem, pairEq⟩ := Multiset.mem_map.mp haltMem
        obtain ⟨l, lMem, tc₁, tc₁Mem', hloc₁, tcEq⟩ := mem_touchPairsAt pairMem
        obtain rfl : l = haltTouches' := by simpa using lMem
        have hlt := haltPullLt tc₁ tc₁Mem'
        obtain ⟨tc₂, tc₂Mem, -, hpush₂, -, -, -⟩ := haltRewriteFacts tc₁ tc₁Mem'
        have origLocEq : Semantics.MemoryMsg.locOf (tc₂ : TimedGrounding.Touch p).2 =
            Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2 := by
          rw [← hpush₂, hloc₁, locDef, hpushEq]
        have origEq : tc₂ = tc :=
          List.inj_on_of_nodup_map haltLocsNodup tc₂Mem tcMem origLocEq
        have hEq' : Semantics.MemoryMsg.timeNat (tc₁ : TimedGrounding.Touch p).1.1 =
            Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).2 :=
          congrArg Semantics.MemoryMsg.timeNat (by rw [← pairEq, ← tcEq])
        have hpushTimeEq : Semantics.MemoryMsg.timeNat (tc₁ : TimedGrounding.Touch p).2 =
            Semantics.MemoryMsg.timeNat (tc' : TimedGrounding.Touch p).2 := by
          rw [hpush₂, origEq, ← hpushEq]
        omega
  -- The walk's final memory frontier: the rewritten halt pull at halt-touched locations, the
  -- eliminated finalize frontier elsewhere.
  have finM'mem : ∀ (loc : Semantics.MemLoc) (tc' : TimedGrounding.Touch p),
      haltTouches'.find? (fun tc₁ =>
        Semantics.MemoryMsg.locOf (tc₁ : TimedGrounding.Touch p).2 = loc) = some tc' →
        tc' ∈ haltTouches' ∧
          Semantics.MemoryMsg.locOf (tc' : TimedGrounding.Touch p).2 = loc := by
    intro loc tc' hfind
    refine ⟨List.mem_of_find?_eq_some hfind, ?_⟩
    have := List.find?_some hfind
    simpa using this
  set finM' : Semantics.MemLoc → Option (Channels.MemoryMsg (ZMod p)) := fun loc =>
    match haltTouches'.find? (fun tc₁ =>
      Semantics.MemoryMsg.locOf (tc₁ : TimedGrounding.Touch p).2 = loc) with
    | some tc' => some (tc' : TimedGrounding.Touch p).1.1
    | none => finalFrontier loc
    with finM'Def
  have memoryBalance : ∀ loc : Semantics.MemLoc,
      TimedGrounding.optMS (memoryInitFrontier witness loc) +
          TimedGrounding.pushesAt (pairs.map walkRow) loc =
        TimedGrounding.optMS (finM' loc) +
          TimedGrounding.pullsAt (pairs.map walkRow) loc := by
    intro loc
    have walkPushEq : ∀ q ∈ pairs, (walkRow q).memPushes = (Prod.snd q).map Prod.snd :=
      fun _ _ => rfl
    have walkPullEq : ∀ q ∈ pairs, (walkRow q).memPulls = (Prod.snd q).map Prod.fst :=
      fun _ _ => rfl
    have pushBridge := pushesAt_of_touchLists pairs walkRow Prod.snd walkPushEq loc
    have pullBridge := pullsAt_of_touchLists pairs walkRow Prod.snd walkPullEq rewrittenLoc loc
    rw [pushBridge, pullBridge, pairsSnd]
    have balanceLoc := refreshFreeBalance loc
    rw [touchPairsAt_append, Multiset.map_add, Multiset.map_add] at balanceLoc
    cases hfind : haltTouches'.find? (fun tc₁ =>
        Semantics.MemoryMsg.locOf (tc₁ : TimedGrounding.Touch p).2 = loc) with
    | none =>
        have haltEmpty : (haltTouches'.filter fun pq =>
            Semantics.MemoryMsg.locOf (pq : TimedGrounding.Touch p).2 = loc) = [] := by
          rw [List.filter_eq_nil_iff]
          intro tc₁ tc₁Mem
          have := List.find?_eq_none.mp hfind tc₁ tc₁Mem
          simpa using this
        rw [touchPairsAt_singleton, haltEmpty] at balanceLoc
        simp only [List.map_nil, Multiset.coe_nil, Multiset.map_zero, add_zero] at balanceLoc
        rw [show finM' loc = finalFrontier loc from by rw [finM'Def]; simp [hfind]]
        exact balanceLoc
    | some tc' =>
        obtain ⟨tc'Mem, tc'Loc⟩ := finM'mem loc tc' hfind
        have haltFilter : (haltTouches'.filter fun pq =>
            Semantics.MemoryMsg.locOf (pq : TimedGrounding.Touch p).2 = loc) = [tc'] := by
          rw [show loc = Semantics.MemoryMsg.locOf (tc' : TimedGrounding.Touch p).2 from
            tc'Loc.symm]
          exact filterSingleton haltTouches' haltLocs'Nodup tc' tc'Mem
        rw [touchPairsAt_singleton, haltFilter] at balanceLoc
        simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.map_singleton]
          at balanceLoc
        have frontierEq : finalFrontier loc = some (tc' : TimedGrounding.Touch p).2 := by
          rw [← tc'Loc]
          exact haltForced tc' tc'Mem
        rw [frontierEq] at balanceLoc
        rw [show finM' loc = some (tc' : TimedGrounding.Touch p).1.1 from by
          rw [finM'Def]; simp [hfind]]
        simp only [TimedGrounding.optMS_some] at balanceLoc ⊢
        -- cancel the read-back record from both sides
        have := balanceLoc
        rw [show (TimedGrounding.optMS (memoryInitFrontier witness loc) +
              ((touchPairsAt ts' loc).map Prod.snd +
                {((tc' : TimedGrounding.Touch p).1.1, (tc' : TimedGrounding.Touch p).2).2})) =
            (TimedGrounding.optMS (memoryInitFrontier witness loc) +
              (touchPairsAt ts' loc).map Prod.snd) +
              {(tc' : TimedGrounding.Touch p).2} from by abel,
          show ({(tc' : TimedGrounding.Touch p).2} +
              ((touchPairsAt ts' loc).map Prod.fst +
                {((tc' : TimedGrounding.Touch p).1.1, (tc' : TimedGrounding.Touch p).2).1})) =
            ({(tc' : TimedGrounding.Touch p).1.1} +
              (touchPairsAt ts' loc).map Prod.fst) +
              {(tc' : TimedGrounding.Touch p).2} from by abel] at this
        exact add_right_cancel this
  have walked := TimedGrounding.walk statement.program initial (Commit.initClkNat witness.data)
    fin finM'
    (pairs.map walkRow).length (pairs.map walkRow)
    (initialBoundaryStateMessage statement.publicValues) (memoryInitFrontier witness)
    rfl stepFacts frameFacts rowOK boundary.localStateTruth
    liveAtHead stateBalance memoryBalance
  refine ⟨?_, walked.2.1, fun loc m finEq => ?_, fun tc tcMem => ?_⟩
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
    have valueEq' : m'.value = m.value := congrArg Prod.snd valueEq
    have locEqm : Semantics.MemoryMsg.locOf m' = Semantics.MemoryMsg.locOf m :=
      congrArg Prod.fst valueEq
    cases hfind : haltTouches'.find? (fun tc₁ =>
        Semantics.MemoryMsg.locOf (tc₁ : TimedGrounding.Touch p).2 = loc) with
    | none =>
        obtain ⟨locEq', truth', current', timeFin'⟩ := walked.2.2 loc m'
          (by rw [finM'Def]; simp only [hfind]; exact frontierEq)
        exact ⟨locEqm.symm.trans locEq', valueEq' ▸ current',
          m', locEq', valueEq', timeLe, timeFin', truth'⟩
    | some tc' =>
        obtain ⟨tc'Mem, tc'Loc⟩ := finM'mem loc tc' hfind
        -- the finalize record's eliminated ancestor is the halt read-back itself
        have frontierForced : finalFrontier loc = some (tc' : TimedGrounding.Touch p).2 := by
          rw [← tc'Loc]
          exact haltForced tc' tc'Mem
        have m'Eq : m' = (tc' : TimedGrounding.Touch p).2 := by
          have := frontierEq.symm.trans frontierForced
          exact Option.some.inj this
        obtain ⟨locEq', truth', current', timeFin'⟩ := walked.2.2 loc
          (tc' : TimedGrounding.Touch p).1.1
          (by rw [finM'Def]; simp only [hfind])
        obtain ⟨tc, tcMem, -, hpushEq, -, hval, htime⟩ := haltRewriteFacts tc' tc'Mem
        -- the rewritten halt pull carries the read-back's word
        have pullValEq : ((tc' : TimedGrounding.Touch p).1.1).value =
            ((tc' : TimedGrounding.Touch p).2).value := by
          rw [hval, haltValEq tc tcMem, ← hpushEq]
        have mValEq : ((tc' : TimedGrounding.Touch p).1.1).value = m.value := by
          rw [pullValEq, ← m'Eq]
          exact valueEq'
        refine ⟨locEqm.symm.trans (m'Eq ▸ tc'Loc), mValEq ▸ current',
          (tc' : TimedGrounding.Touch p).1.1, locEq', mValEq, ?_, timeFin', truth'⟩
        · have hlt := haltPullLt tc' tc'Mem
          rw [m'Eq] at timeLe
          omega
  · -- the halt row's pulled operands: balance-derived timestamp facts plus walk-final currency
    refine ⟨(haltPullGood tc tcMem).1, (haltPullGood tc tcMem).2, ?_⟩
    obtain ⟨tc', tc'Mem, hrw⟩ := TimedGrounding.forall₂_exists_left haltRewritten.flip tc tcMem
    have hrw' := pullRewrite_of_touchRewrite hrw
    obtain ⟨-, hpushEq, hlocEq', hvalEq', -⟩ := hrw'
    set loc := Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1 with locDef
    have locPush : Semantics.MemoryMsg.locOf (tc' : TimedGrounding.Touch p).2 = loc := by
      rw [hpushEq, locDef, haltLocEq tc tcMem]
    cases hfind : haltTouches'.find? (fun tc₁ =>
        Semantics.MemoryMsg.locOf (tc₁ : TimedGrounding.Touch p).2 = loc) with
    | none =>
        exact absurd locPush (by simpa using List.find?_eq_none.mp hfind tc' tc'Mem)
    | some tc₀' =>
        obtain ⟨tc₀'Mem, tc₀'Loc⟩ := finM'mem loc tc₀' hfind
        -- the found entry shares the original halt touch, hence its word
        obtain ⟨tc₀, tc₀Mem, -, hpush₀, -, hval₀, -⟩ := haltRewriteFacts tc₀' tc₀'Mem
        have origLocEq : Semantics.MemoryMsg.locOf (tc₀ : TimedGrounding.Touch p).2 =
            Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2 := by
          rw [← hpush₀, tc₀'Loc, locDef, haltLocEq tc tcMem]
        have origEq : tc₀ = tc :=
          List.inj_on_of_nodup_map haltLocsNodup tc₀Mem tcMem origLocEq
        have valEq : ((tc₀' : TimedGrounding.Touch p).1.1).value =
            ((tc : TimedGrounding.Touch p).1.1).value := by
          rw [hval₀, origEq]
        obtain ⟨-, truth', current', -⟩ := walked.2.2 loc (tc₀' : TimedGrounding.Touch p).1.1
          (by rw [finM'Def]; simp only [hfind])
        have isU64' : Word.isU64 ((tc : TimedGrounding.Touch p).1.1).value := by
          have := truth'.1
          rwa [show Channels.MemoryMsg.isU64 ((tc₀' : TimedGrounding.Touch p).1.1) =
            Word.isU64 (((tc₀' : TimedGrounding.Touch p).1.1).value) from rfl, valEq] at this
        exact ⟨isU64', valEq ▸ current'⟩

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
    (haltFree : realHaltRows witness = [])
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
        Semantics.MemoryMsg.locOf m = loc ∧
        Semantics.LocalValueAt initial (Commit.initClkNat witness.data) loc
          (Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues)) m.value ∧
        ∃ m', Semantics.MemoryMsg.locOf m' = loc ∧
          m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
          Semantics.MemoryMsg.timeNat m' ≤
            Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues) ∧
          Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m') := by
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
  have result := supportedCore_orderedRows_dynamic_of_obligations statement witness initial
    (finalBoundaryStateMessage statement.publicValues) initTimeLt finalTimeLt constraints
    balanced boundary
    (supportedCore_groundingObligations_of_constraints witness constraints)
    orderedRows exhaustive stateWalk []
    (by rw [halt_producedMessages_nil_of_haltFree witness constraints haltFree]; rfl)
    (by rw [halt_consumedMessages_nil_of_haltFree witness constraints haltFree]; rfl)
    (fun tc h => absurd h List.not_mem_nil)
    (fun tc h => absurd h List.not_mem_nil)
    (by simp)
    (fun tc h => absurd h List.not_mem_nil)
    (fun tc h => absurd h List.not_mem_nil)
    (fun tc h => absurd h List.not_mem_nil)
  exact ⟨result.1, result.2.1, result.2.2.1⟩

/-! ## Halt-row arithmetic, over an opaque row

The halted assembly below carries a very large local context, so every numeral/clock computation
about the halt row is proved here against an **opaque** `HaltChip.Inputs` value
(`docs/agents/proof-patterns.md` — extract over opaque arguments). -/

/-- A halt row's register read-back sits `k` ticks after its pre-syscall State pull. -/
private theorem haltPush_timeNat (r : HaltChip.Inputs (ZMod p))
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (block : Extracted.RegisterAccessCols (ZMod p)) (idx : ZMod p) (k : ℕ) (hk : k ≤ 264) :
    Semantics.MemoryMsg.timeNat (HaltChip.memPushedMessage r block idx ((k : ℕ) : ZMod p)) =
      Semantics.StateMsg.timeNat (HaltChip.statePulledMessage r) + k := by
  have hval := (TimeExtraction.clkVal_small_add_of_cpuState_bounds
    r.state.clk_0_16 r.state.clk_16_24 k hk clk0B clk1B).2
  simp only [Semantics.MemoryMsg.timeNat, Semantics.StateMsg.timeNat,
    HaltChip.memPushedMessage, HaltChip.statePulledMessage, Semantics.clkNat, hval]
  omega

/-- A halt row's register read-back carries a well-formed 24-bit access timestamp. -/
private theorem haltPush_clkFacts (r : HaltChip.Inputs (ZMod p))
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8) (highB : r.state.clk_high.val < 2 ^ 24)
    (block : Extracted.RegisterAccessCols (ZMod p)) (idx : ZMod p) (k : ℕ) (hk : k ≤ 6) :
    Channels.MemoryMsg.ClkBound (HaltChip.memPushedMessage r block idx ((k : ℕ) : ZMod p)) ∧
      (HaltChip.memPushedMessage r block idx ((k : ℕ) : ZMod p)).clk_high.val < 2 ^ 24 := by
  have hval := TimeExtraction.clkVal_small_add_of_cpuState_bounds
    r.state.clk_0_16 r.state.clk_16_24 k (by omega) clk0B clk1B
  refine ⟨?_, highB⟩
  show ((r.state.clk_0_16 + r.state.clk_16_24 * 65536) + ((k : ℕ) : ZMod p)).val < 2 ^ 24
  rw [hval.2]
  omega

/-- A halt row's pulled prior record is strictly earlier than its read-back: the composed
`RegisterAccessCols` timestamp discipline plus the bus `ClkBound` on the prior. -/
private theorem haltPull_lt_push (r : HaltChip.Inputs (ZMod p))
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (block : Extracted.RegisterAccessCols (ZMod p)) (idx : ZMod p) (k : ℕ) (hk : k ≤ 6)
    (diffB : block.access_timestamp.diff_low_limb.val < 2 ^ 16)
    (scaledB : ((r.state.clk_0_16 + r.state.clk_16_24 * 65536 + ((k : ℕ) : ZMod p) -
      block.access_timestamp.prev_low - 1 -
      block.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
    (prevClkB : Channels.MemoryMsg.ClkBound (HaltChip.memPulledMessage r block idx)) :
    Semantics.MemoryMsg.timeNat (HaltChip.memPulledMessage r block idx) <
      Semantics.MemoryMsg.timeNat (HaltChip.memPushedMessage r block idx ((k : ℕ) : ZMod p)) := by
  have prevB : block.access_timestamp.prev_low.val < 2 ^ 24 := prevClkB
  have prevLt := TimeExtraction.prevLow_val_lt_of_accessTimestamp
    (r.state.clk_0_16 + r.state.clk_16_24 * 65536 + ((k : ℕ) : ZMod p))
    block.access_timestamp.prev_low block.access_timestamp.diff_low_limb prevB diffB scaledB
  have hval := (TimeExtraction.clkVal_small_add_of_cpuState_bounds
    r.state.clk_0_16 r.state.clk_16_24 k (by omega) clk0B clk1B).2
  simp only [Semantics.MemoryMsg.timeNat, HaltChip.memPulledMessage,
    HaltChip.memPushedMessage, Semantics.clkNat]
  rw [hval] at prevLt
  omega

/-- The three register touches (`x5`/`x10`/`x11`) of a halt row, as the timed engine's carrier. -/
private def haltTouchesOf (r : HaltChip.Inputs (ZMod p)) : List (TimedGrounding.Touch p) :=
  [((HaltChip.memPulledMessage r r.x5_memory 5, 0),
     HaltChip.memPushedMessage r r.x5_memory 5 4),
   ((HaltChip.memPulledMessage r r.x10_memory 10, 0),
     HaltChip.memPushedMessage r r.x10_memory 10 3),
   ((HaltChip.memPulledMessage r r.x11_memory 11, 0),
     HaltChip.memPushedMessage r r.x11_memory 11 2)]

omit [Fact (2 ^ 25 < p)] in
/-- The touch carrier's pushed records, in order. -/
private theorem haltTouchesOf_pushes (r : HaltChip.Inputs (ZMod p)) :
    (haltTouchesOf r).map (fun tc => (tc : TimedGrounding.Touch p).2) =
      [HaltChip.memPushedMessage r r.x5_memory 5 4,
       HaltChip.memPushedMessage r r.x10_memory 10 3,
       HaltChip.memPushedMessage r r.x11_memory 11 2] := rfl

omit [Fact (2 ^ 25 < p)] in
/-- The touch carrier's pulled prior records, in order. -/
private theorem haltTouchesOf_pulls (r : HaltChip.Inputs (ZMod p)) :
    (haltTouchesOf r).map (fun tc => (tc : TimedGrounding.Touch p).1.1) =
      [HaltChip.memPulledMessage r r.x5_memory 5,
       HaltChip.memPulledMessage r r.x10_memory 10,
       HaltChip.memPulledMessage r r.x11_memory 11] := rfl

/-- **Every per-touch fact the timed engine consumes**, for the three register reads of an opaque
halt row: matching pull/push locations and words, three distinct register locations, the
read-backs' timestamp hygiene, their strict lateness against the pre-syscall State pull, and the
`prev_clk < access_clk` slot discipline. -/
private theorem haltTouchesOf_facts (r : HaltChip.Inputs (ZMod p))
    (clk0B : ((r.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (clk1B : r.state.clk_16_24.val < 2 ^ 8)
    (highB : (HaltChip.statePulledMessage r).clk_high.val < 2 ^ 24)
    (ts5 : r.x5_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
      ((r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 4 -
        r.x5_memory.access_timestamp.prev_low - 1 -
        r.x5_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
    (ts10 : r.x10_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
      ((r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 3 -
        r.x10_memory.access_timestamp.prev_low - 1 -
        r.x10_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
    (ts11 : r.x11_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
      ((r.state.clk_0_16 + r.state.clk_16_24 * 65536 + 2 -
        r.x11_memory.access_timestamp.prev_low - 1 -
        r.x11_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) :
    (∀ tc ∈ haltTouchesOf r,
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).1.1 =
        Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2) ∧
    (∀ tc ∈ haltTouchesOf r,
      ((tc : TimedGrounding.Touch p).1.1).value = ((tc : TimedGrounding.Touch p).2).value) ∧
    (((haltTouchesOf r).map (fun tc =>
      Semantics.MemoryMsg.locOf (tc : TimedGrounding.Touch p).2)).Nodup) ∧
    (∀ tc ∈ haltTouchesOf r,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).2 ∧
        ((tc : TimedGrounding.Touch p).2).clk_high.val < 2 ^ 24) ∧
    (∀ tc ∈ haltTouchesOf r,
      Semantics.StateMsg.timeNat (HaltChip.statePulledMessage r) <
        Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).2) ∧
    (∀ tc ∈ haltTouchesOf r,
      Channels.MemoryMsg.ClkBound (tc : TimedGrounding.Touch p).1.1 →
        ((tc : TimedGrounding.Touch p).1.1).clk_high.val < 2 ^ 24 →
          Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).1.1 <
            Semantics.MemoryMsg.timeNat (tc : TimedGrounding.Touch p).2) := by
  have push5 := locOf_reg5 (HaltChip.memPushedMessage r r.x5_memory 5 4) rfl rfl rfl
  have push10 := locOf_reg10 (HaltChip.memPushedMessage r r.x10_memory 10 3) rfl rfl rfl
  have push11 := locOf_reg11 (HaltChip.memPushedMessage r r.x11_memory 11 2) rfl rfl rfl
  have pull5 := locOf_reg5 (HaltChip.memPulledMessage r r.x5_memory 5) rfl rfl rfl
  have pull10 := locOf_reg10 (HaltChip.memPulledMessage r r.x10_memory 10) rfl rfl rfl
  have pull11 := locOf_reg11 (HaltChip.memPulledMessage r r.x11_memory 11) rfl rfl rfl
  have pushFacts := haltPush_clkFacts r clk0B clk1B
    (show r.state.clk_high.val < 2 ^ 24 from highB)
  have pushTime := haltPush_timeNat r clk0B clk1B
  have slot := haltPull_lt_push r clk0B clk1B
  have cast4 : ((4 : ℕ) : ZMod p) = (4 : ZMod p) := by norm_num
  have cast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by norm_num
  have cast2 : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tc tcMem
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · show Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x5_memory 5) =
        Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x5_memory 5 4)
      rw [pull5, push5]
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · show Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x10_memory 10) =
        Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x10_memory 10 3)
      rw [pull10, push10]
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · show Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x11_memory 11) =
        Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x11_memory 11 2)
      rw [pull11, push11]
    · exact absurd tcMem List.not_mem_nil
  · intro tc tcMem
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · rfl
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · rfl
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · rfl
    · exact absurd tcMem List.not_mem_nil
  · show ([Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x5_memory 5 4),
      Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x10_memory 10 3),
      Semantics.MemoryMsg.locOf (HaltChip.memPushedMessage r r.x11_memory 11 2)] :
        List Semantics.MemLoc).Nodup
    rw [push5, push10, push11]
    decide
  · intro tc tcMem
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact cast4 ▸ pushFacts r.x5_memory 5 4 (by omega)
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact cast3 ▸ pushFacts r.x10_memory 10 3 (by omega)
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact cast2 ▸ pushFacts r.x11_memory 11 2 (by omega)
    · exact absurd tcMem List.not_mem_nil
  · intro tc tcMem
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · have h := pushTime r.x5_memory 5 4 (by omega)
      rw [cast4] at h
      show Semantics.StateMsg.timeNat (HaltChip.statePulledMessage r) <
        Semantics.MemoryMsg.timeNat (HaltChip.memPushedMessage r r.x5_memory 5 4)
      omega
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · have h := pushTime r.x10_memory 10 3 (by omega)
      rw [cast3] at h
      show Semantics.StateMsg.timeNat (HaltChip.statePulledMessage r) <
        Semantics.MemoryMsg.timeNat (HaltChip.memPushedMessage r r.x10_memory 10 3)
      omega
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · have h := pushTime r.x11_memory 11 2 (by omega)
      rw [cast2] at h
      show Semantics.StateMsg.timeNat (HaltChip.statePulledMessage r) <
        Semantics.MemoryMsg.timeNat (HaltChip.memPushedMessage r r.x11_memory 11 2)
      omega
    · exact absurd tcMem List.not_mem_nil
  · intro tc tcMem
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact fun hClk _ => cast4 ▸ slot r.x5_memory 5 4 (by omega) ts5.1 (cast4 ▸ ts5.2) hClk
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact fun hClk _ => cast3 ▸ slot r.x10_memory 10 3 (by omega) ts10.1 (cast3 ▸ ts10.2) hClk
    rcases List.mem_cons.mp tcMem with rfl | tcMem
    · exact fun hClk _ => cast2 ▸ slot r.x11_memory 11 2 (by omega) ts11.1 (cast2 ▸ ts11.2) hClk
    · exact absurd tcMem List.not_mem_nil

omit [Fact (2 ^ 25 < p)] in
/-- Transport one grounded pulled-operand currency fact to the register-typed statement the
halted certificate publishes. -/
private theorem haltPull_valueAt (r : HaltChip.Inputs (ZMod p))
    (blk : Extracted.RegisterAccessCols (ZMod p)) (idx : ZMod p) (reg : BitVec 5)
    (hloc : Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r blk idx) =
      Semantics.MemLoc.reg reg)
    (initial : SailState) (c0 t : ℕ)
    (h : Semantics.LocalValueAt initial c0
      (Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r blk idx)) t
      (HaltChip.memPulledMessage r blk idx).value) :
    Semantics.LocalValueAt initial c0 (Semantics.MemLoc.reg reg) t blk.prev_value := by
  rwa [hloc] at h

/-- The three pulled prior records' register locations, over an opaque row. -/
private theorem haltPull_locs (r : HaltChip.Inputs (ZMod p)) :
    Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x5_memory 5) =
        Semantics.MemLoc.reg (5 : BitVec 5) ∧
      Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x10_memory 10) =
        Semantics.MemLoc.reg (10 : BitVec 5) ∧
      Semantics.MemoryMsg.locOf (HaltChip.memPulledMessage r r.x11_memory 11) =
        Semantics.MemLoc.reg (11 : BitVec 5) :=
  ⟨locOf_reg5 _ rfl rfl rfl, locOf_reg10 _ rfl rfl rfl, locOf_reg11 _ rfl rfl rfl⟩

omit [Fact (2 ^ 25 < p)] in
/-- The halt row's Program-pull pc key and its State-pull pc are the same three limbs. -/
private theorem halt_programPcBits (r : HaltChip.Inputs (ZMod p)) :
    Target.pcBitsOfRow (Semantics.rowOfMsg (HaltChip.programMessage r)) =
      Semantics.StateMsg.pcBits (HaltChip.statePulledMessage r) := rfl

/-- The canonical instruction walk ending at a halt row's pre-syscall pull projects to the pc-only
walk local execution consumes.  Extracted over opaque arguments: the halted assembly's own context
is far too large for the endpoint rewriting to run in place. -/
private theorem pcWalk_to_haltPull (data : ProverData (ZMod p))
    (pv : SP1PublicIO (ZMod p)) (r : HaltChip.Inputs (ZMod p))
    (rows : List (DecodedInstructionRow p))
    (walk : Walk.IsWalk (fun decoded =>
        (canonState (decodedStateEdge data decoded).1,
         canonState (decodedStateEdge data decoded).2))
      (initialBoundaryStateMessage pv) (canonState (HaltChip.statePulledMessage r)) rows)
    (good : ∀ decoded ∈ rows,
      ((decodedStateEdge data decoded).1.pc1.val < 2 ^ 16 ∧
        (decodedStateEdge data decoded).1.pc2.val < 2 ^ 16) ∧
      ((decodedStateEdge data decoded).2.pc1.val < 2 ^ 16 ∧
        (decodedStateEdge data decoded).2.pc2.val < 2 ^ 16))
    (hpc1 : (HaltChip.statePulledMessage r).pc1.val < 2 ^ 16)
    (hpc2 : (HaltChip.statePulledMessage r).pc2.val < 2 ^ 16) :
    PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow data)
      (supportedPcBits pv.init_pc0 pv.init_pc1 pv.init_pc2)
      (Semantics.StateMsg.pcBits (HaltChip.statePulledMessage r)) rows := by
  have h := pcWalk_of_canonStateWalk data walk good
  rw [pcBits_canonState hpc1 hpc2] at h
  simpa [initialBoundaryStateMessage, Semantics.StateMsg.pcBits, supportedPcBits] using h

/-! ## The halted-shard grounding certificate -/

/-- The halted twin of `SupportedCoreGrounding`: the shard's active instruction rows form an
eight-tick grounded prefix, and its **one** active Halt row (forced by the Exit hand-off balance)
terminates it — the pre-syscall state is reached by a genuine Sail chain at the committed clock,
the committed program holds the literal `ECALL` word at that pc, the three pulled operand words are
the execution's current register contents, the committed exit code is the row's reduced `x10`
word, and the public final boundary sits one 264-tick syscall window later at `haltPc = 1`. -/
structure SupportedCoreHaltGrounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (orderedRows : List (DecodedInstructionRow p))
    (halt : Array (ZMod p)) : Prop where
  exhaustive : orderedRows.Perm (realDecodedInstructionRows witness.data witness.tables)
  haltReal : realHaltRows witness = [halt]
  spec : HaltChip.Spec (haltRow (haltTable witness) halt)
  real : (haltRow (haltTable witness) halt).is_real = 1
  walk : PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
    (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
      statement.publicValues.init_pc2)
    (Semantics.StateMsg.pcBits (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
    orderedRows
  grounded : RowsGrounded (fun decoded : DecodedInstructionRow p =>
      decoded.toChipRow witness.data) witness.data statement.program initial orderedRows
  pullClock : Semantics.StateMsg.timeNat
      (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) =
    Commit.initClkNat witness.data + 8 * orderedRows.length
  finalClock : Semantics.clkNat statement.publicValues.final_clk_high
      statement.publicValues.final_clk_low =
    Semantics.StateMsg.timeNat (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))
      + 264
  finalPc : supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
      statement.publicValues.final_pc2 = Machine.haltPc
  pullTruth : Semantics.LocalStateTruth statement.program initial
    (Commit.initClkNat witness.data)
    (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))
  ecallFetch : statement.program.fetchWord
      (Semantics.StateMsg.pcBits (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
      = some Target.ECALL_ENC
  exitBinding : HaltChip.exitMessage (haltRow (haltTable witness) halt) =
    (⟨statement.publicValues.exit_code⟩ : Channels.ExitMsg (ZMod p))
  x5U64 : Word.isU64 (haltRow (haltTable witness) halt).x5_memory.prev_value
  x10U64 : Word.isU64 (haltRow (haltTable witness) halt).x10_memory.prev_value
  x11U64 : Word.isU64 (haltRow (haltTable witness) halt).x11_memory.prev_value
  x5Value : Semantics.LocalValueAt initial (Commit.initClkNat witness.data)
    (Semantics.MemLoc.reg (5 : BitVec 5))
    (Semantics.StateMsg.timeNat
      (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
    (haltRow (haltTable witness) halt).x5_memory.prev_value
  x10Value : Semantics.LocalValueAt initial (Commit.initClkNat witness.data)
    (Semantics.MemLoc.reg (10 : BitVec 5))
    (Semantics.StateMsg.timeNat
      (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
    (haltRow (haltTable witness) halt).x10_memory.prev_value
  x11Value : Semantics.LocalValueAt initial (Commit.initClkNat witness.data)
    (Semantics.MemLoc.reg (11 : BitVec 5))
    (Semantics.StateMsg.timeNat
      (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
    (haltRow (haltTable witness) halt).x11_memory.prev_value
  memoryFinalizeTruth : ∀ loc m, memoryFinalizeFrontier witness loc = some m →
    Semantics.MemoryMsg.locOf m = loc ∧
    Semantics.LocalValueAt initial (Commit.initClkNat witness.data) loc
      (Semantics.StateMsg.timeNat
        (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) m.value ∧
    ∃ m', Semantics.MemoryMsg.locOf m' = loc ∧
      m'.value = m.value ∧ Semantics.MemoryMsg.timeNat m' ≤ Semantics.MemoryMsg.timeNat m ∧
      Semantics.MemoryMsg.timeNat m' ≤
        Semantics.StateMsg.timeNat
          (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) ∧
      Semantics.LocalMemTruth initial (Commit.initClkNat witness.data) m'

/-- Every member of an all-left sum-typed list is an injection image, so the list is a map. -/
private theorem listAllInl {α β : Type*} :
    ∀ (l : List (α ⊕ β)), (∀ t ∈ l, ∃ a : α, t = Sum.inl a) →
      ∃ rows : List α, l = rows.map Sum.inl
  | [], _ => ⟨[], rfl⟩
  | t :: l, h => by
      obtain ⟨a, rfl⟩ := h t List.mem_cons_self
      obtain ⟨rows, rfl⟩ := listAllInl l (fun t ht => h t (List.mem_cons_of_mem _ ht))
      exact ⟨a :: rows, rfl⟩

/-- The sole semantic grounding seam for the supported native slice, **case-split at the Exit
hand-off**: a satisfying balanced witness is either an ordinary shard — every active row an
eight-tick instruction, the committed exit code zero — or a halting shard — an ordinary prefix
terminated by the one active Halt row.

Program-provider commitment is no longer part of this seam:
`supportedCore_orderedRows_programDecoded` supplies the exact static decode field for every
exhaustive ordering, and `supportedCore_orderedRows_static` packages the whole static layer.  The
dichotomy itself is the Exit-channel balance (`Soundness/ExitAccounting.lean`): the state-boundary
verifier's ungated `⟨exit_code⟩` pull forces exactly one Halt-table hand-off row. -/
theorem supported_core_witness_grounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (publicInputEq : witness.publicInput = statement.publicValues)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial) :
    (realHaltRows witness = [] ∧ statement.publicValues.exit_code = 0 ∧
      ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows) ∨
    (∃ orderedRows halt,
      SupportedCoreHaltGrounding statement witness initial orderedRows halt) := by
  classical
  obtain ⟨trailRows, trailWalk, trailMultiset⟩ :=
    witness_realDecodedState_canonExhaustiveTrail witness constraints balanced
  rw [publicInputEq] at trailWalk
  cases hhalt : realHaltRows witness with
  | nil =>
      left
      refine ⟨rfl, ?_, ?_⟩
      · have := witness_exit_code_zero_of_haltFree witness constraints balanced hhalt
        rwa [publicInputEq] at this
      rw [hhalt] at trailMultiset
      simp only [List.map_nil, Multiset.coe_nil, add_zero] at trailMultiset
      have allInl : ∀ t ∈ trailRows, ∃ d : DecodedInstructionRow p,
          t = (Sum.inl d : TrailRow p) := by
        intro t tMem
        have tMem' : t ∈ (realDecodedInstructionRows witness.data witness.tables).map
            (Sum.inl : DecodedInstructionRow p → TrailRow p) := by
          rw [← Multiset.mem_coe, ← trailMultiset]
          exact Multiset.mem_coe.mpr tMem
        obtain ⟨d, -, rfl⟩ := List.mem_map.mp tMem'
        exact ⟨d, rfl⟩
      obtain ⟨orderedRows, rfl⟩ := listAllInl trailRows allInl
      have exhaustive : orderedRows.Perm
          (realDecodedInstructionRows witness.data witness.tables) := by
        apply Multiset.coe_eq_coe.mp
        apply Multiset.map_injective
          (Sum.inl_injective : Function.Injective (Sum.inl :
            DecodedInstructionRow p → TrailRow p))
        rw [Multiset.map_coe, Multiset.map_coe]
        exact trailMultiset
      have stateWalk : Walk.IsWalk (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2))
          (initialBoundaryStateMessage statement.publicValues)
          (finalBoundaryStateMessage statement.publicValues) orderedRows :=
        (Walk.isWalk_map (trailCanonEdge witness)
          (Sum.inl : DecodedInstructionRow p → TrailRow p) orderedRows _ _).mp trailWalk
      have goodness := (witness_stateEdges_goodness witness constraints balanced).1
      have dyn := supportedCore_orderedRows_dynamic statement witness initial publicInputEq
        constraints balanced boundary hhalt orderedRows exhaustive stateWalk
      refine ⟨orderedRows, exhaustive, ?_, ?_, ?_, dyn.2.1, dyn.2.2⟩
      · simpa [initialBoundaryStateMessage, finalBoundaryStateMessage,
          Semantics.StateMsg.pcBits, supportedPcBits] using
          pcWalk_of_canonStateWalk witness.data stateWalk (fun decoded decodedMem =>
            ⟨(goodness decoded (exhaustive.mem_iff.mp decodedMem)).2.1,
              (goodness decoded (exhaustive.mem_iff.mp decodedMem)).2.2⟩)
      · exact {
          static := supportedCore_orderedRows_static statement witness constraints balanced
            boundary orderedRows exhaustive
          dynamic := dyn.1 }
      · have clockCount := clockCount_of_stateWalk _ stateWalk
          (fun decoded decodedMem => by
            rw [timeNat_canonState (goodness decoded (exhaustive.mem_iff.mp decodedMem)).1.1,
              timeNat_canonState (goodness decoded (exhaustive.mem_iff.mp decodedMem)).1.2]
            exact witness_realDecodedInstructionRows_timeStep witness constraints balanced
              decoded (exhaustive.mem_iff.mp decodedMem))
        change
          Semantics.clkNat statement.publicValues.init_clk_high
              statement.publicValues.init_clk_low + 8 * orderedRows.length =
            Semantics.clkNat statement.publicValues.final_clk_high
              statement.publicValues.final_clk_low
          at clockCount
        have initClock := boundary.initialClock
        omega
  | cons halt rest =>
      right
      have haltMem : halt ∈ realHaltRows witness := by
        rw [hhalt]
        exact List.mem_cons_self
      obtain ⟨haltRealEq, exitBind⟩ :=
        witness_realHaltRows_eq_of_mem witness constraints balanced haltMem
      obtain ⟨-, real⟩ := mem_realHaltRows witness haltMem
      have goodness := witness_stateEdges_goodness witness constraints balanced
      have instrGood := goodness.1
      have haltGood := goodness.2.2 halt haltMem
      -- locate the halt edge in the trail
      rw [haltRealEq] at trailMultiset
      have haltInTrail : (Sum.inr halt : TrailRow p) ∈ trailRows := by
        rw [← Multiset.mem_coe, trailMultiset]
        refine Multiset.mem_add.mpr (Or.inr ?_)
        simp
      obtain ⟨pre, post, trailEq⟩ := List.append_of_mem haltInTrail
      subst trailEq
      -- the instruction residue: everything except the halt edge is an injection image
      have sideEq : ((↑pre : Multiset (TrailRow p)) + ↑post) =
          ↑((realDecodedInstructionRows witness.data witness.tables).map
            (Sum.inl : DecodedInstructionRow p → TrailRow p)) := by
        have expand : ((↑(pre ++ (Sum.inr halt : TrailRow p) :: post)) :
            Multiset (TrailRow p)) =
            (Sum.inr halt : TrailRow p) ::ₘ ((↑pre : Multiset (TrailRow p)) + ↑post) := by
          rw [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.add_cons]
        have rhs : ((↑((realDecodedInstructionRows witness.data witness.tables).map
              (Sum.inl : DecodedInstructionRow p → TrailRow p)) +
            ↑([halt].map (Sum.inr : Array (ZMod p) → TrailRow p))) :
              Multiset (TrailRow p)) =
            (Sum.inr halt : TrailRow p) ::ₘ
              ↑((realDecodedInstructionRows witness.data witness.tables).map
                (Sum.inl : DecodedInstructionRow p → TrailRow p)) := by
          simp only [List.map_cons, List.map_nil]
          rw [← Multiset.cons_coe, Multiset.add_cons]
          simp
        have := trailMultiset
        rw [expand, rhs] at this
        exact Multiset.cons_inj_right _ |>.mp this
      have sideInl : ∀ t ∈ pre ++ post, ∃ d : DecodedInstructionRow p,
          t = (Sum.inl d : TrailRow p) := by
        intro t tMem
        have tMem' : t ∈ (realDecodedInstructionRows witness.data witness.tables).map
            (Sum.inl : DecodedInstructionRow p → TrailRow p) := by
          have tSide : t ∈ ((↑pre : Multiset (TrailRow p)) + ↑post) := by
            rcases List.mem_append.mp tMem with h | h
            · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr h))
            · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_coe.mpr h))
          rw [sideEq] at tSide
          exact Multiset.mem_coe.mp tSide
        obtain ⟨d, -, rfl⟩ := List.mem_map.mp tMem'
        exact ⟨d, rfl⟩
      obtain ⟨orderedRows, preEq⟩ := listAllInl pre
        (fun t ht => sideInl t (List.mem_append.mpr (Or.inl ht)))
      obtain ⟨postRows, postEq⟩ := listAllInl post
        (fun t ht => sideInl t (List.mem_append.mpr (Or.inr ht)))
      subst preEq
      subst postEq
      -- split the trail walk at the halt edge
      obtain ⟨mid, walkPre, midEq, walkPost⟩ :=
        (Walk.isWalk_append (trailCanonEdge witness) _ _ _ _).mp trailWalk
      -- committed decode of every real instruction row (walk-independent)
      have decodeAll := supportedCore_orderedRows_programDecoded statement witness constraints
        balanced boundary (realDecodedInstructionRows witness.data witness.tables)
        (List.Perm.refl _)
      -- membership of the side rows in the real instruction rows
      have sideRealMem : ∀ d : DecodedInstructionRow p,
          (Sum.inl d : TrailRow p) ∈ orderedRows.map (Sum.inl :
              DecodedInstructionRow p → TrailRow p) ++
            postRows.map (Sum.inl : DecodedInstructionRow p → TrailRow p) →
          d ∈ realDecodedInstructionRows witness.data witness.tables := by
        intro d dMem
        have dMem' : (Sum.inl d : TrailRow p) ∈
            (realDecodedInstructionRows witness.data witness.tables).map
              (Sum.inl : DecodedInstructionRow p → TrailRow p) := by
          have dSide : (Sum.inl d : TrailRow p) ∈
              ((↑(orderedRows.map (Sum.inl : DecodedInstructionRow p → TrailRow p)) :
                  Multiset (TrailRow p)) +
                (↑(postRows.map (Sum.inl : DecodedInstructionRow p → TrailRow p)) :
                  Multiset (TrailRow p))) := by
            rcases List.mem_append.mp dMem with h | h
            · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr h))
            · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_coe.mpr h))
          rw [sideEq] at dSide
          exact Multiset.mem_coe.mp dSide
        obtain ⟨d', d'Mem, d'Eq⟩ := List.mem_map.mp dMem'
        rwa [show d' = d from Sum.inl_injective d'Eq] at d'Mem
      -- the halt push's canonical pc is the terminal `haltPc = 1`
      have pushPcVal : StateMsg.pcVal
          (HaltChip.statePushedMessage (haltRow (haltTable witness) halt)) = 1 := by
        have h1 : ((1 : ZMod p)).val = 1 := ZMod.val_one p
        have h0 : ((0 : ZMod p)).val = 0 := ZMod.val_zero
        simp only [StateMsg.pcVal, HaltChip.statePushedMessage, h1, h0]
        norm_num
      have haltPushPc : Semantics.StateMsg.pcBits
          (canonState (HaltChip.statePushedMessage (haltRow (haltTable witness) halt))) =
          Machine.haltPc := by
        rw [pcBits_canonState (by simp [HaltChip.statePushedMessage, ZMod.val_zero])
          (by simp [HaltChip.statePushedMessage, ZMod.val_zero])]
        simp only [Semantics.StateMsg.pcBits, Semantics.pcBits, HaltChip.statePushedMessage,
          ZMod.val_one, ZMod.val_zero, Machine.haltPc]
        norm_num
      -- no instruction row can follow the halt edge: it would fetch at `pc = 1`
      have postNil : postRows = [] := by
        cases hpost : postRows with
        | nil => rfl
        | cons d post' =>
            exfalso
            have dMem : d ∈ realDecodedInstructionRows witness.data witness.tables := by
              refine sideRealMem d (List.mem_append.mpr (Or.inr ?_))
              rw [hpost]
              exact List.mem_map_of_mem List.mem_cons_self
            rw [hpost] at walkPost
            obtain ⟨headEq, -⟩ := walkPost
            -- the head instruction's canonical pull is the halt push
            have pcEq := congrArg Semantics.StateMsg.pcBits headEq
            have dGood := instrGood d dMem
            rw [show (trailCanonEdge witness (Sum.inl d)).1 =
                canonState (decodedStateEdge witness.data d).1 from rfl] at pcEq
            rw [show (trailCanonEdge witness (Sum.inr halt)).2 =
                canonState (HaltChip.statePushedMessage (haltRow (haltTable witness) halt))
              from rfl, haltPushPc] at pcEq
            rw [pcBits_canonState dGood.2.1.1 dGood.2.1.2] at pcEq
            -- the row's committed fetch sits at that same pc
            obtain ⟨w, I, fetchEq, -, -⟩ := decodeAll d dMem
            have pcRowEq : Target.pcBitsOfRow
                (programAccess (d.toChipRow witness.data).view).toRow =
                Semantics.StateMsg.pcBits (decodedStateEdge witness.data d).1 := by
              rw [show (decodedStateEdge witness.data d).1 =
                statePullMessage (d.toChipRow witness.data) from rfl, statePullMessage_pcBits]
              rfl
            rw [pcRowEq, pcEq] at fetchEq
            have noFetch : statement.program.fetchWord Machine.haltPc = none :=
              statement.program.fetchWord_low_none (by
                simp only [Machine.haltPc]
                norm_num)
            rw [noFetch] at fetchEq
            exact absurd fetchEq (by simp)
      subst postNil
      -- the trail's terminal edge is the public final boundary
      have finEq : canonState
          (HaltChip.statePushedMessage (haltRow (haltTable witness) halt)) =
          finalBoundaryStateMessage statement.publicValues := by
        have : Walk.IsWalk (trailCanonEdge witness)
            (trailCanonEdge witness (Sum.inr halt)).2
            (finalBoundaryStateMessage statement.publicValues) [] := walkPost
        exact this
      -- the instruction prefix walks from the public initial boundary to the halt pull
      have stateWalk' : Walk.IsWalk (fun decoded =>
          (canonState (decodedStateEdge witness.data decoded).1,
           canonState (decodedStateEdge witness.data decoded).2))
          (initialBoundaryStateMessage statement.publicValues)
          (canonState (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
          orderedRows := by
        have midIsPull : mid = canonState
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) := by
          exact midEq.symm
        rw [midIsPull] at walkPre
        exact (Walk.isWalk_map (trailCanonEdge witness)
          (Sum.inl : DecodedInstructionRow p → TrailRow p) orderedRows _ _).mp walkPre
      have exhaustive : orderedRows.Perm
          (realDecodedInstructionRows witness.data witness.tables) := by
        apply Multiset.coe_eq_coe.mp
        apply Multiset.map_injective
          (Sum.inl_injective : Function.Injective (Sum.inl :
            DecodedInstructionRow p → TrailRow p))
        rw [Multiset.map_coe, Multiset.map_coe]
        simpa using sideEq
      -- byte-derived clock facts of the halt row
      obtain ⟨clk0B, clk1B⟩ :=
        witness_realHaltRows_clkBounds witness constraints balanced halt haltMem
      have clkFacts := TimeExtraction.clkVal_small_add_of_cpuState_bounds
        (haltRow (haltTable witness) halt).state.clk_0_16
        (haltRow (haltTable witness) halt).state.clk_16_24 0 (by omega) clk0B clk1B
      have clkLowLt : ((haltRow (haltTable witness) halt).state.clk_0_16 +
          (haltRow (haltTable witness) halt).state.clk_16_24 * 65536).val <
          2 ^ 24 - 6 := clkFacts.1
      -- the canonical pull time is the pull time
      have pullTimeCanon : Semantics.StateMsg.timeNat
          (canonState (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) =
          Semantics.StateMsg.timeNat
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) :=
        timeNat_canonState haltGood.1.1
      -- the walk's endpoint: the halt row's canonicalized pre-syscall pull
      set c := canonState (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))
        with cDef
      have limbBounds : SP1StateBoundary.LimbBounds statement.publicValues := by
        rw [← publicInputEq]
        exact witness_publicInput_limbBounds witness constraints balanced
      have initTimeLt : Semantics.StateMsg.timeNat
          (initialBoundaryStateMessage statement.publicValues) < 2 ^ 48 :=
        clkNat_lt_of_limbs (initialBoundaryStateMessage_bounds _ limbBounds).1
          (initialBoundaryStateMessage_bounds _ limbBounds).2.1
      have finalTimeLt : Semantics.StateMsg.timeNat c < 2 ^ 48 := by
        rw [cDef, pullTimeCanon]
        have hh := haltGood.1.1
        have hlow := clkLowLt
        simp only [Semantics.StateMsg.timeNat, HaltChip.statePulledMessage,
          Semantics.clkNat] at hh ⊢
        omega
      -- the three register touches of the halt row, with every per-touch engine fact
      obtain ⟨tsx5, tsx10, tsx11⟩ :=
        haltRow_accessTimestamp_bounds witness constraints balanced haltMem
      obtain ⟨touchLoc, touchVal, touchNodup, touchPushGood, touchPushLate, touchSlot⟩ :=
        haltTouchesOf_facts (haltRow (haltTable witness) halt) clk0B clk1B haltGood.1.1
          tsx5 tsx10 tsx11
      have finTime : Semantics.StateMsg.timeNat c =
          Semantics.StateMsg.timeNat
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) := by
        rw [cDef]
        exact pullTimeCanon
      -- feed the generalized ordered-row engine at the halt row's own pull as final boundary
      have result := supportedCore_orderedRows_dynamic_of_obligations statement witness initial
        c initTimeLt finalTimeLt constraints balanced boundary
        (supportedCore_groundingObligations_of_constraints witness constraints)
        orderedRows exhaustive stateWalk'
        (haltTouchesOf (haltRow (haltTable witness) halt))
        (by
          rw [halt_producedMessages_eq witness constraints, haltRealEq,
            haltTouchesOf_pushes]
          rfl)
        (by
          rw [halt_consumedMessages_eq witness constraints, haltRealEq,
            haltTouchesOf_pulls]
          rfl)
        touchLoc touchVal touchNodup touchPushGood
        (by
          intro tc tcMem
          rw [finTime]
          exact touchPushLate tc tcMem)
        touchSlot
      -- the halt-touch currency facts, per register
      have touch5 := result.2.2.2 _ List.mem_cons_self
      have touch10 := result.2.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have touch11 := result.2.2.2 _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      -- assemble the halt table's Memory guarantee from the balance-derived pull facts,
      -- and extract the full semantic `Spec`
      have tableEq := witness_haltTable_table_eq_of_mem witness constraints balanced haltMem
      have memGuar : (haltTable witness).ChannelGuarantees Channels.memoryChannel.toRaw := by
        intro row rowMem
        have rowIsHalt : row = halt := by
          rw [tableEq] at rowMem
          exact List.mem_singleton.mp rowMem
        rw [rowIsHalt, haltTable_component]
        refine channelGuarantees_of_consumedMessages _ Channels.memoryChannel _
          (by have := Fact.out (p := 2 ^ 25 < p); omega) ?_
        have rowConsumed : consumedMessages (typedInteractionValuesWith
            (⟨HaltChip.circuit⟩ : Component (ZMod p)).operations Channels.memoryChannel
            ((haltTable witness).environment halt)) =
            [HaltChip.memPulledMessage (haltRow (haltTable witness) halt) (haltRow (haltTable witness) halt).x5_memory 5,
             HaltChip.memPulledMessage (haltRow (haltTable witness) halt) (haltRow (haltTable witness) halt).x10_memory 10,
             HaltChip.memPulledMessage (haltRow (haltTable witness) halt) (haltRow (haltTable witness) halt).x11_memory 11] := by
          have tableConsumed := halt_consumedMessages_eq witness constraints
          rw [haltRealEq] at tableConsumed
          rw [typedTableInteractionsWith, tableEq] at tableConsumed
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at tableConsumed
          rw [show (haltTable witness).component = (⟨HaltChip.circuit⟩ : Component (ZMod p))
            from haltTable_component witness] at tableConsumed
          exact tableConsumed
        rw [rowConsumed]
        intro msg msgMem
        rcases List.mem_cons.mp msgMem with rfl | msgMem
        · exact ⟨touch5.2.2.1, touch5.1⟩
        rcases List.mem_cons.mp msgMem with rfl | msgMem
        · exact ⟨touch10.2.2.1, touch10.1⟩
        rcases List.mem_cons.mp msgMem with rfl | msgMem
        · exact ⟨touch11.2.2.1, touch11.1⟩
        · exact absurd msgMem List.not_mem_nil
      have haltSpec : HaltChip.Spec (haltRow (haltTable witness) halt) :=
        haltTable_spec witness constraints balanced memGuar halt
          (mem_realHaltRows witness haltMem).1
      obtain ⟨loc5', loc10', loc11'⟩ := haltPull_locs (haltRow (haltTable witness) halt)
      -- the committed ECALL site
      have ecallTruth := witness_haltRow_ecallTruth witness constraints balanced
        boundary.programProvider haltMem
      have ecallFetch : statement.program.fetchWord
          (Semantics.StateMsg.pcBits
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) =
          some Target.ECALL_ENC := by
        have := ecallTruth.1
        rw [boundary.programCommitted.2] at this
        rw [halt_programPcBits] at this
        exact this
      -- clock accounting: the instruction prefix places the pull, the syscall window the boundary
      have clockCount := clockCount_of_stateWalk _ stateWalk'
        (fun decoded decodedMem => by
          rw [timeNat_canonState (instrGood decoded (exhaustive.mem_iff.mp decodedMem)).1.1,
            timeNat_canonState (instrGood decoded (exhaustive.mem_iff.mp decodedMem)).1.2]
          exact witness_realDecodedInstructionRows_timeStep witness constraints balanced
            decoded (exhaustive.mem_iff.mp decodedMem))
      have pullClock : Semantics.StateMsg.timeNat
          (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) =
          Commit.initClkNat witness.data + 8 * orderedRows.length := by
        rw [← pullTimeCanon, ← clockCount]
        have := boundary.initialClock
        simp only [Semantics.StateMsg.timeNat, initialBoundaryStateMessage]
        omega
      have finalClock : Semantics.clkNat statement.publicValues.final_clk_high
          statement.publicValues.final_clk_low =
          Semantics.StateMsg.timeNat
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) + 264 := by
        have timeEq := congrArg Semantics.StateMsg.timeNat finEq
        rw [timeNat_canonState haltGood.1.2] at timeEq
        rw [witness_realHaltRows_timeStep witness constraints balanced halt haltMem] at timeEq
        exact timeEq.symm
      have finalPc : supportedPcBits statement.publicValues.final_pc0
          statement.publicValues.final_pc1 statement.publicValues.final_pc2 =
          Machine.haltPc := by
        have pcEq := congrArg Semantics.StateMsg.pcBits finEq
        rw [haltPushPc] at pcEq
        rw [show Semantics.StateMsg.pcBits
            (finalBoundaryStateMessage statement.publicValues) =
          supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
            statement.publicValues.final_pc2 from rfl] at pcEq
        exact pcEq.symm
      -- package the certificate
      refine ⟨orderedRows, halt, {
        exhaustive := exhaustive
        haltReal := haltRealEq
        spec := haltSpec
        real := real
        walk := ?_
        grounded := {
          static := supportedCore_orderedRows_static statement witness constraints balanced
            boundary orderedRows exhaustive
          dynamic := result.1 }
        pullClock := pullClock
        finalClock := finalClock
        finalPc := finalPc
        pullTruth := by
          obtain ⟨n, s, chain, timeEq, pcEq, rom, cfg⟩ := result.2.1
          refine ⟨n, s, chain, ?_, ?_, rom, cfg⟩
          · rw [← pullTimeCanon]
            exact timeEq
          · rw [show Semantics.pcBits
                (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)).pc0
                (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)).pc1
                (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)).pc2 =
              Semantics.StateMsg.pcBits
                (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)) from rfl,
              ← pcBits_canonState haltGood.2.1 haltGood.2.2]
            exact pcEq
        ecallFetch := ecallFetch
        exitBinding := by
          rw [← publicInputEq]
          exact exitBind
        x5U64 := touch5.2.2.1
        x10U64 := touch10.2.2.1
        x11U64 := touch11.2.2.1
        x5Value := by
          rw [← finTime]
          exact haltPull_valueAt _ _ _ _ loc5' _ _ _ touch5.2.2.2
        x10Value := by
          rw [← finTime]
          exact haltPull_valueAt _ _ _ _ loc10' _ _ _ touch10.2.2.2
        x11Value := by
          rw [← finTime]
          exact haltPull_valueAt _ _ _ _ loc11' _ _ _ touch11.2.2.2
        memoryFinalizeTruth := by
          intro loc m finEq
          obtain ⟨locEq, current, m', m'loc, m'val, m'le, m'fin, m'truth⟩ :=
            result.2.2.1 loc m finEq
          refine ⟨locEq, ?_, m', m'loc, m'val, m'le, ?_, m'truth⟩
          · rw [← finTime]
            exact current
          · rw [← finTime]
            exact m'fin }⟩
      exact pcWalk_to_haltPull witness.data statement.publicValues
        (haltRow (haltTable witness) halt) orderedRows stateWalk'
        (fun decoded decodedMem =>
          ⟨(instrGood decoded (exhaustive.mem_iff.mp decodedMem)).2.1,
            (instrGood decoded (exhaustive.mem_iff.mp decodedMem)).2.2⟩)
        haltGood.2.1 haltGood.2.2

end SP1Clean.Soundness
