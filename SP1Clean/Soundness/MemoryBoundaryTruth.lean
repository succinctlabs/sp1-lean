import SP1Clean.Model.Semantics.ImageContent
import SP1Clean.Soundness.MemoryFrontier

/-! # The populated native Memory boundary

The shard-level semantic relation carries a finite `Machine.CoreMemoryBoundary`; until this file
the native soundness path instantiated it with the empty boundary, discharging its two validity
fields vacuously while the timed-grounding walk proved (and discarded) the real per-location
content.  This file converts the walk's exported finalize truth into a populated boundary:

* `microValue_at_final`/`locContent_final_of_localValueAt` — at the exact final micro-time
  `c0 + 8*n` the `microValue` reader is the chain state's `locContent`, so the walk's value
  currency at the committed final clock *is* final-state content;
* `exists_populated_memoryBoundary` — a well-formed boundary whose cells carry, per committed
  finalize record, the genesis initial content and the committed final value, agreed with the
  selected initial state and with `microValue` at the committed final clock.

**Coverage honesty.** Cells are built for the finalize records whose decoded location passes the
canonical-address check and whose location carries a genesis record.  Both restrictions are
population filters, not soundness gaps: per-location balance in fact forces a genesis record at
every finalize location, and the Memory bus's canonical 48-bit encoding makes every faithful
record canonical — but neither fact is exported by the current engine (the address-limb goodness
sweep is named follow-up work), so the boundary this file populates is the canonically-addressed,
genesis-backed portion.  The cell's `finalClock` is the refresh-eliminated last-write time (the
committed record's own timestamp is not shard-bounded natively — the MemoryBump table does not tie
its refreshed clock to the public final clock). -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Execution
open SP1Clean.Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## `microValue` at the final micro-time -/

/-- At the exact final micro-time `c0 + 8*n`, the intra-window offset is `0` — before every
effect offset — so `microValue` reads the chain state `n` itself. -/
theorem microValue_at_final (initial : SailState) (c0 n : ℕ) (loc : MemLoc) :
    microValue initial c0 loc (c0 + 8 * n) =
      (chainState initial n).bind (locContent · loc) := by
  unfold microValue
  rw [if_neg (by omega)]
  cases loc with
  | reg index => simp [regEffectOffset]
  | ram cell => simp [ramEffectOffset]

/-- Convert value currency at the committed final clock into final-state content. -/
theorem locContent_final_of_microValue {initial final : SailState} {c0 n : ℕ}
    {loc : MemLoc} {v : BitVec 64}
    (chain : chainState initial n = some final)
    (current : microValue initial c0 loc (c0 + 8 * n) = some v) :
    locContent final loc = some v := by
  rwa [microValue_at_final, chain, Option.bind_some] at current

/-! ## The committed finalize records as a finite carrier -/

/-- The committed finalize pulls — the finite list behind `memoryFinalizeFrontier`. -/
noncomputable def memoryFinalizeRecords (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    List (MemoryMsg (ZMod p)) :=
  consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
    memoryChannel)

/-- Under per-location uniqueness, each committed finalize record is its location's frontier. -/
theorem memoryFinalizeFrontier_of_mem (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (huniq : MemoryFinalizeProviderUnique witness)
    {m : MemoryMsg (ZMod p)} (hm : m ∈ memoryFinalizeRecords witness) :
    memoryFinalizeFrontier witness (MemoryMsg.locOf m) = some m := by
  have hlen := pairwise_distinct_filter_length_le_one MemoryMsg.locOf
    (memoryFinalizeRecords witness) (MemoryMsg.locOf m)
    (memoryFinalizeConsumedMessages_pairwise witness huniq)
  have hmem : m ∈ (memoryFinalizeRecords witness).filter
      (fun x => decide (MemoryMsg.locOf x = MemoryMsg.locOf m)) :=
    List.mem_filter.mpr ⟨hm, by simp⟩
  show ((memoryFinalizeRecords witness).filter
      (fun x => decide (MemoryMsg.locOf x = MemoryMsg.locOf m))).head? = some m
  rcases hfe : (memoryFinalizeRecords witness).filter
      (fun x => decide (MemoryMsg.locOf x = MemoryMsg.locOf m)) with _ | ⟨a, t⟩
  · rw [hfe] at hmem; cases hmem
  · rw [hfe] at hmem hlen
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons b t' => simp at hlen
    subst ht
    have : m = a := by simpa using hmem
    simp [this]

/-! ## Address canonicity as a population filter -/

/-- Decidable form of `MemLoc.CanonicalAddress`. -/
def canonicalAddressCheck : MemLoc → Bool
  | .reg _ => true
  | .ram cell => decide (32 ≤ cell.toNat * 8) && decide (cell.toNat * 8 < 2 ^ 48)

theorem canonicalAddressCheck_iff (loc : MemLoc) :
    canonicalAddressCheck loc = true ↔ loc.CanonicalAddress := by
  cases loc with
  | reg index => simp [canonicalAddressCheck, MemLoc.CanonicalAddress]
  | ram cell => simp [canonicalAddressCheck, MemLoc.CanonicalAddress]

/-! ## The populated boundary -/

/-- **The populated native Memory boundary.** From the committed finalize records (restricted to
canonically-addressed, genesis-backed locations), a well-formed `CoreMemoryBoundary` whose cells
agree with the selected initial state and with the execution's `microValue` at the committed
final clock.  The caller converts the final conjunct to final-state `locContent` through
`locContent_final_of_localValueAt` once the constructed chain is in hand. -/
theorem exists_populated_memoryBoundary
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (initial : SailState)
    (finalTime : ℕ)
    (huniq : MemoryFinalizeProviderUnique witness)
    (initBound : MemoryInitProviderBound witness initial (Commit.initClkNat witness.data))
    (finTruth : ∀ loc m, memoryFinalizeFrontier witness loc = some m →
      MemoryMsg.locOf m = loc ∧
      LocalValueAt initial (Commit.initClkNat witness.data) loc finalTime m.value ∧
      ∃ m', MemoryMsg.locOf m' = loc ∧
        m'.value = m.value ∧ MemoryMsg.timeNat m' ≤ MemoryMsg.timeNat m ∧
        MemoryMsg.timeNat m' ≤ finalTime ∧
        LocalMemTruth initial (Commit.initClkNat witness.data) m') :
    ∃ b : Machine.CoreMemoryBoundary,
      b.WellFormed finalTime ∧
      ∀ cell ∈ b.cells,
        locContent initial cell.loc = some cell.initialValue ∧
        microValue initial (Commit.initClkNat witness.data) cell.loc finalTime =
          some cell.finalValue := by
  classical
  let selected : List (MemoryMsg (ZMod p)) :=
    (memoryFinalizeRecords witness).filter (fun m =>
      canonicalAddressCheck (MemoryMsg.locOf m) &&
        (memoryInitFrontier witness (MemoryMsg.locOf m)).isSome)
  have selectedFacts : ∀ m ∈ selected,
      m ∈ memoryFinalizeRecords witness ∧
        (MemoryMsg.locOf m).CanonicalAddress ∧
        (memoryInitFrontier witness (MemoryMsg.locOf m)).isSome := by
    intro m hm
    obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hm
    rw [Bool.and_eq_true] at hcond
    exact ⟨hmem, (canonicalAddressCheck_iff _).mp hcond.1, hcond.2⟩
  -- One populated cell per selected record.
  let cellOf : {m : MemoryMsg (ZMod p) // m ∈ selected} → Machine.CoreMemoryBoundaryCell :=
    fun x =>
      { loc := MemoryMsg.locOf x.1
        initialValue := Word.toBitVec64
          (((memoryInitFrontier witness (MemoryMsg.locOf x.1)).get
            (selectedFacts x.1 x.2).2.2).value)
        finalValue := Word.toBitVec64 x.1.value
        finalClock := MemoryMsg.timeNat (Classical.choose
          (finTruth (MemoryMsg.locOf x.1) x.1
            (memoryFinalizeFrontier_of_mem witness huniq (selectedFacts x.1 x.2).1)).2.2) }
  refine ⟨⟨selected.attach.map cellOf⟩, ⟨?_, ?_⟩, ?_⟩
  · -- LocationsNodup: cell locations are the selected records' locations, pairwise distinct.
    show ((selected.attach.map cellOf).map Machine.CoreMemoryBoundaryCell.loc).Nodup
    have mapEq : (selected.attach.map cellOf).map Machine.CoreMemoryBoundaryCell.loc =
        selected.map MemoryMsg.locOf := by
      rw [List.map_map]
      show selected.attach.map (fun x => MemoryMsg.locOf x.1) = selected.map MemoryMsg.locOf
      exact List.attach_map_val
    rw [mapEq]
    have hpw : selected.Pairwise (fun a b => MemoryMsg.locOf a ≠ MemoryMsg.locOf b) :=
      List.Pairwise.sublist List.filter_sublist
        (memoryFinalizeConsumedMessages_pairwise witness huniq)
    exact List.pairwise_map.mpr hpw
  · -- Per-cell canonical address and shard-bounded final clock.
    intro cell hcell
    obtain ⟨⟨m, hm⟩, -, rfl⟩ := List.mem_map.mp hcell
    refine ⟨(selectedFacts m hm).2.1, ?_⟩
    exact (Classical.choose_spec
      (finTruth (MemoryMsg.locOf m) m
        (memoryFinalizeFrontier_of_mem witness huniq (selectedFacts m hm).1)).2.2).2.2.2.1
  · -- Per-cell content agreement at both ends.
    intro cell hcell
    obtain ⟨⟨m, hm⟩, -, rfl⟩ := List.mem_map.mp hcell
    constructor
    · -- Genesis content: the init frontier record is a produced init push, so its
      -- `MemoryInitMessageBound` gives the initial `locContent` at its own location.
      set g := (memoryInitFrontier witness (MemoryMsg.locOf m)).get (selectedFacts m hm).2.2
        with hg
      have hfront : memoryInitFrontier witness (MemoryMsg.locOf m) = some g :=
        (Option.some_get (selectedFacts m hm).2.2).symm
      set flt := (producedMessages (typedTableInteractionsWith
          (memoryInitProviderTable witness) memoryChannel)).filter
            (fun x => decide (MemoryMsg.locOf x = MemoryMsg.locOf m)) with hflt
      have hhead : flt.head? = some g := hfront
      have hginfo : g ∈ flt := by
        cases hfe : flt with
        | nil => rw [hfe] at hhead; cases hhead
        | cons a t =>
          rw [hfe] at hhead
          simp only [List.head?_cons, Option.some.injEq] at hhead
          rw [← hhead]
          exact List.mem_cons_self
      rw [hflt] at hginfo
      obtain ⟨hgmem, hgloc⟩ := List.mem_filter.mp hginfo
      have hbound := memoryInitMessageBound_of_mem_produced witness initial
        (Commit.initClkNat witness.data) initBound g hgmem
      have hglocEq : MemoryMsg.locOf g = MemoryMsg.locOf m := by simpa using hgloc
      show locContent initial (MemoryMsg.locOf m) = some (Word.toBitVec64 g.value)
      rw [← hglocEq]
      exact hbound.1
    · -- Final content: the strengthened walk's value currency at the committed final clock.
      exact (finTruth (MemoryMsg.locOf m) m
        (memoryFinalizeFrontier_of_mem witness huniq (selectedFacts m hm).1)).2.1

/-! ## The boot boundary's image binding -/

/-- **The genesis provider cannot disagree with the committed ELF image on a boot shard**: every
active Memory-init push at an image-covered location carries exactly the committed image's cell
content.  The two content sources — the provider binding's `locContent` at the selected initial
state, and the committed image read through `IsInitialState.imageLoaded` — meet at the same
`locContent`, so the equality needs no uniqueness hypothesis. -/
theorem BootBoundaryFacts.memoryInit_image_bound
    {statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))}
    {witness : EnsembleWitness (sp1Ensemble (p := p))} {initial : SailState}
    (boot : BootBoundaryFacts statement witness initial) :
    ∀ m ∈ producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      memoryChannel), ∀ v,
      statement.program.imageContent? (MemoryMsg.locOf m) = some v →
      Word.toBitVec64 m.value = v := by
  intro m hm v hv
  have hbound := memoryInitMessageBound_of_mem_produced witness initial
    (Commit.initClkNat witness.data) boot.base.memoryProvider m hm
  have himg := GuestProgram.locContent_of_imageLoaded boot.isInitial.imageLoaded hv
  rw [hbound.1] at himg
  exact Option.some_injective _ himg

end SP1Clean.Soundness
