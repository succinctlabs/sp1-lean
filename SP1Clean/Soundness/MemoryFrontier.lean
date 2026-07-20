import SP1Clean.Soundness.TypedMemoryBalance

/-! # The genesis/final Memory frontier and the walk's frontier balance (B5)

`TypedMemoryBalance.realDecodedMemory_perlocBalance` (B4) landed the per-`MemLoc` Memory balance in the
**symmetric** form: both boundary provider tables' produced *and* consumed messages appear on both
sides, over *all* decoded rows (`decodedInstructionRows`), with binary multiplicities carried as the
`memBinary` premise.  This module collapses that symmetric balance to the exact shape the timed
grounding walk (`TimedGrounding.walk`) consumes,

  `∀ loc, optMS (live loc) + pushesAt rows loc = optMS (finM loc) + pullsAt rows loc`,

and constructs the per-`MemLoc` genesis frontier `live` (`memoryInitFrontier`) and final frontier
`finM` (`memoryFinalizeFrontier`) as `Option`s.

The collapse rests on four facts, threaded as honest premises where their discharge belongs to a
different workstream (all flagged in the theorem doc-strings):

* **Provider purity** — the init provider only pushes (`consumedMessages init = []`) and the finalize
  provider only pulls (`producedMessages finalize = []`).  Structurally each provider row emits one
  boolean-gated `pushIf`/`pullIf` (`MemoryProviderChip.main`/`MemoryFinalizeChip.main`), so purity
  follows from the `assertZero (m*(m-1))` gate; deriving it needs the provider-table interaction
  reduction plus the boolean gate from `witness.Constraints`, so it is taken here as
  `initPure`/`finPure`.
* **Genesis uniqueness** (`MemoryInitProviderUnique`, `ProviderBindings.lean`) — at most one active
  init push per location.  **This is where the init `Option` (`memoryInitFrontier`) becomes
  well-defined, and where P0.1 is consumed** (`optMS_memoryInitFrontier`).
* **Final uniqueness** (`MemoryFinalizeProviderUnique`, new here) — the finalize analogue.  It is
  *not* in the current `InitialBoundaryFacts`, so it is added as a definition and taken as a premise;
  it should join `InitialBoundaryFacts` (or be discharged by the extracted-AIR layer) exactly as the
  init uniqueness is.
* **Padding rows emit no active Memory** (`paddingEmpty`) — a non-active row (`is_real ≠ 1`) contributes
  nil produced/consumed Memory messages, reconciling B4's `decodedInstructionRows` (all rows) with the
  walk's `realDecodedInstructionRows` (active rows).  This is the per-chip Memory emission fact the
  workstream defers; under selector binarity it is exactly "`is_real = 0` ⇒ no active Memory".

The `LiveOK` invariant is proved outright from the genesis provider bound (`MemoryInitProviderBound`,
via `localMemTruth_of_mem_produced`) and `MemoryInitMessageBound`. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.Execution
open SP1Clean.Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Generic list/multiset helpers -/

section Generic

/-- An optional boundary record is the coercion of a `≤ 1`-length list to a multiset. -/
lemma optMS_head?_eq_coe {α : Type} (xs : List α) (h : xs.length ≤ 1) :
    optMS xs.head? = (↑xs : Multiset α) := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => simp at h

/-- Coerced-list filter distributes over append. -/
lemma filter_coe_append {α : Type*} (P : α → Prop) [DecidablePred P] (X Y : List α) :
    Multiset.filter P (↑(X ++ Y) : Multiset α) =
      Multiset.filter P (↑X : Multiset α) + Multiset.filter P (↑Y : Multiset α) := by
  rw [← Multiset.coe_add, Multiset.filter_add]

/-- Coerced-list filter distributes over `flatMap`, block by block. -/
lemma filter_coe_flatMap {α β : Type*} (P : β → Prop) [DecidablePred P]
    (l : List α) (f : α → List β) :
    Multiset.filter P (↑(l.flatMap f) : Multiset β) =
      (l.map (fun x => Multiset.filter P (↑(f x) : Multiset β))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih, filter_coe_append]

/-- A mapped-sum is unchanged by dropping elements whose image is zero. -/
lemma sum_map_eq_sum_filter {α : Type*} {β : Type*} [AddCommMonoid β]
    (l : List α) (q : α → Bool) (g : α → β)
    (h : ∀ x ∈ l, q x = false → g x = 0) :
    (l.map g).sum = ((l.filter q).map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    split_ifs with hq
    · rw [List.map_cons, List.sum_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        h a List.mem_cons_self (by simpa using hq), zero_add]

/-- A list pairwise-distinct under `f` has at most one element mapping to any given value. -/
lemma pairwise_distinct_filter_length_le_one {α : Type*} {γ : Type*} [DecidableEq γ]
    (f : α → γ) (l : List α) (loc : γ)
    (h : l.Pairwise (fun a b => f a ≠ f b)) :
    (l.filter (fun a => decide (f a = loc))).length ≤ 1 := by
  rcases hfilter : l.filter (fun a => decide (f a = loc)) with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp
  · simp
  · exfalso
    have hpw : (l.filter (fun a => decide (f a = loc))).Pairwise (fun a b => f a ≠ f b) :=
      List.Pairwise.sublist List.filter_sublist h
    rw [hfilter] at hpw
    have hne : f a ≠ f b := (List.pairwise_cons.mp hpw).1 b List.mem_cons_self
    have ha : f a = loc := by
      have hmem : a ∈ l.filter (fun a => decide (f a = loc)) := by
        rw [hfilter]; exact List.mem_cons_self
      simpa using (List.mem_filter.mp hmem).2
    have hb : f b = loc := by
      have hmem : b ∈ l.filter (fun a => decide (f a = loc)) := by
        rw [hfilter]; exact List.mem_cons_of_mem _ List.mem_cons_self
      simpa using (List.mem_filter.mp hmem).2
    exact hne (ha.trans hb.symm)

end Generic

/-! ## The per-`MemLoc` genesis and final frontiers -/

/-- The genesis (init-provider) frontier record at a location: the unique active init push whose
location is `loc`, packaged as an `Option`.  Well-definedness — that the filter has `≤ 1` element —
is `MemoryInitProviderUnique`. -/
noncomputable def memoryInitFrontier (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
    memoryChannel)).filter (fun m => decide (Semantics.MemoryMsg.locOf m = loc))).head?

/-- The final (finalize-provider) frontier record at a location: the unique active finalize pull
whose location is `loc`. -/
noncomputable def memoryFinalizeFrontier (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (loc : MemLoc) : Option (MemoryMsg (ZMod p)) :=
  ((consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
    memoryChannel)).filter (fun m => decide (Semantics.MemoryMsg.locOf m = loc))).head?

/-- **The finalize-provider per-location uniqueness fact** (mirror of `MemoryInitProviderUnique`).  At
most one active finalize pull per register or aligned 64-bit RAM cell.  Like the init uniqueness, Clean
channel balance alone cannot force this, so it is an honest boundary companion fact — to be discharged
by the extracted-AIR layer, and (unlike the init one) not yet a field of `InitialBoundaryFacts`. -/
noncomputable def MemoryFinalizeProviderUnique
    (witness : EnsembleWitness (sp1Ensemble (p := p))) : Prop :=
  (typedTableInteractionsWith (memoryFinalizeProviderTable witness) memoryChannel).Pairwise
    fun i₁ i₂ => signedVal i₁.mult ≠ 0 → signedVal i₂.mult ≠ 0 →
      Semantics.MemoryMsg.locOf i₁.message ≠ Semantics.MemoryMsg.locOf i₂.message

/-! ## The frontier ↔ filtered-multiset bridges -/

/-- Active init pushes are pairwise distinct in location (from `MemoryInitProviderUnique`). -/
lemma memoryInitProducedMessages_pairwise
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (huniq : MemoryInitProviderUnique witness) :
    (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
        memoryChannel)).Pairwise
      (fun a b => Semantics.MemoryMsg.locOf a ≠ Semantics.MemoryMsg.locOf b) := by
  unfold producedMessages
  rw [List.pairwise_map]
  refine (List.Pairwise.sublist List.filter_sublist huniq).imp_of_mem ?_
  intro i₁ i₂ hi₁ hi₂ hrel
  have h₁ : signedVal i₁.mult = 1 := by simpa using (List.mem_filter.mp hi₁).2
  have h₂ : signedVal i₂.mult = 1 := by simpa using (List.mem_filter.mp hi₂).2
  exact hrel (by rw [h₁]; exact one_ne_zero) (by rw [h₂]; exact one_ne_zero)

/-- Active finalize pulls are pairwise distinct in location (from `MemoryFinalizeProviderUnique`). -/
lemma memoryFinalizeConsumedMessages_pairwise
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (huniq : MemoryFinalizeProviderUnique witness) :
    (consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
        memoryChannel)).Pairwise
      (fun a b => Semantics.MemoryMsg.locOf a ≠ Semantics.MemoryMsg.locOf b) := by
  unfold consumedMessages
  rw [List.pairwise_map]
  refine (List.Pairwise.sublist List.filter_sublist huniq).imp_of_mem ?_
  intro i₁ i₂ hi₁ hi₂ hrel
  have h₁ : signedVal i₁.mult = -1 := by simpa using (List.mem_filter.mp hi₁).2
  have h₂ : signedVal i₂.mult = -1 := by simpa using (List.mem_filter.mp hi₂).2
  exact hrel (by rw [h₁]; norm_num) (by rw [h₂]; norm_num)

/-- **The genesis-frontier bridge.** `optMS (memoryInitFrontier witness loc)` is exactly the
per-location filter of the active init pushes — the multiset `MemoryInitProviderUnique` guarantees has
size `≤ 1`.  This is where the genesis `Option` is justified. -/
lemma optMS_memoryInitFrontier (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (huniq : MemoryInitProviderUnique witness) (loc : MemLoc) :
    optMS (memoryInitFrontier witness loc) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
          memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [memoryInitFrontier, optMS_head?_eq_coe _
    (pairwise_distinct_filter_length_le_one Semantics.MemoryMsg.locOf _ loc
      (memoryInitProducedMessages_pairwise witness huniq)),
    Multiset.filter_coe]

/-- **The final-frontier bridge** (finalize analogue of `optMS_memoryInitFrontier`). -/
lemma optMS_memoryFinalizeFrontier (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (huniq : MemoryFinalizeProviderUnique witness) (loc : MemLoc) :
    optMS (memoryFinalizeFrontier witness loc) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(consumedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
          memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [memoryFinalizeFrontier, optMS_head?_eq_coe _
    (pairwise_distinct_filter_length_le_one Semantics.MemoryMsg.locOf _ loc
      (memoryFinalizeConsumedMessages_pairwise witness huniq)),
    Multiset.filter_coe]

/-! ## The active-row carrier and its per-key push/pull bridges -/

/-- The walk's ordinary `RowFacts` carrier: the active decoded rows' ordinary records. -/
noncomputable def memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    List (RowFacts p) :=
  (realDecodedInstructionRows witness.data witness.tables).map
    (fun decoded => decoded.ordinaryRowFacts witness.data)

/-- One active row's per-location pushes are its produced Memory messages, filtered. -/
lemma rowPushesAt_ordinaryRowFacts_coe (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (loc : MemLoc) :
    (↑(rowPushesAt (decoded.ordinaryRowFacts data) loc) : Multiset (MemoryMsg (ZMod p))) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(decoded.producedMemoryMessages data) : Multiset (MemoryMsg (ZMod p))) := by
  rw [Multiset.filter_coe]
  simp only [rowPushesAt, DecodedInstructionRow.ordinaryRowFacts_memPushes]

/-- One active row's per-location pulls are its consumed Memory messages, filtered. -/
lemma rowPullsAt_ordinaryRowFacts_coe (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p)) (loc : MemLoc) :
    (↑(rowPullsAt (decoded.ordinaryRowFacts data) loc) : Multiset (MemoryMsg (ZMod p))) =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑(decoded.consumedMemoryMessages data) : Multiset (MemoryMsg (ZMod p))) := by
  have key : ((decoded.consumedMemoryMessages data).map
        (fun message => (message,
          StateMsg.timeNat (statePullMessage (decoded.toChipRow data))))).map (fun x => x.1)
      = decoded.consumedMemoryMessages data := by
    simp only [List.map_map, Function.comp_def, List.map_id_fun', id_eq]
  rw [Multiset.filter_coe]
  simp only [rowPullsAt, DecodedInstructionRow.ordinaryRowFacts_memPulls, key]

/-- **The active push bridge.** The active carrier's total per-location pushes equal the filter of all
decoded rows' produced Memory messages — the term appearing in B4's balance.  Padding rows drop out
(`paddingEmpty`). -/
lemma pushesAt_memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (loc : MemLoc) :
    pushesAt (memoryFrontierRows witness) loc =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.producedMemoryMessages witness.data)) :
            Multiset (MemoryMsg (ZMod p))) := by
  have hL : pushesAt (memoryFrontierRows witness) loc =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(decoded.producedMemoryMessages witness.data) : Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [pushesAt, memoryFrontierRows, List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro decoded _
    simp only [Function.comp]
    exact rowPushesAt_ordinaryRowFacts_coe decoded witness.data loc
  have hR : Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      (↑((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.producedMemoryMessages witness.data)) :
          Multiset (MemoryMsg (ZMod p))) =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(decoded.producedMemoryMessages witness.data) :
            Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [filter_coe_flatMap,
      show realDecodedInstructionRows witness.data witness.tables =
        (decodedInstructionRows (p := p) witness.tables).filter
          (fun row => decide ((row.toChipRow witness.data).is_real = 1)) from rfl]
    exact sum_map_eq_sum_filter _ _ _ (fun decoded decodedMem hq => by
      have hne : (decoded.toChipRow witness.data).is_real ≠ 1 := by simpa using hq
      rw [(paddingEmpty decoded decodedMem hne).1]; rfl)
  rw [hL, hR]

/-- **The active pull bridge** (consumed analogue of `pushesAt_memoryFrontierRows`). -/
lemma pullsAt_memoryFrontierRows (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (loc : MemLoc) :
    pullsAt (memoryFrontierRows witness) loc =
      Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
        (↑((decodedInstructionRows (p := p) witness.tables).flatMap
          (fun decoded => decoded.consumedMemoryMessages witness.data)) :
            Multiset (MemoryMsg (ZMod p))) := by
  have hL : pullsAt (memoryFrontierRows witness) loc =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(decoded.consumedMemoryMessages witness.data) : Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [pullsAt, memoryFrontierRows, List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro decoded _
    simp only [Function.comp]
    exact rowPullsAt_ordinaryRowFacts_coe decoded witness.data loc
  have hR : Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
      (↑((decodedInstructionRows (p := p) witness.tables).flatMap
        (fun decoded => decoded.consumedMemoryMessages witness.data)) :
          Multiset (MemoryMsg (ZMod p))) =
      ((realDecodedInstructionRows witness.data witness.tables).map
        (fun decoded => Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(decoded.consumedMemoryMessages witness.data) :
            Multiset (MemoryMsg (ZMod p))))).sum := by
    rw [filter_coe_flatMap,
      show realDecodedInstructionRows witness.data witness.tables =
        (decodedInstructionRows (p := p) witness.tables).filter
          (fun row => decide ((row.toChipRow witness.data).is_real = 1)) from rfl]
    exact sum_map_eq_sum_filter _ _ _ (fun decoded decodedMem hq => by
      have hne : (decoded.toChipRow witness.data).is_real ≠ 1 := by simpa using hq
      rw [(paddingEmpty decoded decodedMem hne).2]; rfl)
  rw [hL, hR]

/-! ## The frontier balance -/

/-- **The frontier-form per-`MemLoc` Memory balance** — the exact input `TimedGrounding.walk`
consumes.  Collapsing B4's symmetric balance with provider purity (`initPure`/`finPure`), the two
uniqueness facts (packaged into the frontier `Option`s), and the padding reconciliation gives

  `optMS (live loc) + pushesAt rows loc = optMS (finM loc) + pullsAt rows loc`

with `live = memoryInitFrontier witness`, `finM = memoryFinalizeFrontier witness`, and
`rows = memoryFrontierRows witness`. -/
theorem memoryFrontierBalance (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1)
    (initPure : consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      memoryChannel) = [])
    (finPure : producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
      memoryChannel) = [])
    (initUnique : MemoryInitProviderUnique witness)
    (finalizeUnique : MemoryFinalizeProviderUnique witness)
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (loc : MemLoc) :
    optMS (memoryInitFrontier witness loc) + pushesAt (memoryFrontierRows witness) loc =
      optMS (memoryFinalizeFrontier witness loc) + pullsAt (memoryFrontierRows witness) loc := by
  have hbal := realDecodedMemory_perlocBalance witness balanced memBinary loc
  rw [filter_coe_append, filter_coe_append, filter_coe_append, filter_coe_append,
    initPure, finPure] at hbal
  simp only [Multiset.coe_nil, Multiset.filter_zero, add_zero, zero_add] at hbal
  rw [optMS_memoryInitFrontier witness initUnique,
    optMS_memoryFinalizeFrontier witness finalizeUnique,
    pushesAt_memoryFrontierRows witness paddingEmpty,
    pullsAt_memoryFrontierRows witness paddingEmpty,
    add_comm, hbal, add_comm]

/-! ## The genesis `LiveOK` invariant -/

/-- The raw genesis bound (content + timing) of one active init push, extracted from
`MemoryInitProviderBound`.  Mirrors the body of `localMemTruth_of_mem_produced`, exposing the
`MemoryInitMessageBound` needed for `LiveOK`'s value-at-`initClk` and time bound. -/
theorem memoryInitMessageBound_of_mem_produced
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (initial : SailState) (initialClock : ℕ)
    (bound : MemoryInitProviderBound witness initial initialClock)
    (message : MemoryMsg (ZMod p))
    (member : message ∈ producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      memoryChannel)) :
    MemoryInitMessageBound initial initialClock message := by
  unfold producedMessages at member
  obtain ⟨interaction, interactionMem, messageEq⟩ := List.mem_map.mp member
  obtain ⟨typedMem, positive⟩ := List.mem_filter.mp interactionMem
  simp only [decide_eq_true_eq] at positive
  have rawMem : interaction.raw ∈
      (memoryInitProviderTable witness).interactionsWith memoryChannel.toRaw := by
    rw [← typedTableInteractionsWith_raw]
    exact List.mem_map_of_mem typedMem
  have multNonzero : interaction.raw.mult ≠ 0 := by
    intro multZero
    change signedVal interaction.raw.mult = 1 at positive
    rw [multZero] at positive
    simp [signedVal] at positive
  let rebound : TypedInteraction memoryChannel :=
    { raw := interaction.raw
      channel_eq := (memoryInitProviderTable witness).channel_eq_of_mem_interactionsWith rawMem }
  have semantic := bound interaction.raw rawMem multNonzero
  change MemoryInitMessageBound initial initialClock rebound.message at semantic
  have reboundEq : rebound = interaction := TypedInteraction.raw_injective rfl
  rw [reboundEq, messageEq] at semantic
  exact semantic

/-- **The genesis `LiveOK` invariant** at the shard-initial clock `t₀ = initClkNat`.  Every active
init push at a location `loc` is the frontier record there: it sits at `loc`, its `LocalMemTruth`
holds, its value is the initial content current at `t₀`, and its access time is `≤ t₀`.  Consumes the
genesis provider bound (`MemoryInitProviderBound`) and the provider `WordRangeCheck`/`clk_low`
requirement (via `localMemTruth_of_mem_produced`). -/
theorem memoryInit_liveOK
    {statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))}
    {witness : EnsembleWitness (sp1Ensemble (p := p))} {initial : SailState}
    (constraints : witness.Constraints)
    (boundary : InitialBoundaryFacts statement witness initial) :
    LiveOK initial (Commit.initClkNat witness.data) (Commit.initClkNat witness.data)
      (memoryInitFrontier witness) := by
  intro loc m hm
  have hmem : m ∈ (producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      memoryChannel)).filter (fun m => decide (Semantics.MemoryMsg.locOf m = loc)) := by
    rw [memoryInitFrontier] at hm
    exact List.mem_of_mem_head? hm
  have hloc : Semantics.MemoryMsg.locOf m = loc := by simpa using (List.mem_filter.mp hmem).2
  have hprod : m ∈ producedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      memoryChannel) := (List.mem_filter.mp hmem).1
  have memTruth := MemoryInitProviderBound.localMemTruth_of_mem_produced witness constraints
    initial (Commit.initClkNat witness.data) boundary.memoryProvider m hprod
  have hbound := memoryInitMessageBound_of_mem_produced witness initial
    (Commit.initClkNat witness.data) boundary.memoryProvider m hprod
  refine ⟨hloc, memTruth, ?_, hbound.2⟩
  rw [← hloc]
  exact localValueAt_of_initial hbound.1 (le_refl _)

end SP1Clean.Soundness
