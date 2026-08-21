import SP1Clean.Soundness.ChipContracts

/-! # Wiring the refresh elimination onto the walk's per-row carrier (W3)

`Soundness/RefreshElimination.lean` proves the generic multiset fact — a balanced touch multiset
split into plain touches and *refreshes* has a refresh-free rewriting — and
`AlignedCarrier.exists_rewrittenTouchLists` proves the generic list fact — per-location multiset
rewrites of a batch's touch pairs are realized by per-row rewritten touch lists.  This module joins
the two into the single statement the capstone consumes: from the **widened** per-location memory
balance (the one that still carries the MemoryBump table's pull/push pairs) and the `IsRefresh`
shape of those pairs, there are per-row touch lists whose per-location balance is refresh-free,
each of whose touches keeps its read time and its pushed record and weakens only its pulled record
(same `value` image, no-later time), together with a rewritten finalize frontier.

The module additionally supplies:

* the two per-location bridges `pushesAt_of_touchLists` / `pullsAt_of_touchLists`, which put the
  walk's `pushesAt`/`pullsAt` aggregates into the `touchPairsAt` pair form both engines speak; and
* the timestamp-goodness helpers (`clkHigh_lt_of_timeNat_le`, `forall_mem_of_balance`) that turn
  "every memory push carries a genuine 24-bit timestamp" into the same statement for every memory
  *pull* — the two facts `memoryBump_isRefresh` receives as premises.

Nothing here mentions chips or circuits: every input is an abstract row/touch list. -/

namespace SP1Clean.Soundness

open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Timestamp goodness -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Two genuine 24-bit clock limbs recombine to a genuine 48-bit time. -/
theorem clkNat_lt_of_limbs {hi lo : ZMod p} (hhi : hi.val < 2 ^ 24) (hlo : lo.val < 2 ^ 24) :
    Semantics.clkNat hi lo < 2 ^ 48 := by
  rw [Semantics.clkNat]
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **The high-limb bound from a time bound.**  A memory record whose ℕ time is below `2 ^ 48` has a
genuine 24-bit high clock limb: that limb contributes `clk_high.val * 2 ^ 24` to the time. -/
theorem clkHigh_lt_of_timeNat_le {m : MemoryMsg (ZMod p)} {B : ℕ}
    (h : MemoryMsg.timeNat m ≤ B) (hB : B < 2 ^ 48) : m.clk_high.val < 2 ^ 24 := by
  by_contra bad
  rw [MemoryMsg.timeNat, Semantics.clkNat] at h
  have : 2 ^ 24 * 2 ^ 24 ≤ m.clk_high.val * 2 ^ 24 := Nat.mul_le_mul_right _ (by omega)
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Balance membership.**  In a two-sided multiset balance, a property of every record on the
produced side holds of every record on the consumed side. -/
theorem forall_mem_of_balance {α : Type} {G : α → Prop} {produced consumed : Multiset α}
    (hbal : produced = consumed) (hgood : ∀ m ∈ produced, G m) : ∀ m ∈ consumed, G m :=
  fun m hm => hgood m (by rw [hbal]; exact hm)

/-! ## Per-location touch pairs -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Filtering commutes with mapping when the predicate is pulled back along the map. -/
private theorem map_filter_comm {α β : Type*} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).filter q = (l.filter fun a => q (f a)).map f := by
  rw [List.filter_map]
  rfl

/-- The per-location `(pulled, pushed)` message pairs of a batch of per-row touch lists.  This is
literally the multiset shape `AlignedCarrier.exists_rewrittenTouchLists` consumes and produces. -/
def touchPairsAt (ts : List (List (Touch p))) (loc : MemLoc) :
    Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) :=
  (ts.map fun l =>
    (↑((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)) :
      Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))).sum

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **The push bridge.**  A batch of rows whose push lists are the pushed components of per-row
touch lists has the touch pairs' pushed components as its per-location push aggregate. -/
theorem pushesAt_of_touchLists {α : Type*} (rows : List α) (f : α → RowFacts p)
    (g : α → List (Touch p)) (hpush : ∀ a ∈ rows, (f a).memPushes = (g a).map Prod.snd)
    (loc : MemLoc) :
    pushesAt (rows.map f) loc = (touchPairsAt (rows.map g) loc).map Prod.snd := by
  rw [pushesAt, touchPairsAt, map_listSum, List.map_map, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  simp only [Function.comp_apply, Function.comp_def, rowPushesAt, hpush a ha, Multiset.map_coe,
    List.map_map, map_filter_comm]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **The pull bridge**, the companion for the pulled components.  The per-touch location agreement
is what turns the pull filter (by the pulled record's location) into the push filter. -/
theorem pullsAt_of_touchLists {α : Type*} (rows : List α) (f : α → RowFacts p)
    (g : α → List (Touch p)) (hpull : ∀ a ∈ rows, (f a).memPulls = (g a).map Prod.fst)
    (hloc : ∀ a ∈ rows, ∀ tc ∈ g a,
      MemoryMsg.locOf (tc : Touch p).2 = MemoryMsg.locOf (tc : Touch p).1.1)
    (loc : MemLoc) :
    pullsAt (rows.map f) loc = (touchPairsAt (rows.map g) loc).map Prod.fst := by
  rw [pullsAt, touchPairsAt, map_listSum, List.map_map, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  simp only [Function.comp_apply, Function.comp_def, rowPullsAt, hpull a ha, Multiset.map_coe,
    List.map_map, map_filter_comm]
  exact congrArg
    (fun l => (↑(List.map (fun tc : Touch p => tc.1.1) l) : Multiset (MemoryMsg (ZMod p))))
    (List.filter_congr fun tc htc => by rw [hloc a ha tc htc])

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Membership in a `List.sum` of per-element multisets (a public copy of the walk's private
helper). -/
private theorem mem_listSum_map {α : Type*} {β : Type} (f : α → Multiset β) :
    ∀ (l : List α) (b : β), b ∈ (l.map f).sum ↔ ∃ a ∈ l, b ∈ f a
  | [], b => by simp
  | a :: l, b => by
      simp only [List.map_cons, List.sum_cons, Multiset.mem_add, mem_listSum_map f l b,
        List.mem_cons]
      constructor
      · rintro (h | ⟨a', ha', hb⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨a', Or.inr ha', hb⟩
      · rintro ⟨a', rfl | ha', hb⟩
        · exact Or.inl hb
        · exact Or.inr ⟨a', ha', hb⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Membership in a batch's per-location push aggregate. -/
theorem mem_pushesAt {rows : List (RowFacts p)} {loc : MemLoc} {m : MemoryMsg (ZMod p)} :
    m ∈ pushesAt rows loc ↔ ∃ r ∈ rows, m ∈ r.memPushes ∧ MemoryMsg.locOf m = loc := by
  rw [pushesAt, mem_listSum_map]
  constructor
  · rintro ⟨r, hr, hm⟩
    have hm' := List.mem_filter.mp (Multiset.mem_coe.mp hm)
    exact ⟨r, hr, hm'.1, by simpa using hm'.2⟩
  · rintro ⟨r, hr, hm, hloc⟩
    exact ⟨r, hr, Multiset.mem_coe.mpr (List.mem_filter.mpr ⟨hm, by simpa using hloc⟩)⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Membership in a batch's per-location pull aggregate. -/
theorem mem_pullsAt {rows : List (RowFacts p)} {loc : MemLoc} {m : MemoryMsg (ZMod p)} :
    m ∈ pullsAt rows loc ↔
      (∃ r ∈ rows, ∃ mp ∈ r.memPulls, (mp : MemoryMsg (ZMod p) × ℕ).1 = m) ∧
        MemoryMsg.locOf m = loc := by
  rw [pullsAt, mem_listSum_map]
  constructor
  · rintro ⟨r, hr, hm⟩
    have hm' := List.mem_filter.mp (Multiset.mem_coe.mp hm)
    obtain ⟨mp, hmp, hmpEq⟩ := List.mem_map.mp hm'.1
    exact ⟨⟨r, hr, mp, hmp, hmpEq⟩, by simpa using hm'.2⟩
  · rintro ⟨⟨r, hr, mp, hmp, rfl⟩, hloc⟩
    exact ⟨r, hr, Multiset.mem_coe.mpr (List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨mp, hmp, rfl⟩, by simpa using hloc⟩)⟩

/-! ## Transporting one row's evidence across the pulled-record rewrite -/

/-- The per-touch rewrite the elimination produces: the read micro-time and the pushed record are
kept, and the pulled record is replaced by one of equal `value` image at a no-later `time`. -/
def TouchRewrite {β : Type} (value : MemoryMsg (ZMod p) → β) (time : MemoryMsg (ZMod p) → ℕ)
    (tc tc' : Touch p) : Prop :=
  (tc' : Touch p).1.2 = (tc : Touch p).1.2 ∧ (tc' : Touch p).2 = (tc : Touch p).2 ∧
    value (tc' : Touch p).1.1 = value (tc : Touch p).1.1 ∧
    time (tc' : Touch p).1.1 ≤ time (tc : Touch p).1.1

/-- The concrete per-touch rewrite: the read micro-time and the pushed record are kept, and the
pulled record is replaced by one at the same location with the same value at a no-later time. -/
def PullRewrite (tc tc' : Touch p) : Prop :=
  (tc' : Touch p).1.2 = (tc : Touch p).1.2 ∧ (tc' : Touch p).2 = (tc : Touch p).2 ∧
    MemoryMsg.locOf (tc' : Touch p).1.1 = MemoryMsg.locOf (tc : Touch p).1.1 ∧
    (tc' : Touch p).1.1.value = (tc : Touch p).1.1.value ∧
    MemoryMsg.timeNat (tc' : Touch p).1.1 ≤ MemoryMsg.timeNat (tc : Touch p).1.1

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The generic rewrite at the SP1 instantiation (`value = (location, word)`, `time = timeNat`) is
the concrete `PullRewrite`. -/
theorem pullRewrite_of_touchRewrite {tc tc' : Touch p}
    (h : TouchRewrite (fun m : MemoryMsg (ZMod p) => (MemoryMsg.locOf m, m.value))
      MemoryMsg.timeNat tc tc') : PullRewrite tc tc' :=
  ⟨h.1, h.2.1, congrArg Prod.fst h.2.2.1, congrArg Prod.snd h.2.2.1, h.2.2.2⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- A push-time chain transfers across a push-preserving `Forall₂` of touches. -/
private theorem isChain_push_of_forall₂ {r : Touch p → Touch p → Prop}
    (hsnd : ∀ a b, r a b → (b : Touch p).2 = (a : Touch p).2) :
    ∀ {l l' : List (Touch p)}, List.Forall₂ r l l' →
      List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) l →
      List.IsChain (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2) l' := by
  intro l l' h
  induction h with
  | nil => intro _; exact List.isChain_nil
  | @cons a b l l' hR hrest ih =>
      intro hchain
      cases hrest with
      | nil => exact List.isChain_singleton _
      | @cons a₂ b₂ l₂ l₂' hR₂ hrest₂ =>
          rw [List.isChain_cons_cons] at hchain ⊢
          exact ⟨by rw [hsnd _ _ hR, hsnd _ _ hR₂]; exact hchain.1, ih hchain.2⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **`RowOK` across the rewrite.**  Every field of `rowOK_alignedOf` reads only the pushed record,
the read micro-time, or the pulled record's location and value — all preserved — except the slot
order, which improves because the rewritten pull is no later. -/
theorem rowOK_alignedOf_pullRewrite (initialClock : ℕ) (r_ord : RowFacts p)
    (touches touches' : List (Touch p)) (hrew : List.Forall₂ PullRewrite touches touches')
    (htime8 : StateMsg.timeNat r_ord.statePush = StateMsg.timeNat r_ord.statePull + 8)
    (halign8 : StateMsg.timeNat r_ord.statePull % 8 = initialClock % 8)
    (htouch : ∀ tc ∈ touches, TouchOK (StateMsg.timeNat r_ord.statePull) tc.1 tc.2)
    (hchain : ∀ loc : MemLoc, List.IsChain
      (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc)))
    (hpushClk : ∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound tc.2)
    (hslot : ∀ tc ∈ touches,
      MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    RowOK initialClock (alignedOf r_ord touches') := by
  have hpair : ∀ tc' ∈ touches', ∃ tc ∈ touches, PullRewrite tc tc' :=
    forall₂_exists_left hrew
  refine rowOK_alignedOf initialClock r_ord touches' htime8 halign8 ?_ ?_ ?_ ?_
  · intro tc' htc'
    obtain ⟨tc, htc, hread, hpush, hloc, hval, -⟩ := hpair tc' htc'
    have base := htouch tc htc
    refine ⟨by rw [hpush, hloc]; exact base.loc_eq, by rw [hread]; exact base.read_lo,
      by rw [hread, hloc]; exact base.read_hi, ?_⟩
    rcases base.push_kind with ⟨hv, ht⟩ | ht
    · exact Or.inl ⟨by rw [hpush, hval]; exact hv, by rw [hpush, hread]; exact ht⟩
    · exact Or.inr (by rw [hpush]; exact ht)
  · intro loc
    refine isChain_push_of_forall₂ (fun (a b : Touch p) (h : PullRewrite a b) => h.2.1) ?_
      (hchain loc)
    exact forall₂_filter_congr (P := fun pq : Touch p => MemoryMsg.locOf pq.2 = loc)
      (fun (a b : Touch p) (h : PullRewrite a b) => by rw [h.2.1]) hrew
  · intro tc' htc'
    obtain ⟨tc, htc, -, hpush, -⟩ := hpair tc' htc'
    rw [hpush]
    exact hpushClk tc htc
  · intro tc' htc' _
    obtain ⟨tc, htc, -, hpush, -, -, htime⟩ := hpair tc' htc'
    have := hslot tc htc
    rw [hpush]
    omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **`ValueAligned` across the rewrite.**  The rewritten aligned carrier still matches every
ordinary pull — at the same location with the same value inside the same read window — so the four
carrier transports of `Soundness/TimedGrounding.lean` apply to it. -/
theorem valueAligned_alignedOf_pullRewrite (r_ord : RowFacts p)
    (touches touches' : List (Touch p)) (hrew : List.Forall₂ PullRewrite touches touches')
    (halign : AlignsWith (alignedOf r_ord touches) r_ord)
    (hpullClk : ∀ mp ∈ r_ord.memPulls, SP1Clean.Channels.MemoryMsg.ClkBound mp.1) :
    ValueAligned (alignedOf r_ord touches') r_ord where
  pullTime := rfl
  pullPc := rfl
  pushTime := rfl
  pushPc := rfl
  pushes := by
    have hmap : touches'.map Prod.snd = touches.map Prod.snd :=
      map_snd_eq_of_forall₂ (fun a b h => h.2.1) hrew
    show (touches'.map Prod.snd).Perm r_ord.memPushes
    rw [hmap]
    exact halign.pushes
  ordTime := halign.ordTime
  pullClk := hpullClk
  match_ := by
    intro mp hmp
    obtain ⟨mp', hmp'_mem, hmsg, hlo, hhi⟩ := halign.match_ mp hmp
    obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp hmp'_mem
    obtain ⟨tc', htc', hread, -, hloc, hval, -⟩ := forall₂_exists_right hrew tc htc
    refine ⟨tc'.1, List.mem_map_of_mem htc', ?_, ?_, ?_, ?_⟩
    · rw [hloc, hmsg]
    · rw [hval, hmsg]
    · show StateMsg.timeNat r_ord.statePull ≤ tc'.1.2
      rw [hread]
      exact hlo
    · show tc'.1.2 ≤ StateMsg.timeNat r_ord.statePull + readWindow (MemoryMsg.locOf mp.1)
      rw [hread]
      exact hhi

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `ValueAligned` transports across a State re-spelling that preserves time and pc image. -/
theorem valueAligned_stateRespell {r_new r_ord : RowFacts p} (h : ValueAligned r_new r_ord)
    {pull push : StateMsg (ZMod p)}
    (hpullT : StateMsg.timeNat pull = StateMsg.timeNat r_new.statePull)
    (hpullP : StateMsg.pcBits pull = StateMsg.pcBits r_new.statePull)
    (hpushT : StateMsg.timeNat push = StateMsg.timeNat r_new.statePush)
    (hpushP : StateMsg.pcBits push = StateMsg.pcBits r_new.statePush) :
    ValueAligned (stateRespell r_new pull push) r_ord where
  pullTime := hpullT.trans h.pullTime
  pullPc := hpullP.trans h.pullPc
  pushTime := hpushT.trans h.pushTime
  pushPc := hpushP.trans h.pushPc
  pushes := h.pushes
  ordTime := h.ordTime
  pullClk := h.pullClk
  match_ := by
    intro mp hmp
    obtain ⟨mp', hmp'_mem, hloc, hval, hlo, hhi⟩ := h.match_ mp hmp
    refine ⟨mp', hmp'_mem, hloc, hval, ?_, ?_⟩
    · show StateMsg.timeNat pull ≤ mp'.2
      rw [hpullT]
      exact hlo
    · show mp'.2 ≤ StateMsg.timeNat pull + readWindow (MemoryMsg.locOf mp.1)
      rw [hpullT]
      exact hhi

/-! ## The refresh-free carrier -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **The refresh-free per-row carrier.**  From the widened per-location memory balance — the rows'
touch pairs plus a refresh table's own `(pulled, pushed)` pairs, against the init/finalize
frontiers — and the `IsRefresh` shape of every refresh pair, there are rewritten per-row touch lists
whose per-location balance carries **no** refresh contribution, each touch rewritten only in its
pulled record, together with a rewritten finalize frontier whose records are the weakened
originals.

This is the exact statement the capstone feeds `TimedGrounding.walk`: the walk consumes the
refresh-free balance, and `TimedGrounding.ValueAligned` transports its conclusions back to the
physical rows across the pulled-record rewrite. -/
theorem exists_refreshFreeTouchLists {β : Type} (value : MemoryMsg (ZMod p) → β)
    (time : MemoryMsg (ZMod p) → ℕ) (ts : List (List (Touch p)))
    (initF finF : MemLoc → Option (MemoryMsg (ZMod p)))
    (bump : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
    (hrefresh : ∀ b ∈ bump, RefreshElimination.IsRefresh value time b)
    (hbumpLoc : ∀ b ∈ bump, MemoryMsg.locOf
      (b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p)).1 = MemoryMsg.locOf b.2)
    (hbal : ∀ loc : MemLoc,
      optMS (initF loc) + (touchPairsAt ts loc).map Prod.snd +
          Multiset.filter (fun m => MemoryMsg.locOf m = loc)
            (↑(bump.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) =
        optMS (finF loc) + (touchPairsAt ts loc).map Prod.fst +
          Multiset.filter (fun m => MemoryMsg.locOf m = loc)
            (↑(bump.map Prod.fst) : Multiset (MemoryMsg (ZMod p)))) :
    ∃ (ts' : List (List (Touch p))) (finF' : MemLoc → Option (MemoryMsg (ZMod p))),
      List.Forall₂ (List.Forall₂ (TouchRewrite value time)) ts ts' ∧
      (∀ loc : MemLoc, optMS (initF loc) + (touchPairsAt ts' loc).map Prod.snd =
        optMS (finF' loc) + (touchPairsAt ts' loc).map Prod.fst) ∧
      (∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), finF loc = some m →
        ∃ m', finF' loc = some m' ∧ value m' = value m ∧ time m' ≤ time m) := by
  classical
  -- The refresh pairs at one location, and the two projections of that multiset.
  have hsnd : ∀ loc : MemLoc,
      (↑(bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
          MemoryMsg.locOf b.2 = loc) : Multiset (MemoryMsg (ZMod p) ×
          MemoryMsg (ZMod p))).map Prod.snd =
        Multiset.filter (fun m => MemoryMsg.locOf m = loc)
          (↑(bump.map Prod.snd) : Multiset (MemoryMsg (ZMod p))) := by
    intro loc
    rw [Multiset.map_coe, Multiset.filter_coe, map_filter_comm]
  have hfst : ∀ loc : MemLoc,
      (↑(bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
          MemoryMsg.locOf b.2 = loc) : Multiset (MemoryMsg (ZMod p) ×
          MemoryMsg (ZMod p))).map Prod.fst =
        Multiset.filter (fun m => MemoryMsg.locOf m = loc)
          (↑(bump.map Prod.fst) : Multiset (MemoryMsg (ZMod p))) := by
    intro loc
    rw [Multiset.map_coe, Multiset.filter_coe, map_filter_comm,
      show (bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
          MemoryMsg.locOf (Prod.fst b) = loc)
        = (bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
          MemoryMsg.locOf b.2 = loc) from
        List.filter_congr fun b hb => by rw [hbumpLoc b hb]]
  -- Run the generic elimination at every location.
  have perLoc : ∀ loc : MemLoc, ∃ (N' : Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
      (o : Option (MemoryMsg (ZMod p))),
      optMS (initF loc) + N'.map Prod.snd = optMS o + N'.map Prod.fst ∧
      Multiset.Rel (RefreshElimination.EdgeRewrite value time) (touchPairsAt ts loc) N' ∧
      ∀ m, finF loc = some m → ∃ m', o = some m' ∧ value m' = value m ∧ time m' ≤ time m := by
    intro loc
    obtain ⟨N', fin', bal', relN, relF⟩ :=
      RefreshElimination.eliminate value time (optMS (initF loc))
        (↑(bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
            MemoryMsg.locOf b.2 = loc) :
          Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))).card
        (↑(bump.filter fun b : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) =>
            MemoryMsg.locOf b.2 = loc) :
          Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
        (touchPairsAt ts loc) (optMS (finF loc)) rfl
        (fun b hb => hrefresh b (List.mem_of_mem_filter (Multiset.mem_coe.mp hb)))
        (by
          rw [Multiset.map_add, Multiset.map_add, ← add_assoc, ← add_assoc, hsnd loc, hfst loc]
          exact hbal loc)
    cases hfinF : finF loc with
    | none =>
        rw [hfinF, optMS_none] at relF
        refine ⟨N', none, ?_, relN, fun m hm => ?_⟩
        · rw [optMS_none, ← Multiset.rel_zero_left.mp relF]
          exact bal'
        · simp at hm
    | some m =>
        rw [hfinF, optMS_some] at relF
        obtain ⟨m', rfl, hm'⟩ := rel_singleton_left relF
        refine ⟨N', some m', by rw [optMS_some]; exact bal', relN, fun m₀ hm₀ => ?_⟩
        rw [Option.some.injEq] at hm₀
        subst hm₀
        exact ⟨m', rfl, hm'.1, hm'.2⟩
  choose N' finF' hbal' hrel hfin using perLoc
  -- Realize the per-location rewrites as per-row touch lists.
  obtain ⟨ts', hts', hsums⟩ :=
    exists_rewrittenTouchLists (R := RefreshElimination.EdgeRewrite value time)
      (fun _ _ h => h.1) ts N' hrel
  refine ⟨ts', finF', ?_, fun loc => ?_, hfin⟩
  · refine hts'.imp (fun l l' hl => hl.imp fun tc tc' h => ?_)
    exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [show touchPairsAt ts' loc = N' loc from hsums loc]
    exact hbal' loc

end SP1Clean.Soundness
