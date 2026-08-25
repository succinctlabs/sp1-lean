import SP1Clean.Soundness.TimedGrounding

/-! # The aligned `RowFacts` carrier (Phase B1)

The timed grounding walk consumes `RowOK` — a *positional* `Forall₂ TouchOK memPulls memPushes` — so
it must be fed a carrier whose pulls are paired, in order, with the same-location pushes at those
pushes' micro-times.  `DecodedInstructionRow.ordinaryRowFacts` is not that carrier: its pulls are in
emitted order, all tagged with the window-start read time.  `Soundness/TimedGrounding.lean`'s
`AlignsWith` + the three carrier transports reconcile the two; this module supplies the *constructor*
those transports and the walk consume.

`alignedOf r_ord touches` rebuilds the ordinary row's pull/push lists from a `touches` list whose
`i`-th entry is `(aligned-pull-with-time, the produced push it pairs with)`.  A per-chip (or
per-reader-family) instance supplies `touches` — the produced list in order, each pull the
same-location prior at the push's micro-time — and the per-touch `TouchOK`; `AlignsWith` and `RowOK`
then follow generically here.

The constructor is location-generic; register-only callers retain a compatibility wrapper while
load/store rows use the RAM read window directly. -/

open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

namespace SP1Clean.Soundness.TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The aligned carrier: same state edge and fetch as the ordinary row; pull/push lists read off the
touch list (`memPulls` = the aligned priors with their read micro-times, `memPushes` = the produced
pushes, in `touches` order). -/
def alignedOf (r_ord : RowFacts p) (touches : List (Touch p)) : RowFacts p :=
  { statePull := r_ord.statePull
    statePush := r_ord.statePush
    fetch := r_ord.fetch
    memPulls := touches.map Prod.fst
    memPushes := touches.map Prod.snd }

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `(L.map fst).zip (L.map snd) = L` for a list of pairs. -/
private lemma zip_map_fst_snd (L : List (Touch p)) :
    (L.map Prod.fst).zip (L.map Prod.snd) = L := by
  simp [List.zip_map']

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `Forall₂ (TouchOK t)` over the split lists reduces to a per-entry membership fact. -/
private lemma forall₂_touchOK_map {t : ℕ} (L : List (Touch p))
    (h : ∀ tc ∈ L, TouchOK t tc.1 tc.2) :
    List.Forall₂ (TouchOK t) (L.map Prod.fst) (L.map Prod.snd) :=
  List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr h))

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The aligned carrier's per-key touches are exactly the touch list filtered at the key. -/
theorem rowTouchesAt_alignedOf (r_ord : RowFacts p) (touches : List (Touch p)) (loc : MemLoc) :
    rowTouchesAt (alignedOf r_ord touches) loc =
      touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc) := by
  simp only [rowTouchesAt, alignedOf, zip_map_fst_snd]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Generic `AlignsWith` for the aligned constructor.**  The instance supplies the two message
permutations, the ordinary read-time convention, and a same-message aligned pull inside the
location-dependent pre-effect window. -/
theorem alignsWith_alignedOf_general (r_ord : RowFacts p) (touches : List (Touch p))
    (hpush : (touches.map Prod.snd).Perm r_ord.memPushes)
    (hpull : ((touches.map Prod.fst).map Prod.fst).Perm (r_ord.memPulls.map Prod.fst))
    (hordTime : ∀ mp ∈ r_ord.memPulls, mp.2 = StateMsg.timeNat r_ord.statePull)
    (hmatch : ∀ mp ∈ r_ord.memPulls, ∃ tc ∈ touches, tc.1.1 = mp.1 ∧
      StateMsg.timeNat r_ord.statePull ≤ tc.1.2 ∧
      tc.1.2 ≤ StateMsg.timeNat r_ord.statePull + readWindow (MemoryMsg.locOf mp.1)) :
    AlignsWith (alignedOf r_ord touches) r_ord where
  statePull := rfl
  statePush := rfl
  pushes := hpush
  pulls := hpull
  ordTime := hordTime
  match_ := by
    intro mp hmp
    obtain ⟨tc, htc, hmsg, hlo, hhi⟩ := hmatch mp hmp
    exact ⟨tc.1, List.mem_map_of_mem htc, hmsg, hlo, hhi⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Register-only compatibility wrapper for the existing grounding families. -/
theorem alignsWith_alignedOf (r_ord : RowFacts p) (touches : List (Touch p))
    (hpush : (touches.map Prod.snd).Perm r_ord.memPushes)
    (hpull : ((touches.map Prod.fst).map Prod.fst).Perm (r_ord.memPulls.map Prod.fst))
    (hreg : ∀ mp ∈ r_ord.memPulls, ∃ i : BitVec 5, MemoryMsg.locOf mp.1 = MemLoc.reg i)
    (hordTime : ∀ mp ∈ r_ord.memPulls, mp.2 = StateMsg.timeNat r_ord.statePull)
    (hmatch : ∀ mp ∈ r_ord.memPulls, ∃ tc ∈ touches, tc.1.1 = mp.1 ∧
      StateMsg.timeNat r_ord.statePull ≤ tc.1.2 ∧
      tc.1.2 < StateMsg.timeNat r_ord.statePull + 4) :
    AlignsWith (alignedOf r_ord touches) r_ord := by
  refine alignsWith_alignedOf_general r_ord touches hpush hpull hordTime ?_
  intro mp hmp
  obtain ⟨i, hloc⟩ := hreg mp hmp
  obtain ⟨tc, htc, hmsg, hlo, hhi⟩ := hmatch mp hmp
  exact ⟨tc, htc, hmsg, hlo, by rw [hloc, readWindow_reg]; omega⟩

/-! ## Realizing per-location pull rewrites in per-row touch lists (W3)

The refresh elimination rewrites, per location, the multiset of a batch's `(pull, push)` message
pairs — pushes untouched, pulls replaced by value-equal earlier records.  The walk, however,
consumes per-row `RowFacts`, so the rewritten multisets must be *realized* as per-row touch lists.
The three lemmas below do exactly that surgery, generically over any pair relation `R` that
preserves the push (`hsnd`): first listify a `Multiset.Rel` against a coerced list, then merge the
per-location rewritten lists back into one positional touch list (read times and pushes kept), and
finally distribute a whole batch's per-location rewrites row by row. -/

section Realization

omit [Fact p.Prime] [Fact (2 ^ 17 < p)]

variable {R : MemoryMsg (ZMod p) × MemoryMsg (ZMod p) →
  MemoryMsg (ZMod p) × MemoryMsg (ZMod p) → Prop}

/-- A `Multiset.Rel` whose left side is a coerced list is realized by an order-preserving
`Forall₂`-related list. -/
private lemma forall₂_of_rel_coe {α β : Type} {r : α → β → Prop} :
    ∀ (l : List α) (t : Multiset β), Multiset.Rel r (↑l) t →
      ∃ l' : List β, t = ↑l' ∧ List.Forall₂ r l l'
  | [], t, h => by
      rw [Multiset.coe_nil] at h
      exact ⟨[], Multiset.rel_zero_left.mp h, List.Forall₂.nil⟩
  | a :: l, t, h => by
      rw [← Multiset.cons_coe] at h
      obtain ⟨b, u, hab, hrest, rfl⟩ := Multiset.rel_cons_left.mp h
      obtain ⟨l', rfl, hf⟩ := forall₂_of_rel_coe l u hrest
      exact ⟨b :: l', (Multiset.cons_coe b l').symm, List.Forall₂.cons hab hf⟩

/-- A push-preserving `Multiset.Rel` leaves the pushed-record multiset unchanged. -/
lemma rel_map_snd_eq (hsnd : ∀ a b, R a b → b.2 = a.2) :
    ∀ {N N' : Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))}, Multiset.Rel R N N' →
      N.map Prod.snd = N'.map Prod.snd := by
  intro N N' h
  induction h with
  | zero => rfl
  | @cons a b as bs hab _ ih => simp only [Multiset.map_cons, ih, hsnd _ _ hab]

/-- A `Multiset.Rel` against a singleton is a related singleton. -/
lemma rel_singleton_left {α β : Type} {r : α → β → Prop} {a : α} {t : Multiset β}
    (h : Multiset.Rel r {a} t) : ∃ b, t = {b} ∧ r a b := by
  rw [show ({a} : Multiset α) = a ::ₘ 0 from rfl] at h
  obtain ⟨b, u, hab, hrest, rfl⟩ := Multiset.rel_cons_left.mp h
  rw [Multiset.rel_zero_left.mp hrest]
  exact ⟨b, rfl, hab⟩

/-- Right-directional pairing of a `Forall₂`. -/
lemma forall₂_exists_right {α β : Type} {r : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, r a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro a ha; cases ha
  | cons hR _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, List.mem_cons_self, hR⟩
      · obtain ⟨b, hb, hab⟩ := ih a ha
        exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- Left-directional pairing of a `Forall₂`. -/
lemma forall₂_exists_left {α β : Type} {r : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, r a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; cases hb
  | cons hR _ ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, hR⟩
      · obtain ⟨a, ha, hab⟩ := ih b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- Right-directional pairing of a `Forall₂`, realized inside the positional zip. -/
lemma forall₂_mem_zip_right {α β : Type} {r : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ →
      ∀ a ∈ l₁, ∃ b, (a, b) ∈ l₁.zip l₂ ∧ r a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro a ha; cases ha
  | @cons a' b' l₁ l₂ hR _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨b', by rw [List.zip_cons_cons]; exact List.mem_cons_self, hR⟩
      · obtain ⟨b, hb, hab⟩ := ih a ha
        exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb, hab⟩

/-- Mapping a multiset function over a list sum of multisets. -/
lemma map_listSum {α β : Type} (f : α → β) :
    ∀ l : List (Multiset α), (l.sum).map f = (l.map (Multiset.map f)).sum
  | [] => by simp
  | s :: l => by
      rw [List.sum_cons, Multiset.map_add, map_listSum f l, List.map_cons, List.sum_cons]

/-- Pointwise second components of a snd-preserving `Forall₂` produce equal `map Prod.snd`
images. -/
lemma map_snd_eq_of_forall₂ {α β : Type} {r : α × β → α × β → Prop}
    (hsnd : ∀ a b, r a b → b.2 = a.2) :
    ∀ {l l' : List (α × β)}, List.Forall₂ r l l' → l'.map Prod.snd = l.map Prod.snd := by
  intro l l' h
  induction h with
  | nil => rfl
  | @cons a b _ _ hR _ ih => rw [List.map_cons, List.map_cons, ih, hsnd _ _ hR]

/-- Filters of `Forall₂`-related lists along a relation-invariant predicate stay related. -/
lemma forall₂_filter_congr {α : Type} {r : α → α → Prop} {P : α → Prop} [DecidablePred P]
    (hP : ∀ a b, r a b → (P a ↔ P b)) :
    ∀ {l l' : List α}, List.Forall₂ r l l' →
      List.Forall₂ r (l.filter fun a => P a) (l'.filter fun a => P a) := by
  intro l l' h
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b _ _ hR _ ih =>
      by_cases hpa : P a
      · rw [List.filter_cons_of_pos (by simpa using hpa),
          List.filter_cons_of_pos (by simpa using (hP a b hR).mp hpa)]
        exact List.Forall₂.cons hR ih
      · rw [List.filter_cons_of_neg (by simpa using hpa),
          List.filter_cons_of_neg (by simpa using fun hb => hpa ((hP a b hR).mpr hb))]
        exact ih

/-- A push-time chain transfers across a snd-preserving `Forall₂`. -/
lemma isChain_snd_of_forall₂ {α : Type} {time : α → ℕ} {r : α × α → α × α → Prop}
    (hsnd : ∀ a b, r a b → b.2 = a.2) :
    ∀ {l l' : List (α × α)}, List.Forall₂ r l l' →
      List.IsChain (fun a b : α × α => time a.2 < time b.2) l →
      List.IsChain (fun a b : α × α => time a.2 < time b.2) l' := by
  intro l l' h
  induction h with
  | nil => intro _; exact List.isChain_nil
  | @cons a b l l' hR hrest ih =>
      intro hchain
      cases hrest with
      | nil => exact List.isChain_singleton _
      | @cons a₂ b₂ l₂ l₂' hR₂ hrest₂ =>
          rw [List.isChain_cons_cons] at hchain ⊢
          refine ⟨?_, ih hchain.2⟩
          rw [hsnd _ _ hR, hsnd _ _ hR₂]
          exact hchain.1

/-- **The filter-partition merge.**  Given per-location `Forall₂`-rewrites of one touch list's
per-location message pairs, a single rewritten touch list realizes all of them simultaneously:
read times and pushes are kept positionally, and each location's filtered pair image is exactly
the given target list. -/
private lemma exists_touchList_of_filter_rewrites (hsnd : ∀ a b, R a b → b.2 = a.2) :
    ∀ (l : List (Touch p)) (w : MemLoc → List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))),
      (∀ loc, List.Forall₂ R
        ((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)) (w loc)) →
      ∃ l' : List (Touch p),
        List.Forall₂ (fun tc tc' : Touch p => tc'.1.2 = tc.1.2 ∧ tc'.2 = tc.2 ∧
          R (tc.1.1, tc.2) (tc'.1.1, tc'.2)) l l' ∧
        ∀ loc, ((l'.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2))
          = w loc
  | [], w, hw => by
      refine ⟨[], List.Forall₂.nil, fun loc => ?_⟩
      have h := hw loc
      rw [List.filter_nil, List.map_nil] at h ⊢
      exact (List.forall₂_nil_left_iff.mp h).symm
  | tc :: rest, w, hw => by
      classical
      have hfilterhead : ((tc :: rest).filter fun pq => MemoryMsg.locOf pq.2 =
            MemoryMsg.locOf tc.2)
          = tc :: (rest.filter fun pq => MemoryMsg.locOf pq.2 = MemoryMsg.locOf tc.2) :=
        List.filter_cons_of_pos (by simp)
      have hwhead := hw (MemoryMsg.locOf tc.2)
      rw [hfilterhead, List.map_cons] at hwhead
      obtain ⟨b, wrest, hb, hrest, hweq⟩ := List.forall₂_cons_left_iff.mp hwhead
      have hb2 : b.2 = tc.2 := hsnd _ _ hb
      obtain ⟨rest', hrest', hfilters⟩ := exists_touchList_of_filter_rewrites hsnd rest
        (Function.update w (MemoryMsg.locOf tc.2) wrest) (by
          intro loc
          by_cases hcase : loc = MemoryMsg.locOf tc.2
          · subst hcase
            rw [Function.update_self]
            exact hrest
          · rw [Function.update_of_ne hcase]
            have hfilter : ((tc :: rest).filter fun pq => MemoryMsg.locOf pq.2 = loc)
                = rest.filter fun pq => MemoryMsg.locOf pq.2 = loc :=
              List.filter_cons_of_neg (by simpa using fun h => hcase h.symm)
            have h := hw loc
            rwa [hfilter] at h)
      refine ⟨((b.1, tc.1.2), tc.2) :: rest', ?_, ?_⟩
      · refine List.Forall₂.cons ⟨rfl, rfl, ?_⟩ hrest'
        show R (tc.1.1, tc.2) (b.1, tc.2)
        rw [show ((b.1, tc.2) : MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) = b from by
          rw [← hb2]]
        exact hb
      · intro loc
        by_cases hcase : loc = MemoryMsg.locOf tc.2
        · subst hcase
          rw [show ((((b.1, tc.1.2), tc.2) : Touch p) :: rest').filter
                (fun pq => MemoryMsg.locOf pq.2 = MemoryMsg.locOf tc.2)
              = ((b.1, tc.1.2), tc.2) ::
                (rest'.filter fun pq => MemoryMsg.locOf pq.2 = MemoryMsg.locOf tc.2) from
            List.filter_cons_of_pos (by simp), List.map_cons, hfilters,
            Function.update_self, hweq]
          rw [show ((b.1, tc.2) : MemoryMsg (ZMod p) × MemoryMsg (ZMod p)) = b from by
            rw [← hb2]]
        · rw [show ((((b.1, tc.1.2), tc.2) : Touch p) :: rest').filter
                (fun pq => MemoryMsg.locOf pq.2 = loc)
              = rest'.filter fun pq => MemoryMsg.locOf pq.2 = loc from
            List.filter_cons_of_neg (by simpa using fun h => hcase h.symm), hfilters,
            Function.update_of_ne hcase]

/-- **The batch realization.**  Distribute per-location multiset rewrites of a batch's touch-pair
sums into per-row rewritten touch lists: pushes and read times survive pointwise (`Forall₂`), and
the per-location pair sums realize exactly the given targets. -/
lemma exists_rewrittenTouchLists (hsnd : ∀ a b, R a b → b.2 = a.2) :
    ∀ (ts : List (List (Touch p)))
      (N' : MemLoc → Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))),
      (∀ loc, Multiset.Rel R
        ((ts.map fun l =>
          (↑((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)) :
            Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))).sum)
        (N' loc)) →
      ∃ ts' : List (List (Touch p)),
        List.Forall₂ (List.Forall₂ (fun tc tc' : Touch p => tc'.1.2 = tc.1.2 ∧ tc'.2 = tc.2 ∧
          R (tc.1.1, tc.2) (tc'.1.1, tc'.2))) ts ts' ∧
        ∀ loc, ((ts'.map fun l =>
          (↑((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)) :
            Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))).sum) = N' loc
  | [], N', hrel => by
      refine ⟨[], List.Forall₂.nil, fun loc => ?_⟩
      have h := hrel loc
      rw [List.map_nil, List.sum_nil] at h ⊢
      exact (Multiset.rel_zero_left.mp h).symm
  | l :: ts, N', hrel => by
      classical
      have hsplit : ∀ loc, ∃ A B,
          Multiset.Rel R
            (↑((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)))
            A ∧
          Multiset.Rel R
            ((ts.map fun l =>
              (↑((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc =>
                (tc.1.1, tc.2)) :
                Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))).sum)
            B ∧ N' loc = A + B := by
        intro loc
        have h := hrel loc
        rw [List.map_cons, List.sum_cons] at h
        obtain ⟨A, B, hA, hB, hAB⟩ := Multiset.rel_add_left.mp h
        exact ⟨A, B, hA, hB, hAB⟩
      choose A B hA hB hAB using hsplit
      have hlist : ∀ loc, ∃ wl : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)),
          A loc = ↑wl ∧ List.Forall₂ R
          ((l.filter fun pq => MemoryMsg.locOf pq.2 = loc).map fun tc => (tc.1.1, tc.2)) wl :=
        fun loc => forall₂_of_rel_coe _ (A loc) (hA loc)
      choose wl hwlA hwl using hlist
      obtain ⟨l', hl', hl'filters⟩ := exists_touchList_of_filter_rewrites hsnd l wl hwl
      obtain ⟨ts', hts', hts'sums⟩ := exists_rewrittenTouchLists hsnd ts B hB
      refine ⟨l' :: ts', List.Forall₂.cons hl' hts', fun loc => ?_⟩
      rw [List.map_cons, List.sum_cons, hl'filters loc, hts'sums loc, ← hwlA loc]
      exact (hAB loc).symm

end Realization

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Generic `RowOK` for the aligned constructor.**  From the per-touch `TouchOK`, the `+8` clock
step, the mod-8 window alignment, per-key push-time strict monotonicity, the per-push `ClkBound`, and
the currency-free **conditional** `slot` fact (`hslot`: given the pulled record's `ClkBound`, the
`prev_clk < access_clk` order — the 1f break; the walk discharges the antecedent from the balance). -/
theorem rowOK_alignedOf (initialClock : ℕ) (r_ord : RowFacts p) (touches : List (Touch p))
    (htime8 : StateMsg.timeNat r_ord.statePush = StateMsg.timeNat r_ord.statePull + 8)
    (halign8 : StateMsg.timeNat r_ord.statePull % 8 = initialClock % 8)
    (htouch : ∀ tc ∈ touches, TouchOK (StateMsg.timeNat r_ord.statePull) tc.1 tc.2)
    (hchain : ∀ loc : MemLoc, List.IsChain
      (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc)))
    (hpushClk : ∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound tc.2)
    (hslot : ∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
      MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2) :
    RowOK initialClock (alignedOf r_ord touches) where
  time8 := htime8
  align8 := halign8
  touches := forall₂_touchOK_map touches htouch
  chain_mono := by simpa only [rowTouchesAt_alignedOf] using hchain
  pushClkBound := by
    intro m hm; obtain ⟨tc, htc, rfl⟩ := List.mem_map.mp hm; exact hpushClk tc htc
  slotOfClkBound := by
    intro pq hpq hclk
    simp only [alignedOf] at hpq
    rw [zip_map_fst_snd touches] at hpq
    exact hslot pq hpq hclk

end SP1Clean.Soundness.TimedGrounding
