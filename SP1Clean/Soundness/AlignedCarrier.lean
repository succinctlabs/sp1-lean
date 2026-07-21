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

Register-axis only; the RAM analogue (loads/stores) is Phase R. -/

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
  rw [List.zip_map']
  simp

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- `Forall₂ (TouchOK t)` over the split lists reduces to a per-entry membership fact. -/
private lemma forall₂_touchOK_map {t : ℕ} (L : List (Touch p))
    (h : ∀ tc ∈ L, TouchOK t tc.1 tc.2) :
    List.Forall₂ (TouchOK t) (L.map Prod.fst) (L.map Prod.snd) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons tc rest ih =>
    exact List.Forall₂.cons (h tc List.mem_cons_self)
      (ih (fun tc' htc' => h tc' (List.mem_cons_of_mem tc htc')))

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The aligned carrier's per-key touches are exactly the touch list filtered at the key. -/
theorem rowTouchesAt_alignedOf (r_ord : RowFacts p) (touches : List (Touch p)) (loc : MemLoc) :
    rowTouchesAt (alignedOf r_ord touches) loc =
      touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc) := by
  unfold rowTouchesAt alignedOf
  dsimp only
  rw [zip_map_fst_snd]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Generic `AlignsWith` for the aligned constructor.**  The instance supplies: the aligned pushes
are the ordinary produced list; every ordinary pull is register-located and read at the window start;
and every ordinary pull's message appears as some touch's aligned pull inside the pre-write epoch. -/
theorem alignsWith_alignedOf (r_ord : RowFacts p) (touches : List (Touch p))
    (hpush : (touches.map Prod.snd).Perm r_ord.memPushes)
    (hpull : ((touches.map Prod.fst).map Prod.fst).Perm (r_ord.memPulls.map Prod.fst))
    (hreg : ∀ mp ∈ r_ord.memPulls, ∃ i : BitVec 5, MemoryMsg.locOf mp.1 = MemLoc.reg i)
    (hordTime : ∀ mp ∈ r_ord.memPulls, mp.2 = StateMsg.timeNat r_ord.statePull)
    (hmatch : ∀ mp ∈ r_ord.memPulls, ∃ tc ∈ touches, tc.1.1 = mp.1 ∧
      StateMsg.timeNat r_ord.statePull ≤ tc.1.2 ∧
      tc.1.2 < StateMsg.timeNat r_ord.statePull + 4) :
    AlignsWith (alignedOf r_ord touches) r_ord where
  statePull := rfl
  statePush := rfl
  pushes := hpush
  pulls := hpull
  reg := hreg
  ordTime := hordTime
  match_ := by
    intro mp hmp
    obtain ⟨tc, htc, hmsg, hlo, hhi⟩ := hmatch mp hmp
    exact ⟨tc.1, List.mem_map_of_mem htc, hmsg, hlo, hhi⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Generic `RowOK` for the aligned constructor.**  From the per-touch `TouchOK`, the `+8` clock
step, the mod-8 window alignment, and per-key push-time strict monotonicity. -/
theorem rowOK_alignedOf (initialClock : ℕ) (r_ord : RowFacts p) (touches : List (Touch p))
    (htime8 : StateMsg.timeNat r_ord.statePush = StateMsg.timeNat r_ord.statePull + 8)
    (halign8 : StateMsg.timeNat r_ord.statePull % 8 = initialClock % 8)
    (htouch : ∀ tc ∈ touches, TouchOK (StateMsg.timeNat r_ord.statePull) tc.1 tc.2)
    (hchain : ∀ loc : MemLoc, List.IsChain
      (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
      (touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc)))
    (hpushClk : ∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) :
    RowOK initialClock (alignedOf r_ord touches) where
  time8 := htime8
  align8 := halign8
  touches := forall₂_touchOK_map touches htouch
  chain_mono := by
    intro loc
    rw [rowTouchesAt_alignedOf]
    exact hchain loc
  pushClkBound := by
    intro m hm
    simp only [alignedOf, List.mem_map] at hm
    obtain ⟨tc, htc, rfl⟩ := hm
    exact hpushClk tc htc

end SP1Clean.Soundness.TimedGrounding
