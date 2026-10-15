import SP1Clean.Soundness.CoreExecutionRow
import SP1Clean.Soundness.RefreshWiring

/-! # Memory alignment and refresh elimination independent of source policy

Per-row permutations preserve complete Memory messages while allowing the syscall carrier's
mixed read times. Refresh elimination consumes a proved frontier equation and strict refresh
chronology, retaining each row, read time, pushed record, and final value/location. Boot and local
assemblies derive these inputs from their own physical ledgers.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance coreRowBalanceField17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Per-row Memory equivalence, leaving read currency points and State normalization independent. -/
structure RowMemoryPermutation (left right : RowFacts p) : Prop where
  pushes : left.memPushes.Perm right.memPushes
  pulls : (left.memPulls.map Prod.fst).Perm (right.memPulls.map Prod.fst)

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Every row preserves its own Memory ledger, including syscall rows with mixed read times. -/
theorem RowMemoryPermutation.refl (row : RowFacts p) : RowMemoryPermutation row row :=
  ⟨List.Perm.refl _, List.Perm.refl _⟩

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Ordinary chip alignment supplies the weaker, currency-independent ledger interface. -/
theorem RowMemoryPermutation.of_alignsWith {left right : RowFacts p} (aligned : AlignsWith left right) :
    RowMemoryPermutation left right := ⟨aligned.pushes, aligned.pulls⟩

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem rowAggregates_of_permutation {left right : List (RowFacts p)}
    (aligned : List.Forall₂ RowMemoryPermutation left right) (loc : MemLoc) :
    pushesAt left loc = pushesAt right loc ∧ pullsAt left loc = pullsAt right loc := by
  induction aligned with
  | nil => exact ⟨rfl, rfl⟩
  | @cons left right ls rs aligned rest ih =>
    constructor
    · change (↑(rowPushesAt left loc) : Multiset _) + pushesAt ls loc =
        (↑(rowPushesAt right loc) : Multiset _) + pushesAt rs loc
      rw [ih.1]
      exact congrArg (· + pushesAt rs loc) (Multiset.coe_eq_coe.mpr (aligned.pushes.filter _))
    · change (↑(rowPullsAt left loc) : Multiset _) + pullsAt ls loc =
        (↑(rowPullsAt right loc) : Multiset _) + pullsAt rs loc
      rw [ih.2]
      exact congrArg (· + pullsAt rs loc) (Multiset.coe_eq_coe.mpr (aligned.pulls.filter _))

/-- Pair the aligned row's pulls with its pushes. `RowOKCore.touches` guarantees no truncation. -/
def rowTouches (row : RowFacts p) : List (Touch p) := row.memPulls.zip row.memPushes

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem rowTouches_projections (initialClock : ℕ) (row : RowFacts p)
    (ok : RowOKCore initialClock row) :
    row.memPushes = (rowTouches row).map Prod.snd ∧
      row.memPulls = (rowTouches row).map Prod.fst ∧
      ∀ touch ∈ rowTouches row, MemoryMsg.locOf touch.2 = MemoryMsg.locOf touch.1.1 := by
  have lengths := (List.forall₂_iff_zip.mp ok.touches).1
  exact ⟨(List.map_snd_zip lengths.symm.le).symm, (List.map_fst_zip lengths.le).symm,
    fun _ member => ((List.forall₂_iff_zip.mp ok.touches).2 member).loc_eq⟩

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A balanced mixed-row ledger with ordered value-preserving refreshes has a refresh-free
representation. No enclosing ensemble or boot-state policy occurs in this statement. -/
theorem refresh_free_of_balance (rows : List (RowFacts p))
    (initialFrontier finalFrontier : MemLoc → Option (MemoryMsg (ZMod p)))
    (refreshes : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
    (initialClock : ℕ) (rowOK : ∀ row ∈ rows, RowOKCore initialClock row)
    (balance : ∀ loc, optMS (initialFrontier loc) + pushesAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(refreshes.map Prod.snd) : Multiset _) =
      optMS (finalFrontier loc) + pullsAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(refreshes.map Prod.fst) : Multiset _))
    (preserve : ∀ pair ∈ refreshes,
      (MemoryMsg.locOf pair.1, pair.1.value) = (MemoryMsg.locOf pair.2, pair.2.value))
    (refreshOrder : ∀ pair ∈ refreshes, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2) :
    ∃ (touches : List (List (Touch p))) (final : MemLoc → Option (MemoryMsg (ZMod p))),
      List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches ∧
      (∀ loc, optMS (initialFrontier loc) +
          pushesAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc =
        optMS (final loc) + pullsAt ((rows.zip touches).map (fun pair => alignedOf pair.1 pair.2)) loc) ∧
      (rows.zip touches).map Prod.fst = rows ∧
      (∀ loc message, finalFrontier loc = some message →
        ∃ earlier, final loc = some earlier ∧ MemoryMsg.locOf earlier = MemoryMsg.locOf message ∧
          earlier.value = message.value ∧ MemoryMsg.timeNat earlier ≤ MemoryMsg.timeNat message) := by
  have touchFacts := fun row member => rowTouches_projections initialClock row (rowOK row member)
  have pushes := fun loc => pushesAt_of_touchLists rows id rowTouches
    (fun row member => (touchFacts row member).1) loc
  have pulls := fun loc => pullsAt_of_touchLists rows id rowTouches
    (fun row member => (touchFacts row member).2.1) (fun row member => (touchFacts row member).2.2) loc
  simp only [List.map_id] at pushes pulls
  have touchBalance := balance
  simp only [pushes, pulls] at touchBalance
  have refresh : ∀ pair ∈ refreshes,
      RefreshElimination.IsRefresh (fun message : MemoryMsg (ZMod p) => (MemoryMsg.locOf message, message.value))
        MemoryMsg.timeNat pair := fun pair member =>
    ⟨preserve pair member, refreshOrder pair member⟩
  obtain ⟨touches, final, rewritten, balance, finalRewrite⟩ := exists_refreshFreeTouchLists
    (fun message : MemoryMsg (ZMod p) => (MemoryMsg.locOf message, message.value)) MemoryMsg.timeNat
    (rows.map rowTouches) initialFrontier finalFrontier
    (refreshes) refresh
    (fun pair member => congrArg Prod.fst (preserve pair member)) touchBalance
  have pullRewrites : List.Forall₂ (List.Forall₂ PullRewrite) (rows.map rowTouches) touches :=
    rewritten.imp (fun _ _ h => h.imp (fun _ _ h => pullRewrite_of_touchRewrite h))
  have lengths : rows.length = touches.length := by simpa using rewritten.length_eq
  have first : (rows.zip touches).map Prod.fst = rows := List.map_fst_zip lengths.le
  have second : (rows.zip touches).map Prod.snd = touches := List.map_snd_zip lengths.symm.le
  have locAgree : ∀ ts ∈ touches, ∀ touch ∈ ts, MemoryMsg.locOf touch.2 = MemoryMsg.locOf touch.1.1 := by
    intro ts member touch touchMem
    obtain ⟨original, originalMem, related⟩ := forall₂_exists_left pullRewrites ts member
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp originalMem
    obtain ⟨old, oldMem, rewrite⟩ := forall₂_exists_left related touch touchMem
    rw [rewrite.2.1, rewrite.2.2.1]
    exact (touchFacts row rowMem).2.2 old oldMem
  refine ⟨touches, final, pullRewrites, ?_, first, ?_⟩
  · intro loc
    rw [pushesAt_of_touchLists (rows.zip touches) (fun pair => alignedOf pair.1 pair.2) Prod.snd
        (fun _ _ => rfl),
      pullsAt_of_touchLists (rows.zip touches) (fun pair => alignedOf pair.1 pair.2) Prod.snd
        (fun _ _ => rfl) (fun pair member => locAgree pair.2 (by
          rw [← second]; exact List.mem_map_of_mem member)), second]
    exact balance loc
  · intro loc message present
    obtain ⟨earlier, present, same, time⟩ := finalRewrite loc message present
    exact ⟨earlier, present, congrArg Prod.fst same, congrArg Prod.snd same, time⟩


end SP1Clean.Soundness.NativeCore
