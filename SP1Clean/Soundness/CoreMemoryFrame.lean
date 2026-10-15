import SP1Clean.Soundness.CoreRowBalance
import SP1Clean.Soundness.CoreRowTransport

/-! # Locations absent from a complete Memory frontier

Paired accesses conserve the number of records at each location. If the final frontier has no
record, neither can the source. Strict access/refresh clocks then exclude a closed cycle of
interior records. Thus every actual push belongs to the final frontier's support, independently
of values or successful execution. This uses the original ledger, before refresh elimination.
-/

namespace SP1Clean.Soundness.NativeCore

open Channels Semantics TimedGrounding

private theorem edges_nil_of_no_final {α : Type} (rank : α → ℕ)
    (initial : Multiset α) (edges : Multiset (α × α))
    (balance : initial + edges.map Prod.snd = edges.map Prod.fst)
    (increases : ∀ pair ∈ edges, rank pair.1 < rank pair.2) : edges = 0 := by
  classical
  have count := congrArg Multiset.card balance
  simp only [Multiset.card_add, Multiset.card_map] at count
  have empty : initial = 0 := Multiset.card_eq_zero.mp (by omega)
  rw [empty, zero_add] at balance
  by_contra nonempty
  obtain ⟨pair, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
  apply nonempty
  exact RankedGrounding.eq_zero_of_endpointBalanced_self edges id rank increases
    (congrArg (Multiset.cons pair.1) balance)

variable {p : ℕ}

/-- An absent physical final record excludes every execution push at that location, even with
refresh rows present. All clock conditions concern real records and their original priors. -/
theorem pushesAt_zero_of_final_none (rows : List (RowFacts p))
    (initial final : MemLoc → Option (MemoryMsg (ZMod p)))
    (refreshes : List (MemoryMsg (ZMod p) × MemoryMsg (ZMod p)))
    (clock : ℕ) (ok : ∀ row ∈ rows, RowOKCore clock row)
    (prior : ∀ row ∈ rows, ∀ pull ∈ row.memPulls, MemoryMsg.ClkBound pull.1)
    (balance : ∀ loc, optMS (initial loc) + pushesAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(refreshes.map Prod.snd) : Multiset _) =
      optMS (final loc) + pullsAt rows loc +
        Multiset.filter (fun message => MemoryMsg.locOf message = loc)
          (↑(refreshes.map Prod.fst) : Multiset _))
    (preserve : ∀ pair ∈ refreshes, MemoryMsg.locOf pair.1 = MemoryMsg.locOf pair.2)
    (advance : ∀ pair ∈ refreshes, MemoryMsg.timeNat pair.1 < MemoryMsg.timeNat pair.2)
    (loc : MemLoc) (absent : final loc = none) : pushesAt rows loc = 0 := by
  classical
  have projections := fun row member => rowTouches_projections clock row (ok row member)
  have pushes := pushesAt_of_touchLists rows id rowTouches
    (fun row member => (projections row member).1) loc
  have pulls := pullsAt_of_touchLists rows id rowTouches
    (fun row member => (projections row member).2.1)
    (fun row member => (projections row member).2.2) loc
  simp only [List.map_id] at pushes pulls
  let refreshed := (↑refreshes : Multiset (MemoryMsg (ZMod p) × MemoryMsg (ZMod p))).filter
    (fun pair => MemoryMsg.locOf pair.2 = loc)
  have refreshPush : Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(refreshes.map Prod.snd) : Multiset _) = refreshed.map Prod.snd := by
    rw [← Multiset.map_coe, Multiset.filter_map]
    rfl
  have refreshPull : Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(refreshes.map Prod.fst) : Multiset _) = refreshed.map Prod.fst := by
    rw [← Multiset.map_coe, Multiset.filter_map]
    apply congrArg (Multiset.map Prod.fst)
    apply Multiset.filter_congr
    intro pair member
    dsimp only [Function.comp_apply]
    rw [preserve pair (Multiset.mem_coe.mp member)]
  have ledger := balance loc
  rw [absent, show optMS (none : Option (MemoryMsg (ZMod p))) = 0 from rfl,
    zero_add, pushes, pulls, refreshPush, refreshPull, add_assoc,
    ← Multiset.map_add, ← Multiset.map_add] at ledger
  have empty := edges_nil_of_no_final MemoryMsg.timeNat _ _ ledger (by
    intro pair member
    rcases Multiset.mem_add.mp member with touch | refresh
    · rw [touchPairsAt, mem_listSum_map] at touch
      obtain ⟨touches, touchesMem, pairMem⟩ := touch
      obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp touchesMem
      have pairMem := Multiset.mem_coe.mp pairMem
      obtain ⟨access, accessMem, rfl⟩ := List.mem_map.mp pairMem
      have zipped := (List.mem_filter.mp accessMem).1
      exact (ok row rowMem).slotOfClkBound access zipped
        (prior row rowMem access.1 (List.of_mem_zip zipped).1)
    · exact advance pair (Multiset.mem_coe.mp (Multiset.mem_filter.mp refresh).1))
  have noTouches := (add_eq_zero.mp empty).1
  rw [pushes, noTouches, Multiset.map_zero]

private theorem preserve_along_walk {α V : Type} (edge : α → V × V) (P : V → Prop)
    {rows : List α} {initial final : V} (walk : Walk.IsWalk edge initial final rows)
    (preserves : ∀ row ∈ rows, P (edge row).1 → P (edge row).2) (start : P initial) : P final := by
  induction rows generalizing initial with
  | nil => exact walk ▸ start
  | cons row rest ih =>
      obtain ⟨same, tail⟩ := walk
      exact ih tail (fun row member => preserves row (List.mem_cons_of_mem _ member))
        (preserves row List.mem_cons_self (same ▸ start))

variable [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance memoryFrameLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Transport a source value across the same carrier when its original event inventory never
pushes this location. No new trajectory, replay or access-order representation is introduced. -/
theorem ExecutionCarrier.frame_of_no_push
    {facts : ExecutionRow p → RowFacts p} {events : List (ExecutionRow p)}
    {incoming outgoing : StateMsg (ZMod p)}
    {initialFrontier physicalFinal : MemLoc → Option (MemoryMsg (ZMod p))}
    (carrier : ExecutionCarrier facts events incoming outgoing initialFrontier physicalFinal)
    {program : Target.GuestProgram} {trajectory : Trajectory} {initial : SailState}
    (current : ∀ event ∈ events,
      LocalStateTruthG program trajectory carrier.timeline (facts event).statePull ∧
      ∀ pull ∈ (facts event).memPulls, MemoryMsg.isU64 pull.1 ∧ MemoryMsg.ClkBound pull.1 ∧
        LocalValueAtG trajectory initial carrier.timeline (MemoryMsg.locOf pull.1) pull.2 pull.1.value)
    (frames : ∀ event ∈ events, FrameFactG program trajectory initial carrier.timeline (facts event))
    (loc : MemLoc) (value : Word (ZMod p))
    (untouched : ∀ event ∈ events, ∀ message ∈ (facts event).memPushes, MemoryMsg.locOf message ≠ loc)
    (start : LocalValueAtG trajectory initial carrier.timeline loc (StateMsg.timeNat incoming) value) :
    LocalValueAtG trajectory initial carrier.timeline loc (StateMsg.timeNat outgoing) value := by
  apply preserve_along_walk (fun row : RowFacts p => (row.statePull, row.statePush))
    (fun state => LocalValueAtG trajectory initial carrier.timeline loc (StateMsg.timeNat state) value)
    carrier.stateWalk ?_ start
  intro row member before
  obtain ⟨original, originalMem, aligned⟩ := forall₂_exists_right carrier.aligned row member
  obtain ⟨event, eventMem, rfl⟩ := List.mem_map.mp originalMem
  have active := carrier.exhaustive.mem_iff.mp eventMem
  rw [aligned.pullTime] at before
  rw [aligned.pushTime]
  exact frames event active (current event active).1 (current event active).2 loc value
    (fun message member same => (untouched event active message member same).elim) before

end SP1Clean.Soundness.NativeCore
