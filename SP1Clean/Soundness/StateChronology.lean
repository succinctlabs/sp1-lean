import SP1Clean.Soundness.TypedTimeContracts

/-! # Canonical chronology from a balanced State graph

The argument is independent of the ensemble layout and event types. Executing edges advance time,
preserve the high clock limb, and either preserve or bound the upper PC limbs. StateBump edges
provide canonical targets. Two goodness passes rule out noncanonical cycles before bump edges
cancel under re-limbing. The remaining ranked graph contains every execution occurrence.
-/

namespace SP1Clean.Soundness.StateChronology

open SP1Clean.Channels SP1Clean.Semantics RankedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Bounds needed to preserve State time and PC values under canonical re-limbing. -/
def Good (message : StateMsg (ZMod p)) : Prop :=
  message.clk_high.val < 2 ^ 24 ∧ message.pc1.val < 2 ^ 16 ∧ message.pc2.val < 2 ^ 16

/-- Executing edges' row-local classification, before global clock/PC bounds are known. -/
structure Advancing (edge : StateMsg (ZMod p) × StateMsg (ZMod p)) : Prop where
  increases : StateMsg.timeNat edge.1 < StateMsg.timeNat edge.2
  clockHigh : edge.2.clk_high = edge.1.clk_high
  pcClass : (edge.2.pc1 = edge.1.pc1 ∧ edge.2.pc2 = edge.1.pc2) ∨
    (edge.2.pc1.val < 2 ^ 16 ∧ edge.2.pc2.val < 2 ^ 16)

/-- Both endpoints of every executing edge are good; actual StateBump edges become self-loops. -/
theorem good_and_bumps_cancel {α : Type*} (rows : List α)
    (edge : α → StateMsg (ZMod p) × StateMsg (ZMod p))
    (bumps : List (StateBumpChip.Inputs (ZMod p))) (initial final : StateMsg (ZMod p))
    (balanced : EndpointBalanced
      ((↑(rows.map edge) : Multiset _) +
        (↑(bumps.map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))) : Multiset _))
      id initial final)
    (initialGood : Good initial) (finalGood : Good final)
    (advance : ∀ row ∈ rows, Advancing (edge row))
    (bumpSpec : ∀ row ∈ bumps, StateBumpChip.Spec row ∧ row.is_real = 1) :
    (∀ row ∈ rows, Good (edge row).1 ∧ Good (edge row).2) ∧
      ∀ row ∈ bumps, canonState (StateBumpChip.pulledMessage row) =
        canonState (StateBumpChip.pushedMessage row) := by
  classical
  let events : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p)) := ↑(rows.map edge)
  let refreshes : Multiset (StateMsg (ZMod p) × StateMsg (ZMod p)) :=
    ↑(bumps.map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row)))
  have eventFacts : ∀ e ∈ events, Advancing e := by
    intro e member
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
    exact advance row rowMem
  have bumpGood : ∀ e ∈ refreshes, Good e.2 := by
    intro e member
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
    exact stateBump_pushedMessage_good (bumpSpec row rowMem).1 (bumpSpec row rowMem).2
  have clocks := GoodnessFilter.good_of_endpointBalanced id
    (fun message : StateMsg (ZMod p) => message.clk_high.val < 2 ^ 24) StateMsg.timeNat
    events refreshes initial final balanced initialGood.1 finalGood.1
    (fun e member => ⟨by dsimp only [id_eq]; rw [(eventFacts e member).clockHigh],
      fun _ => (eventFacts e member).increases⟩)
    (fun e member => (bumpGood e member).1)
  let preserves := fun e : StateMsg (ZMod p) × StateMsg (ZMod p) =>
    e.2.pc1 = e.1.pc1 ∧ e.2.pc2 = e.1.pc2
  have split : events + refreshes = events.filter preserves +
      (events.filter (fun e => ¬ preserves e) + refreshes) := by
    rw [← add_assoc, Multiset.filter_add_not]
  have pcBalance : EndpointBalanced (events.filter preserves +
      (events.filter (fun e => ¬ preserves e) + refreshes)) id initial final := by
    rw [← split]; exact balanced
  have pcPres : ∀ e ∈ events.filter preserves,
      ((e.1.pc1.val < 2 ^ 16 ∧ e.1.pc2.val < 2 ^ 16) ↔
        (e.2.pc1.val < 2 ^ 16 ∧ e.2.pc2.val < 2 ^ 16)) ∧
      (¬ (e.1.pc1.val < 2 ^ 16 ∧ e.1.pc2.val < 2 ^ 16) → StateMsg.timeNat e.1 < StateMsg.timeNat e.2) := by
    intro e member
    obtain ⟨eventMem, keep⟩ := Multiset.mem_filter.mp member
    exact ⟨by rw [keep.1, keep.2], fun _ => (eventFacts e eventMem).increases⟩
  have pcCons : ∀ e ∈ events.filter (fun e => ¬ preserves e) + refreshes,
      e.2.pc1.val < 2 ^ 16 ∧ e.2.pc2.val < 2 ^ 16 := by
    intro e member
    rcases Multiset.mem_add.mp member with eventMem | bumpMem
    · obtain ⟨eventMem, different⟩ := Multiset.mem_filter.mp eventMem
      exact (eventFacts e eventMem).pcClass.resolve_left different
    · exact (bumpGood e bumpMem).2
  have pcs := GoodnessFilter.good_of_endpointBalanced id
    (fun message : StateMsg (ZMod p) => message.pc1.val < 2 ^ 16 ∧ message.pc2.val < 2 ^ 16)
    StateMsg.timeNat _ _ initial final pcBalance initialGood.2 finalGood.2 pcPres pcCons
  constructor
  · intro row member
    have em : edge row ∈ events := Multiset.mem_coe.mpr (List.mem_map_of_mem member)
    have pc :
        ((edge row).1.pc1.val < 2 ^ 16 ∧ (edge row).1.pc2.val < 2 ^ 16) ∧
        ((edge row).2.pc1.val < 2 ^ 16 ∧ (edge row).2.pc2.val < 2 ^ 16) := by
      by_cases keep : preserves (edge row)
      · exact pcs.1 _ (Multiset.mem_filter.mpr ⟨em, keep⟩)
      · exact ⟨pcs.2 _ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_filter.mpr ⟨em, keep⟩))),
          (advance row member).pcClass.resolve_left keep⟩
    exact ⟨⟨(clocks.1 _ em).1, pc.1⟩, ⟨(clocks.1 _ em).2, pc.2⟩⟩
  · intro row member
    have bm : (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row) ∈ refreshes :=
      Multiset.mem_coe.mpr (List.mem_map_of_mem member)
    have pc := pcs.2 _ (Multiset.mem_add.mpr (Or.inr bm))
    exact stateBump_canon_eq_of_pulled_good (bumpSpec row member).1 (bumpSpec row member).2
      (clocks.2 _ bm) pc.1 pc.2

omit [Fact (2 ^ 25 < p)] in
private theorem trail_of_canonical_balance {α V : Type*} (rows : List α)
    (edge : α → V × V) (bumps : Multiset (V × V)) (initial final : V)
    (canon : V → V) (rank : V → ℕ)
    (balanced : EndpointBalanced ((↑(rows.map edge) : Multiset (V × V)) + bumps) id initial final)
    (loops : ∀ pair ∈ bumps, canon pair.1 = canon pair.2)
    (increase : ∀ row ∈ rows, rank (canon (edge row).1) < rank (canon (edge row).2)) :
    ∃ ordered, Walk.IsWalk (fun row => (canon (edge row).1, canon (edge row).2))
      (canon initial) (canon final) ordered ∧ ordered.Perm rows := by
  classical
  have mapped := GoodnessFilter.endpointBalanced_map canon _ id _ _ balanced
  have residue := GoodnessFilter.endpointBalanced_of_cancel_loops
    (↑(rows.map edge) : Multiset (V × V)) bumps
    (fun pair => (canon pair.1, canon pair.2)) (canon initial) (canon final) loops mapped
  have rowBalance := GoodnessFilter.endpointBalanced_of_map edge (↑rows)
    (fun pair => (canon pair.1, canon pair.2)) _ _ (by
      rw [Multiset.map_coe]; exact residue)
  obtain ⟨ordered, walk, exhaustive⟩ := exists_exhaustiveTrail_of_endpointBalanced (↑rows)
    (fun row => (canon (edge row).1, canon (edge row).2)) rank _ _ rowBalance
    (fun row member => increase row (Multiset.mem_coe.mp member))
  exact ⟨ordered, walk, Multiset.coe_eq_coe.mp exhaustive⟩

/-- Canonicalizing and cancelling the actual bump edges leaves an exhaustive execution trail. -/
theorem exhaustiveTrail {α : Type*} (rows : List α)
    (edge : α → StateMsg (ZMod p) × StateMsg (ZMod p))
    (bumps : List (StateBumpChip.Inputs (ZMod p))) (initial final : StateMsg (ZMod p))
    (balanced : EndpointBalanced
      ((↑(rows.map edge) : Multiset _) +
        (↑(bumps.map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))) : Multiset _))
      id initial final)
    (initialGood : Good initial) (finalGood : Good final)
    (advance : ∀ row ∈ rows, Advancing (edge row))
    (bumpSpec : ∀ row ∈ bumps, StateBumpChip.Spec row ∧ row.is_real = 1) :
    ∃ ordered : List α,
      Walk.IsWalk (fun row => (canonState (edge row).1, canonState (edge row).2))
        (canonState initial) (canonState final) ordered ∧ ordered.Perm rows := by
  classical
  have facts := good_and_bumps_cancel rows edge bumps initial final balanced initialGood finalGood advance bumpSpec
  apply trail_of_canonical_balance rows edge
    (↑(bumps.map (fun row => (StateBumpChip.pulledMessage row, StateBumpChip.pushedMessage row))))
    initial final canonState StateMsg.timeNat balanced
  · intro pair member
    obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
    exact facts.2 row rowMem
  · intro row member
    rw [timeNat_canonState (facts.1 row member).1.1,
      timeNat_canonState (facts.1 row member).2.1]
    exact (advance row member).increases

end SP1Clean.Soundness.StateChronology
