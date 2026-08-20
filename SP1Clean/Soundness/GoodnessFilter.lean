import SP1Clean.Soundness.RankedGrounding

/-! # The goodness filter: a balanced graph over a good boundary has only good vertices (W3 D2)

The generic residue argument behind the StateBump rework (external report Finding 2). The state
trail's rank engine (`RankedGrounding`) needs every vertex's rank to be *meaningful* — for SP1,
`timeNat` is the genuine execution time only when the message's `clk_high` limb is a real 24-bit
value, not a huge field representative. Adding the StateBump table also breaks the old strict-rank
argument directly: a bump row's pull and push carry the *same* time, so its edge cannot strictly
increase any rank. This file isolates the two generic multiset facts that repair both problems,
keeping `RankedGrounding` itself byte-identical (W3 D1):

1. `endpointBalanced_of_cancel_loops` — **self-loop cancellation**: once vertices are mapped
   through a canonicalization under which a bump edge's endpoints are *equal*, those edges cancel
   from the endpoint balance outright, leaving the strictly-ranked instruction residue the existing
   engine consumes.
2. `good_of_endpointBalanced` — **the filter**: in an endpoint-balanced edge multiset over a good
   boundary, where every edge either *preserves* goodness across its endpoints (and strictly raises
   a rank whenever its endpoints are bad — SP1's instruction rows: `clk_high` is the same column on
   both sides, and the pulled low clock is range-checked by the row itself so the `+8` step is a
   genuine ℕ increase) or has an unconditionally *good* target (SP1's StateBump rows, whose pushed
   limbs are range-checked in-circuit; the boundary verifier's endpoints are good by D5-A's
   `LimbBounds`), **every endpoint is good**. The bad residue dies twice over: consumer edges by
   cardinality (each bad consumer pull would need a bad push, but bad pushes come only from
   preserving edges, matched one-for-one with their own bad pulls), preserving edges by the strict
   rank sum (`Multiset.sum_lt_sum`, exactly the `eq_zero_of_endpointBalanced_self` argument).

The SP1 instantiation — `Good m := m.clk_high.val < 2^24 ∧ …`, the canonicalization, and the
per-chip preservation facts — is the W3 phase-3 wiring; nothing here mentions messages, chips, or
fields. -/

namespace SP1Clean.Soundness.GoodnessFilter

open SP1Clean.Soundness.RankedGrounding

universe u v

variable {Edge : Type u} {Vertex : Type v}

/-- **Self-loop cancellation.** Edges whose two endpoints coincide contribute the same multiset to
the produced and consumed sides, so they cancel from the endpoint balance. -/
theorem endpointBalanced_of_cancel_loops (edges loops : Multiset Edge) (edge : Edge → Vertex × Vertex) (initial final : Vertex)
    (hloops : ∀ l ∈ loops, (edge l).1 = (edge l).2)
    (balanced : EndpointBalanced (edges + loops) edge initial final) :
    EndpointBalanced edges edge initial final := by
  unfold EndpointBalanced at balanced ⊢
  rw [Multiset.map_add, Multiset.map_add,
    Multiset.map_congr (rfl : loops = loops) (fun l hl => (hloops l hl).symm)] at balanced
  have shifted :
      (initial ::ₘ edges.map fun row => (edge row).2) + loops.map (fun row => (edge row).1) =
        (final ::ₘ edges.map fun row => (edge row).1) + loops.map (fun row => (edge row).1) := by
    simpa only [Multiset.cons_add] using balanced
  exact add_right_cancel shifted

section Filter

variable (edge : Edge → Vertex × Vertex) (Good : Vertex → Prop) (rank : Vertex → ℕ)

/-- **The goodness filter.** In an endpoint-balanced multiset `presEdges + consEdges` over a good
boundary, where every `presEdges` member preserves goodness across its endpoints and strictly
raises `rank` whenever its endpoints are bad, and every `consEdges` member has a good target,
every endpoint of every edge is good. -/
theorem good_of_endpointBalanced
    (presEdges consEdges : Multiset Edge) (initial final : Vertex)
    (balanced : EndpointBalanced (presEdges + consEdges) edge initial final)
    (hinit : Good initial) (hfinal : Good final)
    (hpres : ∀ e ∈ presEdges, (Good (edge e).1 ↔ Good (edge e).2) ∧
      (¬ Good (edge e).1 → rank (edge e).1 < rank (edge e).2))
    (hcons : ∀ e ∈ consEdges, Good (edge e).2) :
    (∀ e ∈ presEdges, Good (edge e).1 ∧ Good (edge e).2) ∧
      ∀ e ∈ consEdges, Good (edge e).1 := by
  classical
  -- Filter the endpoint-multiset equality down to the bad vertices; the good boundary drops out.
  have filtered := congrArg (Multiset.filter fun v => ¬ Good v) balanced
  rw [Multiset.filter_cons_of_neg (p := fun v => ¬ Good v) _ (not_not_intro hinit),
    Multiset.filter_cons_of_neg (p := fun v => ¬ Good v) _ (not_not_intro hfinal),
    Multiset.map_add, Multiset.map_add,
    Multiset.filter_add, Multiset.filter_add, Multiset.filter_map, Multiset.filter_map,
    Multiset.filter_map, Multiset.filter_map] at filtered
  -- The consumer targets are all good, so their bad-target filter is empty.
  rw [show consEdges.filter ((fun v => ¬ Good v) ∘ fun row => (edge row).2) = 0 from
    Multiset.filter_eq_nil.mpr fun e he => not_not_intro (hcons e he)] at filtered
  -- Preserving edges have bad targets exactly when they have bad sources.
  rw [show presEdges.filter ((fun v => ¬ Good v) ∘ fun row => (edge row).2)
      = presEdges.filter ((fun v => ¬ Good v) ∘ fun row => (edge row).1) from
    Multiset.filter_congr fun e he => not_congr (hpres e he).1.symm] at filtered
  set badPres := presEdges.filter ((fun v => ¬ Good v) ∘ fun row => (edge row).1) with hbadPres
  set badCons := consEdges.filter ((fun v => ¬ Good v) ∘ fun row => (edge row).1) with hbadCons
  simp only [Multiset.map_zero, add_zero] at filtered
  -- Cardinality: the bad consumer pulls are surplus, so there are none.
  have cardEq := congrArg Multiset.card filtered
  rw [Multiset.card_add, Multiset.card_map, Multiset.card_map, Multiset.card_map] at cardEq
  have badConsNil : badCons = 0 := by
    rw [← Multiset.card_eq_zero]
    omega
  rw [badConsNil, Multiset.map_zero, add_zero] at filtered
  -- Rank sum: each bad preserving edge strictly raises the rank, yet the two endpoint multisets
  -- coincide — so there are none either (`eq_zero_of_endpointBalanced_self`'s argument).
  have badPresNil : badPres = 0 := by
    by_contra nonempty
    obtain ⟨e, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
    have badMem : ∀ e' ∈ badPres, ¬ Good (edge e').1 := fun e' he' =>
      (Multiset.mem_filter.mp he').2
    have presMem : ∀ e' ∈ badPres, e' ∈ presEdges := fun e' he' =>
      (Multiset.mem_filter.mp he').1
    have sumLt : (badPres.map fun row => rank (edge row).1).sum <
        (badPres.map fun row => rank (edge row).2).sum :=
      Multiset.sum_lt_sum
        (fun e' he' => ((hpres e' (presMem e' he')).2 (badMem e' he')).le)
        ⟨e, member, (hpres e (presMem e member)).2 (badMem e member)⟩
    have sumEq : (badPres.map fun row => rank (edge row).2).sum =
        (badPres.map fun row => rank (edge row).1).sum := by
      have mapped := congrArg (fun rows : Multiset Vertex => (rows.map rank).sum) filtered
      simpa only [Multiset.map_map, Function.comp_apply] using mapped
    omega
  -- Assemble: no bad sources anywhere, and targets inherit goodness.
  have presGood : ∀ e ∈ presEdges, Good (edge e).1 := by
    intro e he
    by_contra bad
    exact absurd (Multiset.mem_filter.mpr ⟨he, bad⟩) (by rw [← hbadPres, badPresNil]; simp)
  refine ⟨fun e he => ⟨presGood e he, (hpres e he).1.mp (presGood e he)⟩, fun e he => ?_⟩
  by_contra bad
  exact absurd (Multiset.mem_filter.mpr ⟨he, bad⟩) (by rw [← hbadCons, badConsNil]; simp)

end Filter

end SP1Clean.Soundness.GoodnessFilter
