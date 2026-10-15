import SP1Clean.Soundness.RankedGrounding

/-! # A balanced State ledger with a disconnected cycle

The two-edge path from 0 to 2 and the cycle between 10 and 11 have balanced endpoints,
but no walk from 0 to 2 uses all four edges. No natural rank can strictly increase around
the cycle. This is a counterexample to State balance alone, not an accepted SP1 AIR witness.
The production ranked-grounding theorem supplies the missing exhaustiveness argument.
-/

namespace SP1Clean.Soundness.StateBalanceExample

open RankedGrounding

/-- A path from 0 to 2 together with a disconnected two-edge cycle. -/
def edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (10, 11), (11, 10)]

/-- Boundary tokens at 0 and 2 close the complete four-edge State ledger. -/
theorem endpointBalanced : EndpointBalanced (↑edges) id 0 2 := by
  unfold EndpointBalanced edges
  decide

/-- The visible path reaches the final endpoint without visiting the disconnected cycle. -/
theorem visiblePath : Walk.IsWalk id 0 2 [(0, 1), (1, 2)] := by
  simp [Walk.IsWalk]

/-- Strict increase on both cycle edges would require each rank to be smaller than the other. -/
theorem noIncreasingRank :
    ¬ ∃ rank : ℕ → ℕ, ∀ edge ∈ edges, rank edge.1 < rank edge.2 := by
  rintro ⟨rank, increases⟩
  have forward := increases (10, 11) (by simp [edges])
  have backward := increases (11, 10) (by simp [edges])
  exact (Nat.lt_asymm forward backward)

private theorem walkSourcesSmall (path : List (ℕ × ℕ)) (initial final : ℕ)
    (small : initial < 3) (member : ∀ edge ∈ path, edge ∈ edges)
    (walk : Walk.IsWalk id initial final path) : ∀ edge ∈ path, edge.1 < 3 := by
  induction path generalizing initial with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨atSource, tailWalk⟩ := walk
    have firstMember := member first (List.mem_cons_self ..)
    have nextSmall : first.2 < 3 := by
      rcases first with ⟨source, target⟩
      change source = initial at atSource
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at firstMember
      rcases firstMember with h | h | h | h <;> omega
    intro edge present
    rcases List.mem_cons.mp present with equal | inRest
    · subst edge
      change first.1 = initial at atSource
      rwa [atSource]
    · exact ih first.2 nextSmall (fun other h => member other (List.mem_cons_of_mem first h))
        tailWalk edge inRest

/-- Endpoint balance does not force a walk that exhausts the physical edge inventory. -/
theorem noExhaustiveTrail : ¬ ExhaustiveTrail (↑edges) id 0 2 := by
  rintro ⟨path, walk, exhaustive⟩
  have permutation := Multiset.coe_eq_coe.mp exhaustive
  have small := walkSourcesSmall path 0 2 (by decide)
    (fun edge present => permutation.mem_iff.mp present) walk
  have cyclePresent : (10, 11) ∈ path := permutation.mem_iff.mpr (by simp [edges])
  have impossible := small (10, 11) cyclePresent
  omega

end SP1Clean.Soundness.StateBalanceExample
