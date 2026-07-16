import SP1Clean.Soundness.GatedVm.Chain
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-! # Ranked balance gives an exhaustive trail

Plain interaction balance produces only a subtrail; disconnected balanced cycles may remain.  VM
soundness needs a stronger statement: every real transition row occurs exactly once in the semantic
execution order.  The missing ingredient is a well-founded rank, instantiated by the decoded State
clock.  If every edge strictly raises that rank, no nonempty balanced residue can exist.

This file isolates that generic graph fact from SP1's field encodings, row decoder, and Sail semantics.
The production grounding engine must prove the two premises from the actual witness:

1. endpoint-multiset balance, supplied directly by the typed interaction-bus bridge; and
2. strict rank increase for every decoded real row, from its schedule constraints.

It then receives an exhaustive ordered trace.  Operand currency and the per-chip step theorem are a
separate induction over that trace. -/

namespace SP1Clean.Soundness.RankedGrounding

open SP1Clean.Soundness.GatedVm

universe u v

variable {Edge : Type u} {Vertex : Type v} [DecidableEq Edge] [DecidableEq Vertex]

/-- Balance as equality of produced and consumed endpoint multisets.  For transitions
`source → target`, the boundary contributes the initial source on the produced side and the final
target on the consumed side. -/
def EndpointBalanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) : Prop :=
  initial ::ₘ edges.map (fun row => (edge row).2) =
    final ::ₘ edges.map (fun row => (edge row).1)

omit [DecidableEq Edge] in
/-- Degree balance and endpoint-multiset balance are equivalent presentations.  This direction lets
the existing Eulerian extraction theorem feed the ranked exhaustiveness argument without another
trusted graph premise. -/
theorem endpointBalanced_of_balanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) (balanced : Balanced edges edge initial final) :
    EndpointBalanced edges edge initial final := by
  apply Multiset.ext.mpr
  intro vertex
  simp only [Multiset.count_cons, Multiset.count_map]
  have sourceFilter :
      edges.filter (fun row => vertex = (edge row).1) =
        edges.filter (fun row => (edge row).1 = vertex) := by
    congr 1
    funext row
    simp [eq_comm]
  have targetFilter :
      edges.filter (fun row => vertex = (edge row).2) =
        edges.filter (fun row => (edge row).2 = vertex) := by
    congr 1
    funext row
    simp [eq_comm]
  rw [sourceFilter, targetFilter]
  have h := balanced vertex
  simp only [outdeg, indeg] at h
  by_cases hif : initial = final
  · subst final
    simp at h ⊢
    omega
  · by_cases hi : vertex = initial
    · simp [hif, hi] at h ⊢
      omega
    · have hif' : final ≠ initial := fun equal => hif equal.symm
      by_cases hf : vertex = final <;> simp [hi, hf, hif'] at h ⊢ <;> omega

omit [DecidableEq Edge] in
/-- Endpoint-multiset balance implies the degree presentation used internally by the Eulerian trail
extractor.  Keeping this conversion here lets SP1's grounding layer expose only the direct typed-bus
statement, rather than rebuilding a second degree-counting model at the machine boundary. -/
theorem balanced_of_endpointBalanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) (balanced : EndpointBalanced edges edge initial final) :
    Balanced edges edge initial final := by
  intro vertex
  have counts := congrArg (Multiset.count vertex) balanced
  simp only [Multiset.count_cons, Multiset.count_map] at counts
  have sourceFilter :
      edges.filter (fun row => vertex = (edge row).1) =
        edges.filter (fun row => (edge row).1 = vertex) := by
    congr 1
    funext row
    simp [eq_comm]
  have targetFilter :
      edges.filter (fun row => vertex = (edge row).2) =
        edges.filter (fun row => (edge row).2 = vertex) := by
    congr 1
    funext row
    simp [eq_comm]
  rw [sourceFilter, targetFilter] at counts
  simp only [outdeg, indeg]
  by_cases hif : initial = final
  · subst final
    simp at counts ⊢
    omega
  · by_cases hi : vertex = initial
    · simp [hif, hi] at counts ⊢
      omega
    · have hif' : final ≠ initial := fun equal => hif equal.symm
      by_cases hf : vertex = final <;> simp [hi, hf, hif'] at counts ⊢ <;> omega

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Every walk has the expected telescoping endpoint-multiset balance. -/
theorem endpointBalanced_of_isWalk (edge : Edge → Vertex × Vertex) :
    ∀ {initial final : Vertex} {path : List Edge}, IsWalk edge initial final path →
      EndpointBalanced (↑path) edge initial final
  | initial, final, [], walk => by
      simp only [IsWalk] at walk
      simp [EndpointBalanced, walk]
  | initial, final, row :: rest, walk => by
      obtain ⟨source, tail⟩ := walk
      have ih := endpointBalanced_of_isWalk edge tail
      change (edge row).2 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).2) =
        final ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).1) at ih
      change initial ::ₘ (edge row).2 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).2) =
        final ::ₘ (edge row).1 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).1)
      rw [← source]
      rw [Multiset.cons_swap final (edge row).1]
      exact congrArg (Multiset.cons (edge row).1) ih

omit [DecidableEq Vertex] in
/-- A strictly ranked edge multiset has no nonempty balanced cycle. -/
theorem eq_zero_of_endpointBalanced_self (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2)
    (balanced : EndpointBalanced edges edge initial initial) :
    edges = 0 := by
  have endpointEq : edges.map (fun row => (edge row).2) =
      edges.map (fun row => (edge row).1) :=
    (Multiset.cons_inj_right initial).mp balanced
  by_contra nonempty
  obtain ⟨row, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
  have sumLt :
      (edges.map fun row => rank (edge row).1).sum <
        (edges.map fun row => rank (edge row).2).sum :=
    Multiset.sum_lt_sum
      (fun row member => (increases row member).le)
      ⟨row, member, increases row member⟩
  have sumEq :
      (edges.map fun row => rank (edge row).2).sum =
        (edges.map fun row => rank (edge row).1).sum := by
    have mapped := congrArg (fun rows : Multiset Vertex => (rows.map rank).sum) endpointEq
    simpa only [Multiset.map_map, Function.comp_apply] using mapped
  omega

/-- A trail that uses every edge exactly once.  Equality as a multiset permits the path order to be
derived rather than assumed while retaining duplicate row labels faithfully. -/
def ExhaustiveTrail (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) : Prop :=
  ∃ path : List Edge, IsWalk edge initial final path ∧ (↑path : Multiset Edge) = edges

/-- **Ranked balance ⇒ exhaustive trail.**  The older balance theorem yields a subtrail.  Subtracting
it leaves a balanced cycle; strict rank increase forces that residue to be empty. -/
theorem exists_exhaustiveTrail (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : Balanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2) :
    ExhaustiveTrail edges edge initial final := by
  obtain ⟨path, walk, subtrail⟩ := exists_trail edge edges initial final balanced
  obtain ⟨residue, decomposition⟩ := Multiset.le_iff_exists_add.mp subtrail
  have wholeEndpoints := endpointBalanced_of_balanced edges edge initial final balanced
  have pathEndpoints := endpointBalanced_of_isWalk edge walk
  have residueEndpoints : EndpointBalanced residue edge final final := by
    rw [decomposition] at wholeEndpoints
    simp only [EndpointBalanced, Multiset.map_add] at wholeEndpoints pathEndpoints ⊢
    have whole' :
        (initial ::ₘ (↑path : Multiset Edge).map (fun row => (edge row).2)) +
            residue.map (fun row => (edge row).2) =
          (final ::ₘ (↑path : Multiset Edge).map (fun row => (edge row).1)) +
            residue.map (fun row => (edge row).1) := by
      simpa only [Multiset.cons_add] using wholeEndpoints
    rw [pathEndpoints] at whole'
    exact congrArg (Multiset.cons final) (add_left_cancel whole')
  have residueIncrease : ∀ row ∈ residue, rank (edge row).1 < rank (edge row).2 := by
    intro row member
    apply increases row
    rw [decomposition]
    exact Multiset.mem_add.mpr (Or.inr member)
  have residueEmpty :=
    eq_zero_of_endpointBalanced_self residue edge rank residueIncrease residueEndpoints
  refine ⟨path, walk, ?_⟩
  simpa only [residueEmpty, add_zero] using decomposition.symm

/-- Direct endpoint-balance API for the grounding engine.  Degree balance remains an internal detail
of the existing trail extractor; callers need only the message permutation produced by a channel. -/
theorem exists_exhaustiveTrail_of_endpointBalanced (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : EndpointBalanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2) :
    ExhaustiveTrail edges edge initial final :=
  exists_exhaustiveTrail edges edge rank initial final
    (balanced_of_endpointBalanced edges edge initial final balanced) increases

end SP1Clean.Soundness.RankedGrounding
