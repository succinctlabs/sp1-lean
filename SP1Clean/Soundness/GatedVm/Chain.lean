import SP1Clean.Soundness.GatedVm.Defs

/-! # Balance ⇒ trail: the Eulerian core of the gated VM

The mathematical heart of the gated VM capstone, stated abstractly over a directed multigraph and
**independent of SP1 / channels / fields**.

Model the state bus as a directed multigraph: each real row is an edge `current_state → next_state`
(`edge a = (current, next)` for `a` ranging over a multiset `E` of row labels), and the boundary
verifier contributes a genesis production of `init` and a finalization consumption of `final`. The
gated state-bus balance (`multiplicitySum = 0` at every state value) is exactly the **degree balance**

  `outdeg v − indeg v = [v = src] − [v = snk]`   (one source `src = init`, one sink `snk = final`),

`Balanced E edge src snk` below. From it we extract a **trail** (a walk whose edge multiset is `≤ E`)
from `src` to `snk` — `exists_trail` — with **no** clock-injectivity or clock-advance side conditions:
the whole-program transition path is forced by balance alone. The proof is a clean strong induction on
the edge multiset: take an out-edge of the source, erase it, observe the remainder is balanced with the
source shifted one step along, recurse. -/

namespace SP1Clean.Soundness

namespace GatedVm

variable {α V : Type} [DecidableEq α] [DecidableEq V]

/-- Out-degree of `v` in the edge multiset `E`: the number of edges whose **source** is `v`. -/
def outdeg (E : Multiset α) (edge : α → V × V) (v : V) : ℕ :=
  (E.filter (fun a => (edge a).1 = v)).card

/-- In-degree of `v`: the number of edges whose **target** is `v`. -/
def indeg (E : Multiset α) (edge : α → V × V) (v : V) : ℕ :=
  (E.filter (fun a => (edge a).2 = v)).card

/-- Degree balance: `src` has exactly one more outgoing than incoming edge, `snk` one more incoming
than outgoing, and every other vertex is balanced. This is precisely what the gated state bus's
`isConsistentBalanced` says, with `src = init`, `snk = final`. -/
def Balanced (E : Multiset α) (edge : α → V × V) (src snk : V) : Prop :=
  ∀ v, (outdeg E edge v : ℤ) - indeg E edge v
      = (if v = src then 1 else 0) - (if v = snk then 1 else 0)

/-- A walk along `edge`s from `a` to `b`: the edge list's sources and targets chain up
(`src = e₀.1`, `e_i.2 = e_{i+1}.1`, last `.2 = snk`); the empty walk requires `a = b`. -/
def IsWalk (edge : α → V × V) : V → V → List α → Prop
  | a, b, [] => a = b
  | a, b, x :: rest => (edge x).1 = a ∧ IsWalk edge (edge x).2 b rest

/-- Erasing one element `e ∈ E` drops the count of a filter by `1` exactly when `e` satisfies it. -/
lemma card_filter_erase {E : Multiset α} {e : α} (he : e ∈ E)
    (P : α → Prop) [DecidablePred P] :
    (E.filter P).card = ((E.erase e).filter P).card + (if P e then 1 else 0) := by
  conv_lhs => rw [← Multiset.cons_erase he]
  rw [Multiset.filter_cons, Multiset.card_add]
  by_cases h : P e <;> simp [h, Nat.add_comm]

/-- **The induction step.** If `E` is balanced with source `src`, sink `snk`, and `e` is an out-edge
of `src` (`(edge e).1 = src`), then `E.erase e` is balanced with the source moved to `(edge e).2`
(one step along `e`) and the same sink. -/
lemma balanced_erase {E : Multiset α} {e : α} (he : e ∈ E) (edge : α → V × V)
    {src snk : V} (h : Balanced E edge src snk) (h1 : (edge e).1 = src) :
    Balanced (E.erase e) edge (edge e).2 snk := by
  intro v
  have ho : (outdeg E edge v : ℤ)
      = (outdeg (E.erase e) edge v : ℤ) + (if (edge e).1 = v then 1 else 0) := by
    simp only [outdeg]; exact_mod_cast card_filter_erase he (fun a => (edge a).1 = v)
  have hi : (indeg E edge v : ℤ)
      = (indeg (E.erase e) edge v : ℤ) + (if (edge e).2 = v then 1 else 0) := by
    simp only [indeg]; exact_mod_cast card_filter_erase he (fun a => (edge a).2 = v)
  have hv := h v
  have e1 : (if (edge e).1 = v then (1 : ℤ) else 0) = (if v = src then 1 else 0) := by
    rcases eq_or_ne v src with hc | hc
    · rw [if_pos (h1.trans hc.symm), if_pos hc]
    · rw [if_neg (fun hh => hc (h1.symm.trans hh).symm), if_neg hc]
  have e2 : (if (edge e).2 = v then (1 : ℤ) else 0) = (if v = (edge e).2 then 1 else 0) := by
    rcases eq_or_ne v (edge e).2 with hc | hc
    · rw [if_pos hc.symm, if_pos hc]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc]
  rw [e1] at ho
  rw [e2] at hi
  linarith [ho, hi, hv]

/-- **Balance ⇒ trail (the Eulerian core).** From degree balance alone — no clock injectivity, no
clock-advance — a walk from `src` to `snk` exists whose edges are a sub-multiset of `E`. The
whole-program transition path is forced by the gated state-bus balance. -/
theorem exists_trail (edge : α → V × V) (E : Multiset α) :
    ∀ (src snk : V), Balanced E edge src snk →
      ∃ path : List α, IsWalk edge src snk path ∧ (↑path : Multiset α) ≤ E := by
  induction E using Multiset.strongInductionOn with
  | _ E IH =>
    intro src snk h
    by_cases hss : src = snk
    · exact ⟨[], hss, by simp⟩
    · have hsrc := h src
      rw [if_pos rfl, if_neg hss] at hsrc
      have hpos : 0 < outdeg E edge src := by omega
      simp only [outdeg] at hpos
      obtain ⟨e, he_filter⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos)
      rw [Multiset.mem_filter] at he_filter
      obtain ⟨he_mem, he1⟩ := he_filter
      have hbal' : Balanced (E.erase e) edge (edge e).2 snk := balanced_erase he_mem edge h he1
      have hlt : E.erase e < E := by
        conv_rhs => rw [← Multiset.cons_erase he_mem]
        exact Multiset.lt_cons_self _ _
      obtain ⟨path', hwalk', hsub'⟩ := IH (E.erase e) hlt (edge e).2 snk hbal'
      refine ⟨e :: path', ⟨he1, hwalk'⟩, ?_⟩
      have hle : (e ::ₘ (↑path' : Multiset α)) ≤ e ::ₘ E.erase e := Multiset.cons_le_cons e hsub'
      rwa [Multiset.cons_erase he_mem] at hle

end GatedVm

end SP1Clean.Soundness
