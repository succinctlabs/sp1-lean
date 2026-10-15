module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Basic

/-! # Recovering prefixes from strictly ordered keys

Mathlib supplies pairwise ordering and sublist transport, but not the prefix characterization
used when two heterogeneous event lists share ordered keys. A strict key cutoff recovers the
prefix before an event; membership in that prefix selects the same rows from any list whose
keys occur in the larger list. These additions belong beside the list ordering lemmas upstream.
Grouping a physical inventory by distinct covered keys also preserves every occurrence; this
partition lemma keeps duplicate items while allowing the groups to change their order.
-/

public section

namespace List

variable {α β γ : Type*} [LinearOrder γ]

theorem filter_lt_eq_prefix (key : α → γ) {prior rest : List α} {row : α}
    (sorted : (prior ++ row :: rest).Pairwise (fun a b => key a < key b)) :
    (prior ++ row :: rest).filter (fun other => decide (key other < key row)) = prior := by
  have parts := pairwise_append.mp sorted
  have before : prior.filter (fun other => decide (key other < key row)) = prior :=
    filter_eq_self.mpr (fun other member => decide_eq_true (parts.2.2 other member row (mem_cons_self ..)))
  have after : rest.filter (fun other => decide (key other < key row)) = [] := by
    apply filter_eq_nil_iff.mpr
    intro other member
    simpa only [decide_eq_true_eq] using not_lt_of_gt ((pairwise_cons.mp parts.2.1).1 other member)
  simp only [filter_append, before, filter_cons, lt_self_iff_false, decide_false,
    Bool.false_eq_true, ↓reduceIte, after, append_nil]

/-- Selecting a smaller inventory by a larger walk's prefix agrees with the strict clock cutoff.
The smaller inventory need not itself be sorted to identify the same selected occurrences. -/
theorem filter_mem_prefix_eq_filter_lt (key : α → γ) (otherKey : β → γ)
    {prior rest : List α} {row : α} (others : List β)
    (sorted : (prior ++ row :: rest).Pairwise (fun a b => key a < key b))
    (included : others.map otherKey ⊆ (prior ++ row :: rest).map key) :
    others.filter (fun other => decide (otherKey other ∈ prior.map key)) =
      others.filter (fun other => decide (otherKey other < key row)) := by
  have before : ((prior ++ row :: rest).map key).filter (fun stamp => decide (stamp < key row)) = prior.map key := by
    rw [filter_map]
    exact congrArg (map key) (filter_lt_eq_prefix key sorted)
  apply filter_congr
  intro other member
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [← before, mem_filter, decide_eq_true_eq]
  exact and_iff_right (included (mem_map_of_mem (f := otherKey) member))

omit [LinearOrder γ] in
/-- Grouping an inventory by distinct keys preserves every occurrence, including duplicates. -/
theorem flatMap_filter_key_perm {κ : Type*} [DecidableEq κ] (keys : List κ) (items : List α)
    (key : α → κ) (unique : keys.Nodup) (covered : ∀ item ∈ items, key item ∈ keys) :
    (keys.flatMap (fun k => items.filter (fun item => decide (key item = k)))).Perm items := by
  have singleton (item : α) (member : key item ∈ keys) :
      keys.flatMap (fun k => if key item = k then [item] else []) = [item] := by
    have selected : keys.flatMap (fun k => if key item = k then [item] else []) =
        (keys.filter (fun k => decide (k = key item))).map (fun _ => item) := by
      clear unique covered member
      induction keys with
      | nil => rfl
      | cons k ks ih =>
        simp only [flatMap_cons, ih, filter_cons]
        by_cases same : key item = k
        · rw [if_pos same, if_pos (decide_eq_true same.symm)]
          rfl
        · rw [if_neg same, if_neg (show ¬decide (k = key item) = true by
            simpa only [decide_eq_true_eq] using Ne.symm same)]
          rfl
    rw [selected, filter_eq, count_eq_one_of_mem unique member]
    rfl
  induction items with
  | nil => simp
  | cons item rest ih =>
    have split : keys.flatMap (fun k => (item :: rest).filter (fun item => decide (key item = k))) =
        keys.flatMap (fun k => (if key item = k then [item] else []) ++
          rest.filter (fun item => decide (key item = k))) := by
      congr 1
      funext k
      by_cases same : key item = k <;> simp [same]
    rw [split]
    exact (flatMap_append_perm keys _ _).symm.trans
      ((Perm.of_eq (singleton item (covered item mem_cons_self))).append
        (ih (fun other member => covered other (mem_cons_of_mem _ member))))

end List
