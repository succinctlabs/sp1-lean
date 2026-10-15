module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Multiset.MapFold
public import Std.Data.ExtDHashMap.Lemmas

/-! # A finite dependent map from a function on a finite type

## Gap against upstream

Std builds dependent hash maps from explicit lists and arrays. Mathlib provides finite-type
enumerations as finsets, whose unordered support should not require choosing a list order.
Inserting the same function value at each key commutes, so a multiset fold builds the map
computably, with lookup exactly equal to the supplied function.
-/

public section

namespace Std.ExtDHashMap

variable {α : Type*} {β : α → Type*} [DecidableEq α] [Hashable α]

private instance insertFunction_comm (f : (key : α) → β key) :
    LeftCommutative (fun key (map : ExtDHashMap α β) => map.insert key (f key)) where
  left_comm left right map := by
    apply ext_get?
    intro key
    by_cases same : left = right
    · subst right; rfl
    · by_cases atLeft : left = key
      · subst key
        simp [get?_insert, Ne.symm same]
      · by_cases atRight : right = key
        · subst key
          simp [get?_insert, same]
        · simp [get?_insert, atLeft, atRight]

/-- Construct every key of a finite dependent function without choosing an enumeration order. -/
def ofFintype [Fintype α] (f : (key : α) → β key) : ExtDHashMap α β :=
  Finset.univ.val.foldr (fun key map => map.insert key (f key)) ∅

private theorem get?_foldr_function (f : (key : α) → β key) (keys : Multiset α) (query : α) :
    (keys.foldr (fun key (map : ExtDHashMap α β) => map.insert key (f key)) ∅).get? query =
      if query ∈ keys then some (f query) else none := by
  induction keys using Multiset.induction_on with
  | empty => simp
  | cons key rest ih =>
      by_cases same : key = query
      · subst query
        simp
      · simp [Multiset.foldr_cons, get?_insert, same, Ne.symm same, ih]

@[simp] theorem get?_ofFintype [Fintype α] (f : (key : α) → β key) (key : α) :
    (ofFintype f).get? key = some (f key) := by
  simpa only [ofFintype, Finset.mem_val, Finset.mem_univ, ↓reduceIte] using
    get?_foldr_function f Finset.univ.val key

end Std.ExtDHashMap
