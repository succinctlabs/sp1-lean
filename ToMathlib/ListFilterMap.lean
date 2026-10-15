module

public import Mathlib.Data.List.Nodup

/-! # Distinct decoded keys from distinct source keys

Mathlib's `List.Nodup.filterMap` requires the decoder itself to be injective on successful
inputs. A witness decoder commonly forgets columns instead: a separate source key is distinct
and determines the decoded key. This corollary needs agreement only on list members, and does
not require the encoding function to be injective. It belongs beside `Nodup.filterMap` upstream.
-/

public section

namespace List

theorem nodup_filterMap_of_nodup_map {Row Key Code : Type*} (rows : List Row)
    (key : Row → Code) (decode : Row → Option Key) (encode : Key → Code)
    (unique : (rows.map key).Nodup)
    (agrees : ∀ row ∈ rows, ∀ value, decode row = some value → key row = encode value) :
    (rows.filterMap decode).Nodup := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have parts := List.nodup_cons.mp unique
    have tail := ih parts.2 (fun row member => agrees row (List.mem_cons_of_mem _ member))
    cases found : decode row with
    | none => simpa only [List.filterMap_cons, found] using tail
    | some value =>
      simp only [List.filterMap_cons, found, List.nodup_cons]
      refine ⟨?_, tail⟩
      intro member
      obtain ⟨other, otherMem, same⟩ := List.mem_filterMap.mp member
      apply parts.1
      refine List.mem_map.mpr ⟨other, otherMem, ?_⟩
      exact (agrees other (List.mem_cons_of_mem _ otherMem) value same).trans
        (agrees row (List.mem_cons_self ..) value found).symm

end List
