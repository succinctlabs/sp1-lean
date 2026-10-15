import SP1Clean.FormalModel.Contracts.FinalMemoryChange
import ToClean.Air.UnitBalance

/-! # Complete Memory comparison from final-record and change ledgers

These are accounting lemmas for the installed boundary proof. Every validation row is tied
to the finalizer's full record by receipt permutation, and its Boolean key names that record's
semantic location. Count-bounded change-channel balance then covers the verifier's canonical
change inventory. Consequently untouched target changes cannot disappear from the final list.
The assembly must derive these inventories and local facts from its physical tables.
-/

namespace SP1Clean.Soundness.FinalMemoryChangeCoverage

open Model.Core Channels Semantics FinalMemoryChange

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A decoded validation row together with its statically registered location kind. -/
abbrev Row (p : ℕ) := Bool × Inputs (ZMod p)

/-- The full physical change ledger, including every disabled producer occurrence. -/
def ledger (source target : MemorySnapshot) (rows : List (Row p)) : List (Interaction (ZMod p)) :=
  rows.map (fun row => channel.pushedIfValue row.2.selected (key row.1 row.2.record)) ++
    (source.changes target).map (fun loc => channel.pulledValue (encode loc))

/-- A balanced change ledger covers every computed change with an actual validation row. -/
theorem changes_covered (source target : MemorySnapshot) (rows : List (Row p))
    (binary : ∀ row ∈ rows, Spec row.2)
    (names : ∀ row ∈ rows, key row.1 row.2.record = encode (MemoryMsg.locOf row.2.record))
    (balanced : BalancedInteractions (ledger source target rows)) :
    source.changes target ⊆ rows.map (fun row => MemoryMsg.locOf row.2.record) := by
  have same := channel.gated_unit_perm_of_balanced rows (fun row => row.2.selected)
    (fun row => key row.1 row.2.record) ((source.changes target).map encode) binary
    (by simpa only [ledger, List.map_map, Function.comp_def] using balanced)
  intro loc changed
  have member := same.mem_iff.mpr (List.mem_map_of_mem (f := encode (p := p)) changed)
  obtain ⟨row, selected, equal⟩ := List.mem_map.mp member
  have present := (List.mem_filter.mp selected).1
  have location : MemoryMsg.locOf row.2.record = loc :=
    encode_injective ((names row present).symm.trans equal)
  exact List.mem_map.mpr ⟨row, present, location⟩

/-- Target validation, complete final receipts, and the physical change ledger imply the
existing complete snapshot comparison. No Boolean comparison is assumed by this theorem. -/
theorem checkFinal_of_balanced (source target : MemorySnapshot)
    (records : List (MemoryMsg (ZMod p))) (rows : List (Row p))
    (receipts : (rows.map fun row => row.2.record).Perm records)
    (values : ∀ row ∈ rows,
      target.read (MemoryMsg.locOf row.2.record) = Word.toBitVec64 row.2.record.value)
    (binary : ∀ row ∈ rows, Spec row.2)
    (names : ∀ row ∈ rows, key row.1 row.2.record = encode (MemoryMsg.locOf row.2.record))
    (balanced : BalancedInteractions (ledger source target rows)) :
    source.checkFinal target
      (records.map fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value)) = true := by
  apply (MemorySnapshot.checkFinal_iff_changes _ _ _).mpr
  constructor
  · intro observed member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨row, rowPresent, rfl⟩ := List.mem_map.mp (receipts.mem_iff.mpr present)
    exact values row rowPresent
  · intro loc changed
    have covered := changes_covered source target rows binary names balanced changed
    obtain ⟨row, present, equal⟩ := List.mem_map.mp covered
    simp only [List.map_map, Function.comp_def]
    exact List.mem_map.mpr ⟨row.2.record,
      receipts.mem_iff.mp (List.mem_map_of_mem (f := fun row : Row p => row.2.record) present), equal⟩

end SP1Clean.Soundness.FinalMemoryChangeCoverage
