import SP1Clean.Model.Core.Memory
import SP1Clean.Model.Semantics.GuestProgram

/-! # Realizing sparse byte memory in the official Sail state

The Sail runtime uses a finite partial map, whereas the native input model has zero defaults.
`toSailMemory` realizes the latter on a bounded address space and proves exact read/write agreement.
This is a semantic construction for the Sail execution relation: it is never evaluated by the
event compiler or exported witness generator. Those use the sparse representation directly.
The bound stays symbolic in all proofs, including the eventual 48-bit native specialization.
-/

namespace SP1Clean.Model.Core

namespace ByteMemory

/-- Realize every address below `limit`, including explicitly present zero bytes. -/
@[irreducible] def toSailMemory (memory : ByteMemory) (limit : ℕ) : Std.ExtHashMap ℕ (BitVec 8) :=
  (List.range limit).foldr (fun address result => result.insert address (memory.read address)) ∅

private theorem get?_foldr (memory : ByteMemory) (addresses : List ℕ) (query : ℕ) :
    (addresses.foldr (fun address (result : Std.ExtHashMap ℕ (BitVec 8)) =>
      result.insert address (memory.read address)) ∅).get? query =
      if query ∈ addresses then some (memory.read query) else none := by
  induction addresses with
  | nil => simp
  | cons address rest ih =>
      simp only [List.foldr_cons, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      by_cases equal : address = query
      · simp [equal]
      · simpa [equal, Ne.symm equal] using ih

/-- The realized Sail memory has exactly the native bytes inside its address space. -/
theorem toSailMemory_get? (memory : ByteMemory) (limit query : ℕ) :
    (memory.toSailMemory limit).get? query =
      if query < limit then some (memory.read query) else none := by
  simpa only [toSailMemory, List.mem_range] using get?_foldr memory (List.range limit) query

/-- Exact Sail-map equality is extensional equality of the supported sparse bytes. All addresses
outside the window are absent on both sides; equality never ignores an extra Sail-memory entry. -/
theorem toSailMemory_eq_iff (left right : ByteMemory) (limit : ℕ) :
    left.toSailMemory limit = right.toSailMemory limit ↔
      ∀ address < limit, left.read address = right.read address := by
  constructor
  · intro equal address bound
    have observed := congrArg (fun memory : Std.ExtHashMap ℕ (BitVec 8) => memory.get? address) equal
    simpa only [toSailMemory_get?, if_pos bound, Option.some.injEq] using observed
  · intro equal
    apply Std.ExtHashMap.ext_getElem?
    intro address
    change (left.toSailMemory limit).get? address = (right.toSailMemory limit).get? address
    by_cases bound : address < limit
    · simp only [toSailMemory_get?, if_pos bound, equal address bound]
    · simp only [toSailMemory_get?, if_neg bound]

/-- In-range sparse updates agree with Sail's actual memory-map insertion. -/
theorem toSailMemory_write (memory : ByteMemory) (limit address : ℕ) (value : BitVec 8)
    (inside : address < limit) :
    (memory.write address value).toSailMemory limit =
      (memory.toSailMemory limit).insert address value := by
  apply Std.ExtHashMap.ext_getElem?
  intro query
  change ((memory.write address value).toSailMemory limit).get? query =
    ((memory.toSailMemory limit).insert address value).get? query
  rw [toSailMemory_get?]
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  by_cases equal : address = query
  · subst query
    simp [inside]
  · simpa [equal, read_write] using (memory.toSailMemory_get? limit query).symm

end ByteMemory

open Sail LeanRV64D SP1Clean.Soundness.Target

/-- Platform configuration depends only on registers; replacing memory preserves all its facts. -/
theorem configured_with_memory {state : SailState} (configured : SailConfigured state)
    (memory : Std.ExtHashMap ℕ (BitVec 8)) : SailConfigured { state with mem := memory } := by
  rcases configured with ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

end SP1Clean.Model.Core
