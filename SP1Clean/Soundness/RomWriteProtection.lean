import SP1Clean.Soundness.RowEffectDefs
import SP1Clean.FormalModel.Contracts.WritePermission

/-! # ROM preservation from the actual byte footprint

The chip bridge already proves that a store frames every byte outside its committed write.
Permission for those written bytes therefore preserves instruction memory, including code sharing
an eight-byte RAM cell with writable data. No property of unrelated interpreter steps is needed.
-/

namespace SP1Clean.Soundness.Target

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Permission refers to the committed write footprint, rather than an entire RAM bus cell. -/
def RowWritePermitted (image : ProgramImage) (row : Trace.RowView (ZMod p)) : Prop :=
  ∀ write, row.commit.memWrite = some write →
    ∀ address, write.covers address → image.readOnly address = false

/-- Full permission for the semantic footprint retains the native address bound as well as ROM exclusion. -/
def RowWriteAuthorized (image : ProgramImage) (row : Trace.RowView (ZMod p)) : Prop :=
  ∀ write, row.commit.memWrite = some write →
    ∀ address, write.covers address → address < 2 ^ 48 ∧ image.readOnly address = false

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem RowWriteAuthorized.permitted {image : ProgramImage} {row : Trace.RowView (ZMod p)}
    (authorized : RowWriteAuthorized image row) : RowWritePermitted image row :=
  fun write same address covered => (authorized write same address covered).2

/-- The byte requests cover the semantic write range, including its final byte. -/
theorem write_authorized_of_permissions (image : ProgramImage)
    (write : Trace.MemWrite (ZMod p)) (widthBound : write.width ≤ 2 ^ 16)
    (permissions : ∀ index : Fin write.width,
      WritePermissionProvider.Permitted image (Address.offset write.addr (index.val : ZMod p)))
    (address : ℕ) (covered : write.covers address) : address < 2 ^ 48 ∧ image.readOnly address = false := by
  change Address.toNat write.addr ≤ address ∧ address < Address.toNat write.addr + write.width at covered
  have positive : 0 < write.width := by omega
  have bounded : Address.Bounded write.addr := by
    simpa only [Nat.cast_zero, Address.offset_zero] using (permissions ⟨0, positive⟩).1
  let index : Fin write.width := ⟨address - Address.toNat write.addr, by omega⟩
  have permitted := (permissions index).2
  rw [Address.toNat_offset write.addr bounded index.val (by have := index.isLt; omega)] at permitted
  have same : Address.toNat write.addr + index.val = address := by dsimp only [index]; omega
  rwa [same] at permitted

theorem write_readOnly_false_of_permissions (image : ProgramImage)
    (write : Trace.MemWrite (ZMod p)) (widthBound : write.width ≤ 2 ^ 16)
    (permissions : ∀ index : Fin write.width,
      WritePermissionProvider.Permitted image (Address.offset write.addr (index.val : ZMod p)))
    (address : ℕ) (covered : write.covers address) : image.readOnly address = false := by
  exact (write_authorized_of_permissions image write widthBound permissions address covered).2

/-- An authorized row frames the complete Sail map outside native RAM, including absent keys. -/
theorem RowEffect.memory_outside_of_writeAuthorization {image : ProgramImage} (valid : image.Valid)
    {row : Trace.RowView (ZMod p)} {state next : SailState}
    (effect : RowEffect (image.toGuestProgram valid) row state next)
    (authorized : RowWriteAuthorized image row) (address : ℕ) (outside : 2 ^ 48 ≤ address) :
    next.mem.get? address = state.mem.get? address := by
  cases write : row.commit.memWrite with
  | none => exact effect.mem.1 write address
  | some footprint =>
    apply (effect.mem.2 footprint write).2
    intro covered
    have := (authorized footprint write address covered).1
    omega

/-- Byte permissions frame each protected address, even when its stored value would be unchanged. -/
theorem RowEffect.readOnly_of_writePermission {image : ProgramImage} {program : GuestProgram}
    {row : Trace.RowView (ZMod p)} {state next : SailState}
    (effect : RowEffect program row state next) (permitted : RowWritePermitted image row)
    (address : ℕ) (readOnly : image.readOnly address = true) :
    next.mem.get? address = state.mem.get? address := by
  cases write : row.commit.memWrite with
  | none => exact effect.mem.1 write address
  | some footprint =>
      apply (effect.mem.2 footprint write).2
      intro covered
      have denied := permitted footprint write address covered
      rw [readOnly] at denied
      contradiction

theorem RowEffect.romLoaded_of_writePermission {image : ProgramImage} (valid : image.Valid)
    {row : Trace.RowView (ZMod p)} {state next : SailState}
    (effect : RowEffect (image.toGuestProgram valid) row state next)
    (permitted : RowWritePermitted image row)
    (loaded : RomLoaded (image.toGuestProgram valid) state) :
    RomLoaded (image.toGuestProgram valid) next := by
  intro pc word fetched index
  have readonly : image.readOnly (pc.toNat + index) = true := by
    obtain ⟨entry, found, wordEq⟩ := Option.map_eq_some_iff.mp fetched
    have member : entry ∈ image.rom := List.mem_of_find?_eq_some found
    have atPc : entry.1 = pc := by simpa using List.find?_some found
    apply (image.readOnly_iff _).mpr
    exact ⟨entry, member, by rw [atPc]; omega, by rw [atPc]; have := index.isLt; omega⟩
  have frame := effect.readOnly_of_writePermission permitted _ readonly
  exact frame.trans (loaded pc word fetched index)

end SP1Clean.Soundness.Target
