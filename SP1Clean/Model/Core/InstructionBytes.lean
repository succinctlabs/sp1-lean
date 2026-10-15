import SP1Clean.Model.Semantics.GuestProgram

/-! # Committed instruction words in byte memory

The check reads all four little-endian bytes through a partial memory observation. Sparse
snapshots and Sail memory use the same check; an absent byte is not a zero byte. This is byte
agreement, not a replacement for Sail fetch/decode or a proof of whole-path ROM preservation.
-/

namespace SP1Clean.Model.Core.InstructionBytes

/-- All four instruction bytes are present and agree with the committed word. -/
def check (read : ℕ → Option (BitVec 8)) (pc : BitVec 64) (word : BitVec 32) : Bool :=
  decide (∀ index : Fin 4,
    read (pc.toNat + index.val) = some (word.extractLsb' (8 * index.val) 8))

/-- The executable check is exactly little-endian byte agreement, including key presence. -/
theorem check_iff (read : ℕ → Option (BitVec 8)) (pc : BitVec 64) (word : BitVec 32) :
    check read pc word = true ↔ ∀ index : Fin 4,
      read (pc.toNat + index.val) = some (word.extractLsb' (8 * index.val) 8) := by
  simp only [check, decide_eq_true_eq]

/-- Loaded immutable code discharges the check at any committed instruction address. -/
theorem check_of_romLoaded {program : SP1Clean.Soundness.Target.GuestProgram}
    {state : SailState} {pc : BitVec 64} {word : BitVec 32}
    (loaded : SP1Clean.Soundness.Target.RomLoaded program state)
    (fetched : program.fetchWord pc = some word) :
    check state.mem.get? pc word = true :=
  (check_iff _ _ _).mpr (loaded pc word fetched)

end SP1Clean.Model.Core.InstructionBytes
