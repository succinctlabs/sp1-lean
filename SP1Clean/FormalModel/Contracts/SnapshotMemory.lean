import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.Model.Core.MemorySnapshot

/-! # Authenticated source records for arbitrary local snapshots

Zero is the local ledger's source-record time. These records authenticate values at a supplied
finite snapshot; they do not claim that a continuation's last access occurred at global time zero.
Transport to timed grounding and complete endpoint authentication remain ensemble-level work.
-/

namespace SP1Clean.MemoryBoundary

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime]

def SnapshotSpec (snapshot : MemorySnapshot) (message : MemoryMsg (ZMod p)) : Prop :=
  MemoryMsg.isU64 message ∧ MemoryMsg.ClkBound message ∧
    MemoryMsg.timeNat message = 0 ∧ (MemoryMsg.locOf message).CanonicalAddress ∧
      snapshot.read (MemoryMsg.locOf message) = Word.toBitVec64 message.value ∧ CanonicalKey message

def SnapshotAtSpec (snapshot : MemorySnapshot) (query : ℕ) (message : MemoryMsg (ZMod p)) : Prop :=
  SnapshotSpec snapshot message ∧ Word.toNat (address message) = query

theorem SnapshotSpec.canonical {snapshot : MemorySnapshot} {message : MemoryMsg (ZMod p)}
    (valid : SnapshotSpec snapshot message) : CanonicalSpec message :=
  ⟨valid.2.2.2.1, valid.2.2.2.2.2⟩

/-- The value is authentic in any actual Sail state realizing the complete finite snapshot. -/
theorem SnapshotSpec.locContent {snapshot : MemorySnapshot} {message : MemoryMsg (ZMod p)}
    (valid : SnapshotSpec snapshot message) {state : SailState}
    (realizes : snapshot.Realizes state) :
    locContent state (MemoryMsg.locOf message) = some (Word.toBitVec64 message.value) :=
  (realizes.locContent _ valid.2.2.2.1).trans (congrArg some valid.2.2.2.2.1)

/-- The old boot-record contract is a specialization of snapshot authentication. -/
theorem SnapshotSpec.initial {image : ProgramImage} {message : MemoryMsg (ZMod p)}
    (valid : SnapshotSpec image.memorySnapshot message) : InitialSpec image message :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1,
    valid.locContent image.memorySnapshot_realizes, valid.2.2.2.2.2⟩

end SP1Clean.MemoryBoundary
