import SP1Clean.Model.Core.MemorySnapshot
import SP1Clean.FormalModel.Contracts.InitialMemoryRead
import SP1Clean.FormalModel.Contracts.FinalRam
import SP1Clean.Model.FinalMemoryValue

/-! # Complete outgoing RAM values

The checker authenticates eight target bytes at the record's encoded address. The original
RAM finalizer owns alignment and the RAM address domain; its full-record handoff retains those
facts. This operation neither consumes the Memory bus nor invents a second final inventory.
-/

namespace SP1Clean.FinalRamValue

open Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime]

def Spec (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 (MemoryBoundary.address record) ∧
    Word.toNat (MemoryBoundary.address record) + 8 ≤ 2 ^ 48 ∧
    Word.isU64 record.value ∧ Word.toBitVec64 record.value =
      target.memory.readWord (Word.toNat (MemoryBoundary.address record))

/-- Canonical RAM provenance turns the checked byte read into the common snapshot observation. -/
theorem Spec.snapshot (target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (checked : Spec target record) (canonical : MemoryBoundary.CanonicalKey record)
    (ram : 32 ≤ (MemoryMsg.locOf record).busAddress) :
    Word.toBitVec64 record.value = target.read (MemoryMsg.locOf record) := by
  rw [target.read_of_ram_address _ ram, ← canonical.2]
  exact checked.2.2.2

/-- The native RAM finalizer supplies the location kind needed by the target-value check. -/
theorem Spec.final_snapshot (target : MemorySnapshot) (record : MemoryMsg (ZMod p))
    (checked : Spec target record) (finalized : MemoryBoundary.RamFinalSpec record) :
    Word.toBitVec64 record.value = target.read (MemoryMsg.locOf record) :=
  checked.snapshot target record finalized.1.2 (le_trans (by decide) finalized.2)

end SP1Clean.FinalRamValue
