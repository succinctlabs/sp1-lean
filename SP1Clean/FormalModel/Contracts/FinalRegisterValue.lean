import SP1Clean.Model.Core.RegisterSnapshotTable
import SP1Clean.Model.FinalMemoryValue

/-! # Complete outgoing register values

The final record's decoded register and all value limbs agree with the supplied target snapshot.
Its clock is preserved by the full-record handoff and is grounded by the enclosing Memory proof.
-/

namespace SP1Clean.FinalRegisterValue

open Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime]

def Spec (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Prop :=
  record.addr0.val < 32 ∧ record.addr1 = 0 ∧ record.addr2 = 0 ∧
    Word.isU64 record.value ∧
    Word.toBitVec64 record.value = target.read (MemoryMsg.locOf record)

end SP1Clean.FinalRegisterValue
