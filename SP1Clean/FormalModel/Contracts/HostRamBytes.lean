import SP1Clean.FormalModel.Contracts.HostRamRead
import SP1Clean.Math.ByteWord

/-! # Byte contents of a host RAM read

The read channel supplies one bounded aligned word. This consumer returns its eight canonical
little-endian bytes. The cell's global currency comes from matching the read to the physical
Memory ledger; the byte decoder neither changes its address nor emits another Memory access.
-/

namespace SP1Clean.HostRamBytes

open Circuit

structure Inputs (F : Type) where
  read : HostRamReadChip.Message F
  low : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) (output : Vector (ZMod p) 8) : Prop :=
  input.read.Valid ∧ (∀ index : Fin 8, output[index].val < 256) ∧
    Word.toBitVec64 input.read.value =
      Word.bytesValue (output.map fun byte => BitVec.ofNat 8 byte.val)

end SP1Clean.HostRamBytes
