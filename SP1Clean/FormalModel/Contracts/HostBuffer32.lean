import SP1Clean.FormalModel.Contracts.HostRamBytes
import SP1Clean.Model.Core.HostReadWords

/-! # Complete 32-byte host reads

The buffer contract states its complete native address window and byte contents. The internal
aligned cells retain their event clock and cover exactly the requested span. The eight possible
starting offsets are circuit parameters; consumers use a common buffer message.
-/

namespace SP1Clean.HostBuffer32

open Circuit

/-- A 32-byte slice occupies four aligned cells, or five when its start is unaligned. -/
def cellCount (offset : Fin 8) : ℕ := (offset.val + 31) / 8 + 1

theorem cellCount_pos (offset : Fin 8) : 0 < cellCount offset := by
  unfold cellCount
  omega

def byteCell (offset : Fin 8) (index : Fin 32) : Fin (cellCount offset) :=
  ⟨(offset.val + index.val) / 8, by unfold cellCount; have := index.isLt; omega⟩

structure Message (F : Type) where
  clk_high : F
  clk_low : F
  address : Word F
  bytes : Vector F 32
deriving ProvableStruct
provable_struct_eval_lemmas Message

structure Inputs (offset : Fin 8) (F : Type) where
  message : Message F
  cells : Vector (HostRamBytes.Inputs F) (cellCount offset)
deriving ProvableStruct

def Message.Valid {p : ℕ} [Fact p.Prime] (message : Message (ZMod p)) : Prop :=
  Word.isU64 message.address ∧ 2 ^ 16 ≤ Word.toNat message.address ∧
    Word.toNat message.address + 32 ≤ 2 ^ 48 ∧
    ∀ index : Fin 32, message.bytes[index].val < 256

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_buffer32"
  Guarantees message _ := message.Valid

/-- The logical read keys have the buffer clock and precisely the minimal aligned cell cover. -/
def CellsMatch {p : ℕ} [Fact p.Prime] {offset : Fin 8} (input : Inputs offset (ZMod p)) : Prop :=
  Word.toNat input.message.address % 8 = offset.val ∧
    ∀ index : Fin (cellCount offset),
      input.cells[index].read.Valid ∧
      input.cells[index].read.clk_high = input.message.clk_high ∧
      input.cells[index].read.clk_low = input.message.clk_low ∧
      Word.toNat input.cells[index].read.address =
        Word.toNat input.message.address / 8 * 8 + 8 * index.val

/-- The output is exactly the requested bytes once the consumed words are grounded. -/
def Spec {p : ℕ} [Fact p.Prime] {offset : Fin 8} (input : Inputs offset (ZMod p)) : Prop :=
  input.message.Valid ∧ CellsMatch input ∧
    ∀ context : Model.Core.HostReadContext,
      (∀ index : Fin (cellCount offset), context.ObservesWord
        (Word.toNat input.cells[index].read.address) (Word.toBitVec64 input.cells[index].read.value)) →
      context.readBytes? (Word.toNat input.message.address) 32 =
        some (input.message.bytes.map fun byte => BitVec.ofNat 8 byte.val).toList

end SP1Clean.HostBuffer32
