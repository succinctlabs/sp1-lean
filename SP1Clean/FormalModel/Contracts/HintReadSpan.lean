import SP1Clean.FormalModel.Contracts.AddressDiv8

/-! # Exact word count and final cell for HINT_READ

The last written cell remains a 48-bit address even when the write ends exactly at `2^48`.
The count includes mandatory padding for empty and aligned hints. This contract fixes the
endpoints a complete word consumer must connect; it does not assert ledger coverage or permission.
-/

namespace SP1Clean.HintReadSpan

structure Inputs (F : Type) where
  start : fields 3 F
  startQuotients : fields 3 F
  length : AddressDiv8.Inputs F
  last : fields 3 F
  count : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Domain (address length : ℕ) : Prop :=
  2 ^ 16 ≤ address ∧ address % 8 = 0 ∧ address + 8 * (length / 8 + 1) ≤ 2 ^ 48

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  Address.Bounded input.start ∧ Word.isU64 input.length.value ∧
    Domain (Address.toNat input.start) (Word.toNat input.length.value) ∧
    Address.Bounded input.last ∧
    Address.toNat input.last = Address.toNat input.start + Word.toNat input.length.value / 8 * 8 ∧
    Address.Bounded input.count ∧ Address.toNat input.count = Word.toNat input.length.value / 8 + 1

end SP1Clean.HintReadSpan
