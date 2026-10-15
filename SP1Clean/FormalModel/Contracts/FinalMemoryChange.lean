import SP1Clean.Model.FinalMemoryChange
import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.Math.WordEquality

/-! # Selected contributions to the complete target-change inventory

Each input refers to a full final record. Its Boolean selector contributes zero or one copy
of the record's tagged location. Target-check wrappers compose this operation after validation
of the same record; selection cannot substitute another address or omit the validation.
-/

namespace SP1Clean.FinalMemoryChange

open Circuit Channels Semantics

/-- A complete authenticated record with one Boolean coverage choice. -/
structure Inputs (F : Type) where
  /-- The same record consumed by the target-value validator. -/
  record : MemoryMsg F
  /-- Whether this record covers a verifier-demanded change. -/
  selected : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Select the record's own address; the enclosing table fixes its register/RAM kind. -/
def key {F : Type} [Zero F] [One F] (ram : Bool) (record : MemoryMsg F) : Key F :=
  ⟨if ram then 1 else 0, MemoryBoundary.address record⟩

/-- Each validated record contributes either zero or one changed-location occurrence. -/
def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  input.selected = 0 ∨ input.selected = 1

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The tagged key names the exact semantic location when the original finalizer is canonical. -/
theorem key_eq_encode (ram : Bool) (record : MemoryMsg (ZMod p))
    (canonical : MemoryBoundary.CanonicalKey record)
    (kind : ram = match MemoryMsg.locOf record with | .reg _ => false | .ram _ => true) :
    key ram record = encode (MemoryMsg.locOf record) := by
  have address : MemoryBoundary.address record =
      Soundness.Target.bitVecToWord (BitVec.ofNat 64 (MemoryMsg.locOf record).busAddress) := by
    apply Word.eq_of_toBitVec64_eq canonical.1 (Soundness.Target.isU64_bitVecToWord _)
    rw [Soundness.Target.toBitVec64_bitVecToWord]
    change BitVec.ofNat 64 (Word.toNat (MemoryBoundary.address record)) = _
    rw [canonical.2]
  unfold key encode
  rw [kind]
  cases location : MemoryMsg.locOf record <;> rw [location] at address <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact congrArg (Key.mk _) address

end SP1Clean.FinalMemoryChange
