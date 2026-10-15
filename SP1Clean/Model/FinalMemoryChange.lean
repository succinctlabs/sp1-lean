import SP1Clean.Model.Core.MemoryFinalCheck
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.Channels

/-! # Tagged locations for complete outgoing Memory coverage

The complete change inventory includes low RAM locations, which must remain distinct from
registers with the same numeric address. This accounting key carries that distinction explicitly.
It asserts no historical truth: the enclosing ledger must tie each selected key to a validated
final record. Decoding is a left inverse on all semantic locations, including low RAM.
-/

namespace SP1Clean.FinalMemoryChange

open Circuit Semantics Soundness

/-- An explicit register/RAM tag and the complete address word. -/
structure Key (F : Type) where
  /-- Zero for registers, one for RAM. -/
  ram : F
  /-- The canonical byte address, or register index. -/
  address : Word F
deriving ProvableStruct, DecidableEq, Inhabited
provable_struct_eval_lemmas Key

variable {p : ℕ} [Fact p.Prime]

/-- Pure accounting for selected final locations, with no semantic channel guarantee. -/
def channel : Channel (ZMod p) Key where
  name := "SP1FinalMemoryChange"
  Guarantees _ _ := True

omit [Fact p.Prime] in
@[circuit_norm ↓] theorem guarantees (key : Key (ZMod p)) (data : ProverData (ZMod p)) :
    channel.Guarantees key data := trivial

/-- Canonical tagged encoding, independent of the Memory bus's reserved address window. -/
def encode (loc : MemLoc) : Key (ZMod p) :=
  ⟨match loc with | .reg _ => 0 | .ram _ => 1,
    Target.bitVecToWord (BitVec.ofNat 64 loc.busAddress)⟩

/-- Decode the location kind before interpreting its numeric address. -/
def decode (key : Key (ZMod p)) : MemLoc :=
  if key.ram = 0 then .reg (BitVec.ofNat 5 (Word.toBitVec64 key.address).toNat)
  else .ram (BitVec.ofNat 61 ((Word.toBitVec64 key.address).toNat / 8))

variable [Fact (2 ^ 17 < p)]

theorem decode_encode (loc : MemLoc) : decode (encode (p := p) loc) = loc := by
  cases loc with
  | reg index =>
      simp only [decode, encode, MemLoc.busAddress, ↓reduceIte, Target.toBitVec64_bitVecToWord]
      have bound : index.toNat < 2 ^ 64 := lt_trans index.isLt (by decide)
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt index.isLt]
  | ram cell =>
      simp only [decode, encode, MemLoc.busAddress, one_ne_zero, ↓reduceIte,
        Target.toBitVec64_bitVecToWord]
      have bound : cell.toNat * 8 < 2 ^ 64 := by have := cell.isLt; omega
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt bound, show cell.toNat * 8 / 8 = cell.toNat by omega,
        Nat.mod_eq_of_lt cell.isLt]

theorem encode_injective : Function.Injective (encode (p := p)) :=
  Function.LeftInverse.injective decode_encode

end SP1Clean.FinalMemoryChange
