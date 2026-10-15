import SP1Clean.Math.Word

/-! # Three-limb unsigned addresses

The canonical encoding uses three little-endian 16-bit limbs. The conversion theorem makes its
48-bit domain explicit; callers must establish the bound before using the encoded address.
-/

namespace SP1Clean.Address

variable {p : ℕ}

def toNat (address : fields 3 (ZMod p)) : ℕ :=
  address[0].val + address[1].val * 2 ^ 16 + address[2].val * 2 ^ 32

def Bounded (address : fields 3 (ZMod p)) : Prop :=
  ∀ index : Fin 3, address[index].val < 2 ^ 16

def ofNat (address : ℕ) : fields 3 (ZMod p) :=
  #v[(address % 2 ^ 16 : ℕ), ((address / 2 ^ 16) % 2 ^ 16 : ℕ),
    ((address / 2 ^ 32) % 2 ^ 16 : ℕ)]

/-- Small offsets within the low limb, used for naturally aligned byte footprints. -/
def offset {F : Type} [Add F] (address : fields 3 F) (index : F) : fields 3 F :=
  #v[address[0] + index, address[1], address[2]]

theorem offset_zero {F : Type} [AddZeroClass F] (address : fields 3 F) :
    offset address 0 = address := by
  ext index hi
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> simp [offset]

variable [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem bounded_ofNat (address : ℕ) : Bounded (ofNat (p := p) address) := by
  intro index
  have hp := Fact.out (p := 2 ^ 17 < p)
  have bound (n : ℕ) : ((n % 2 ^ 16 : ℕ) : ZMod p).val < 2 ^ 16 := by
    rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt n (by decide : 0 < 2 ^ 16); omega)]
    exact Nat.mod_lt _ (by decide)
  fin_cases index <;> exact bound _

theorem toNat_ofNat (address : ℕ) (bounded : address < 2 ^ 48) :
    toNat (ofNat (p := p) address) = address := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have value (n : ℕ) : ((n % 2 ^ 16 : ℕ) : ZMod p).val = n % 2 ^ 16 :=
    ZMod.val_natCast_of_lt (by have := Nat.mod_lt n (by decide : 0 < 2 ^ 16); omega)
  simp only [toNat, ofNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, value]
  omega

theorem toNat_offset (address : fields 3 (ZMod p)) (bounded : Bounded address)
    (index : ℕ) (small : index < 2 ^ 16) :
    toNat (offset address (index : ZMod p)) = toNat address + index := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have low : address[0].val < 2 ^ 16 := bounded 0
  have indexVal : (index : ZMod p).val = index := ZMod.val_natCast_of_lt (by omega)
  simp only [offset, toNat, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [ZMod.val_add_of_lt (by rw [indexVal]; omega), indexVal]
  omega

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem toNat_lt {address : fields 3 (ZMod p)} (bounded : Bounded address) :
    toNat address < 2 ^ 48 := by
  have low : address[0].val < 2 ^ 16 := bounded 0
  have middle : address[1].val < 2 ^ 16 := bounded 1
  have high : address[2].val < 2 ^ 16 := bounded 2
  dsimp only [toNat]
  omega

/-- Canonical limbs are recovered exactly, not only modulo the identity space. -/
theorem ofNat_toNat {address : fields 3 (ZMod p)} (bounded : Bounded address) :
    ofNat (toNat address) = address := by
  have low : address[0].val < 2 ^ 16 := bounded 0
  have middle : address[1].val < 2 ^ 16 := bounded 1
  have high : address[2].val < 2 ^ 16 := bounded 2
  have hp := Fact.out (p := 2 ^ 17 < p)
  have value (n : ℕ) : ((n % 2 ^ 16 : ℕ) : ZMod p).val = n % 2 ^ 16 :=
    ZMod.val_natCast_of_lt (by have := Nat.mod_lt n (by decide : 0 < 2 ^ 16); omega)
  apply Vector.ext
  intro index bound
  apply ZMod.val_injective
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    simp only [ofNat, toNat, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, value]
  all_goals omega

/-- Embed an identity into the existing unsigned-word arithmetic gadgets. -/
def asWord {F : Type} [Zero F] (address : fields 3 F) : Word F :=
  #v[address[0], address[1], address[2], 0]

omit [Fact (2 ^ 17 < p)] in
theorem isU64_asWord {address : fields 3 (ZMod p)} (bounded : Bounded address) :
    Word.isU64 (asWord address) := by
  apply Word.isU64_of_cases
  · exact bounded 0
  · exact bounded 1
  · exact bounded 2
  · simp [asWord]

omit [Fact (2 ^ 17 < p)] in
theorem bounded_of_isU64_asWord {address : fields 3 (ZMod p)} (bounded : Word.isU64 (asWord address)) :
    Bounded address := by
  intro index
  fin_cases index
  · exact bounded 0
  · exact bounded 1
  · exact bounded 2

omit [Fact (2 ^ 17 < p)] in
theorem toNat_asWord (address : fields 3 (ZMod p)) : Word.toNat (asWord address) = toNat address := by
  simp [asWord, Word.toNat_def, toNat]

end SP1Clean.Address
