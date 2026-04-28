import SP1Foundations.Field
import SP1Foundations.Word
import LeanRV64D

open BitVec

lemma bitVec_sshiftright_eq (bv : BitVec w) (shift : ℕ) :
  bv.sshiftRight shift =
    BitVec.setWidth w
      (BitVec.extractLsb ((w - 1) + shift) shift (BitVec.signExtend (w + shift) bv))
    := by grind

namespace BitVec

attribute [simp] LeanRV64D.Functions.sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
attribute [simp] extractLsb extractLsb'

def extend {m : ℕ} (bv : BitVec m) (n : ℕ) (sgn : Prop) [Decidable sgn] := (if sgn then signExtend else setWidth) n bv

lemma toNat_lt_toNat_iff {n : ℕ} (x y : BitVec n) :
    x.toNat < y.toNat ↔ x < y := by rfl

lemma toNat_le_toNat_iff {n : ℕ} (x y : BitVec n) :
    x.toNat ≤ y.toNat ↔ x ≤ y := by rfl

@[simp] lemma twoPow_65536_32 : 65536#32 = BitVec.twoPow 32 16 := rfl

@[simp] lemma mod4_add_eq_mod4 (x y : BitVec 64)
    (hx : x < BitVec.twoPow 64 32)
    (hy : y < BitVec.twoPow 64 32) :
    (x + y) % 4#64 = (x % 4#64 + y) % 4#64 := by
  bv_decide

@[simp] lemma ofNat64_mod_4_eq_zero_iff (n : ℕ) :
    (BitVec.ofNat 64 n) % 4#64 = 0#64 ↔ n % 4 = 0 := by
  rw [BitVec.ofNat]
  rw [← BitVec.toFin_inj]
  simp
  rw [Fin.mod_def]
  rw [← Fin.val_inj]
  simp

theorem twoPow64_and_eq_self {a b : BitVec 64} (h : (a + b) % 4 = 0) :
    18446744073709551614#64 &&& (a + b) = a + b := by bv_decide

theorem add_mod4_eq_zero_of_mod4_eq_zero {a b : BitVec 64}
    (ha : a % 4 = 0) (hb : b % 4 = 0) : (a + b) % 4 = 0 := by bv_decide

theorem mod4_eq_zero_of_0_1_are_0 {x : BitVec 64} (h0 : x[0] = false) (h1 : x[1] = false) :
    x % 4 = 0 := by bv_decide

theorem mul4_means_0_1_are_0 {x : BitVec 64} (hx : x % 4 = 0) : x[0] = false ∧ x[1] = false := by
  have hx' : x.toNat % 4 = 0 := by bv_omega
  apply And.intro
  · have hzero : x[0] = x[(0 : Fin 64)] := by
      aesop
    rw [hzero]
    rw [←BitVec.getLsb_eq_getElem x 0]
    clear hzero
    simp [BitVec.getLsb]
    omega
  · have hzero : x[1] = x[(1 : Fin 64)] := by
      aesop
    rw [hzero]
    rw [←BitVec.getLsb_eq_getElem x 1]
    clear hzero
    simp [BitVec.getLsb, Nat.testBit]
    omega

end BitVec

/-- Absorbing a concrete bitvec constant `c` (as a `ℕ` literal) into a `Fin n`-based
`BitVec.ofNat` expression. The `c : ℕ` form is chosen so callsites with literals like
`4#64 = BitVec.ofNat 64 4` unify syntactically against the LHS pattern. -/
lemma Fin.BitVec_ofNat_add_eq_add_ofNat {n : ℕ} [NeZero n] (x : Fin n) (c : ℕ) {y z : ℕ}
    (hc : c < n) (hx : x.val + c < n) :
    BitVec.ofNat 64 (x.val + y + z) + BitVec.ofNat 64 c =
      BitVec.ofNat 64 ((x + Fin.ofNat n c).val + y + z) := by
  have hcval : (Fin.ofNat n c).val = c := Nat.mod_eq_of_lt hc
  rw [Fin.val_add, hcval, Nat.mod_eq_of_lt hx]
  simp [BitVec.ofNat_add]; ring_nf

namespace Nat

lemma lift_lt {a b : ℕ} (w : ℕ) : a < 2 ^ w → b < 2 ^ w → (a < b ↔ BitVec.ofNat w a < BitVec.ofNat w b) := by
  intro haw hbw
  constructor <;> intro lhs <;> simp_all
  · repeat rw [Nat.mod_eq_of_lt (by omega)]
    assumption
  · repeat rw [Nat.mod_eq_of_lt (by omega)] at lhs
    assumption

end Nat

namespace Word

lemma toBitVec64_mod_of_lt (w : Word (Fin KB)) (n : Fin 8) :
    (Word.toBitVec64 w) % BitVec.twoPow 64 n.val =
      (BitVec.ofNat 64 w[0]) % BitVec.twoPow 64 n.val := by
  simp [toBitVec64, toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  simp [BitVec.twoPow]
  set k := BitVec.ofNat 64 w[0]
  fin_cases n
  · simp only [shiftLeft_zero, umod_one] -- trivial case
  all_goals {simp only [reduceHShiftLeft]; bv_decide}

@[simp] lemma toBitVec64_mod2 (w : Word (Fin KB)) :
    (Word.toBitVec64 w) % 2#64 = (BitVec.ofNat 64 w[0]) % 2#64 :=
  toBitVec64_mod_of_lt w 1

@[simp] lemma toBitVec64_mod4 (w : Word (Fin KB)) :
    (Word.toBitVec64 w) % 4#64 = (BitVec.ofNat 64 w[0]) % 4#64 :=
  toBitVec64_mod_of_lt w 2

@[simp] lemma toBitVec64_mod8 (w : Word (Fin KB)) :
    (Word.toBitVec64 w) % 8#64 = (BitVec.ofNat 64 w[0]) % 8#64 :=
  toBitVec64_mod_of_lt w 3

@[simp] lemma toBitVec64_add_mod4 (w : Word (Fin KB)) (x : BitVec 64) :
    (Word.toBitVec64 w + x) % 4#64 = (BitVec.ofNat 64 w[0] + x) % 4#64 := by
  simp [toBitVec64, Word.toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  set k := BitVec.ofNat 64 w[0]
  bv_decide

@[simp] lemma add_toBitVec64_mod4 (w : Word (Fin KB)) (x : BitVec 64) :
    (x + Word.toBitVec64 w) % 4#64 = (x + BitVec.ofNat 64 w[0]) % 4#64 := by
  simp [toBitVec64, Word.toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  set k := BitVec.ofNat 64 w[0]
  bv_decide

@[simp] lemma setWidth8_toBitVec64 (w : Word (Fin KB)) :
    BitVec.setWidth 8 w.toBitVec64 = BitVec.ofNat 8 w[0] := by
  simp [toBitVec64, Word.toNat_def]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  omega

/-! ### Polymorphic counterparts -/

lemma toBitVec64_poly_mod_of_lt {p : ℕ} [NeZero p] (w : Word (ZMod p)) (n : Fin 8) :
    (Word.toBitVec64_poly w) % BitVec.twoPow 64 n.val =
      (BitVec.ofNat 64 w[0].val) % BitVec.twoPow 64 n.val := by
  simp [Word.toBitVec64_poly, Word.toNat_poly]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  simp [BitVec.twoPow]
  set k := BitVec.ofNat 64 w[0].val
  fin_cases n
  · simp only [shiftLeft_zero, umod_one]
  all_goals {simp only [reduceHShiftLeft]; bv_decide}

@[simp] lemma toBitVec64_poly_mod2 {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    (Word.toBitVec64_poly w) % 2#64 = (BitVec.ofNat 64 w[0].val) % 2#64 :=
  toBitVec64_poly_mod_of_lt w 1

@[simp] lemma toBitVec64_poly_mod4 {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    (Word.toBitVec64_poly w) % 4#64 = (BitVec.ofNat 64 w[0].val) % 4#64 :=
  toBitVec64_poly_mod_of_lt w 2

@[simp] lemma toBitVec64_poly_mod8 {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    (Word.toBitVec64_poly w) % 8#64 = (BitVec.ofNat 64 w[0].val) % 8#64 :=
  toBitVec64_poly_mod_of_lt w 3

@[simp] lemma toBitVec64_poly_add_mod4 {p : ℕ} [NeZero p]
    (w : Word (ZMod p)) (x : BitVec 64) :
    (Word.toBitVec64_poly w + x) % 4#64 = (BitVec.ofNat 64 w[0].val + x) % 4#64 := by
  simp [Word.toBitVec64_poly, Word.toNat_poly]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  set k := BitVec.ofNat 64 w[0].val
  bv_decide

@[simp] lemma add_toBitVec64_poly_mod4 {p : ℕ} [NeZero p]
    (w : Word (ZMod p)) (x : BitVec 64) :
    (x + Word.toBitVec64_poly w) % 4#64 = (x + BitVec.ofNat 64 w[0].val) % 4#64 := by
  simp [Word.toBitVec64_poly, Word.toNat_poly]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  set k := BitVec.ofNat 64 w[0].val
  bv_decide

@[simp] lemma setWidth8_toBitVec64_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    BitVec.setWidth 8 w.toBitVec64_poly = BitVec.ofNat 8 w[0].val := by
  simp [Word.toBitVec64_poly, Word.toNat_poly]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  omega

end Word

namespace BitVec

lemma toInt_toInt_as_toNat_128 {r1 r2 : BitVec 64} :
  (r1.toInt * r2.toInt % 340282366920938463463374607431768211456).toNat =
    (BitVec.signExtend 128 r1 * BitVec.signExtend 128 r2).toNat
    := by
  rw [← BitVec.toInt_signExtend_of_le (v := 128) (x := r1) (by simp)]
  rw [← BitVec.toInt_signExtend_of_le (v := 128) (x := r2) (by simp)]
  have h_max : forall (x : ℤ), max (x % 340282366920938463463374607431768211456) 0 = x % 340282366920938463463374607431768211456 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 340282366920938463463374607431768211456) 0 = (r2.toNat : ℤ) % 340282366920938463463374607431768211456 := by omega
  have rr1 : (r1.toNat : ℤ) % 340282366920938463463374607431768211456 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 340282366920938463463374607431768211456 = r2.toNat := by omega
  simp [BitVec.toInt, BitVec.signExtend]; split_ifs
  all_goals
    simp_all
    try omega
  · have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega
  · have : ((r2.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega
  · have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

lemma toInt_toNat_as_toNat_128 {r1 r2 : BitVec 64} :
  (r1.toInt * r2.toNat % 340282366920938463463374607431768211456).toNat =
    (BitVec.signExtend 128 r1 * BitVec.setWidth 128 r2).toNat
    := by
  rw [← BitVec.toInt_signExtend_of_le (v := 128) (x := r1) (by simp)]
  rw [← setWidth_idem (n := 128) (bv := r2) (by simp)]
  have h_max : forall (x : ℤ), max (x % 340282366920938463463374607431768211456) 0 = x % 340282366920938463463374607431768211456 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 340282366920938463463374607431768211456) 0 = (r2.toNat : ℤ) % 340282366920938463463374607431768211456 := by omega
  have rr1 : (r1.toNat : ℤ) % 340282366920938463463374607431768211456 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 340282366920938463463374607431768211456 = r2.toNat := by omega
  simp [BitVec.toInt, BitVec.signExtend]; split_ifs
  all_goals
    simp_all
    try omega
  · have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

lemma toNat_toInt_as_toNat_128 {r1 r2 : BitVec 64} :
  ((r1.toNat : ℤ) * r2.toInt % 340282366920938463463374607431768211456).toNat =
    (BitVec.setWidth 128 r1 * BitVec.signExtend 128 r2).toNat
    := by
  rw [← BitVec.toInt_signExtend_of_le (v := 128) (x := r2) (by simp)]
  rw [← setWidth_idem (n := 128) (bv := r1) (by simp)]
  have h_max : forall (x : ℤ), max (x % 340282366920938463463374607431768211456) 0 = x % 340282366920938463463374607431768211456 := by omega
  have mr1 : max ((r1.toNat : ℤ) % 340282366920938463463374607431768211456) 0 = (r1.toNat : ℤ) % 340282366920938463463374607431768211456 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 340282366920938463463374607431768211456) 0 = (r2.toNat : ℤ) % 340282366920938463463374607431768211456 := by omega
  have rr1 : (r1.toNat : ℤ) % 340282366920938463463374607431768211456 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 340282366920938463463374607431768211456 = r2.toNat := by omega
  simp [BitVec.toInt, BitVec.signExtend]; split_ifs
  all_goals
    simp_all
    try omega
  · have : ((r2.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

end BitVec
