import SP1Foundations.Field
import SP1Foundations.Word
import LeanRV64D.Prelude
import LeanRV64D.Sail.Sail

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

namespace KoalaBear

lemma add4_into_pc_ofNat {x : Fin KB} {y z : ℕ} : x < 65536 →
  BitVec.ofNat 64 (x.val + y + z) + 4#64 = BitVec.ofNat 64 ((x + 4).val + y + z) := by
  intros
  rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  simp [ofNat_add]; ring_nf

end KoalaBear

namespace Nat

lemma lift_lt {a b : ℕ} (w : ℕ) : a < 2 ^ w → b < 2 ^ w → (a < b ↔ BitVec.ofNat w a < BitVec.ofNat w b) := by
  intro haw hbw
  constructor <;> intro lhs <;> simp_all
  . repeat rw [Nat.mod_eq_of_lt (by omega)]
    assumption
  . repeat rw [Nat.mod_eq_of_lt (by omega)] at lhs
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

end Word

namespace BitVec

theorem useless_signExtend {x : Fin KB} {hx : x.val < 2^12}
  : let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
  bx64 % 4 = (BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4
  := by
    extract_lets bx64
    have hx_bb : x.val < KB := x.isLt
    have hx_64 : x.val < 2^64 := by omega

    -- Now prove using bit representation
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    have h_bx64 : bx64.toNat = x.val := by
      simp [bx64, BitVec.toNat_ofNatLT]
    let bx12 : BitVec 12 := BitVec.ofNatLT x.val hx
    have h_bx12 : bx12.toNat = x.val := by
      simp [bx12, BitVec.toNat_ofNatLT]
    have h_sign_ext : (BitVec.signExtend 64 bx12).toNat % 4 = x.val % 4 := by
      simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
      split_ifs with hmsb
      · have hsub_mod : (2^64 - 2^12) % 4 = 0 := by norm_num
        rw [Nat.add_mod, hsub_mod, Nat.add_zero]
        have : bx12.toNat < 2^64 := by
          rw [h_bx12]
          exact hx_64
        rw [Nat.mod_eq_of_lt this, h_bx12, Nat.mod_mod_of_dvd]
        norm_num
      · simp [Nat.add_zero]
        have : bx12.toNat < 2^64 := by
          rw [h_bx12]
          exact hx_64
        rw [h_bx12]
    have h4 : (4 : BitVec 64).toNat = 4 := by simp
    rw [h4]
    rw [h_bx64]
    have : bx12 = BitVec.ofNatLT (w := 12) x.val hx := rfl
    rw [← this, ← h_sign_ext]

theorem useless_signExtend_add {x : Fin KB} {hx : x.val < 2^12} {y : BitVec 64}
  : let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
  (y + bx64) % 4 = (y + BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4
  := by
    extract_lets bx64
    have h_base := useless_signExtend (x := x) (hx := hx)
    simp [bx64] at h_base
    let sx := BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x.val hx)
    suffices h_suff : ∀ (a b c : BitVec 64), a % 4 = b % 4 → (c + a) % 4 = (c + b) % 4 by
      exact h_suff bx64 sx y h_base
    intro a b c h_ab
    bv_decide

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

  . have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

  . have : ((r2.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

  . have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
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

  . have : ((r1.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r1.toNat := by omega
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

  . have : ((r2.toNat : ℤ) - 18446744073709551616) % 340282366920938463463374607431768211456 = 340282366920938463444927863358058659840 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add, Int.toNat_mul]
    ring_nf
    omega

end BitVec
