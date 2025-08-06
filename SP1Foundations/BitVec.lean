import SP1Foundations.Field
import SP1Foundations.Word
import LeanRV64IM.Prelude
import LeanRV64IM.Sail.Sail

open BitVec

lemma bitVec_ofNat_toNat {w n : ℕ} : (BitVec.ofNat w n).toNat = n % 2 ^ w := by rfl

lemma bitVec_sshiftright_eq (bv : BitVec w) (shift : ℕ) :
  bv.sshiftRight shift =
    BitVec.setWidth w
      (BitVec.extractLsb ((w - 1) + shift) shift (BitVec.signExtend (w + shift) bv))
    := by grind

namespace BitVec

attribute [simp] LeanRV64IM.Functions.sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
attribute [simp] extractLsb extractLsb'

@[simp] lemma twoPow_65536_32 : 65536#32 = BitVec.twoPow 32 16 := rfl

lemma shiftLeft_xor_shiftLeft16 (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) ^^^ (c + d <<< 16) =
      (a ^^^ c) + (b ^^^ d) <<< 16 := by bv_decide

lemma shiftLeft_or_shiftLeft16 (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) ||| (c + d <<< 16) =
      (a ||| c) + (b ||| d) <<< 16 := by bv_decide

lemma shiftLeft_and_shiftLeft16 (a b c d : BitVec 32)
    (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) (hd : d < 65536) :
    (a + b <<< 16) &&& (c + d <<< 16) =
      (a &&& c) + (b &&& d) <<< 16 := by bv_decide

lemma and_add_and_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  bv_decide

lemma or_add_or_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ||| y_low) + (x_high ||| y_high) * 256 =
      (x_low + x_high * 256) ||| (y_low + y_high * 256) := by
  bv_decide

lemma xor_add_xor_mul_bv {x_low x_high y_low y_high : BitVec 32}
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low ^^^ y_low) + (x_high ^^^ y_high) * 256 =
      (x_low + x_high * 256) ^^^ (y_low + y_high * 256) := by
  bv_decide

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

lemma ofNat64_mod_4_eq_zero (n : ℕ) :
    (BitVec.ofNat 64 n) % 4 = n % 4 := rfl

theorem twoPow64_and_eq_self {a b : BitVec 64} (h : (a + b) % 4 = 0) :
    18446744073709551614#64 &&& (a + b) = a + b := by bv_decide

theorem add_mod4_eq_zero_of_mod4_eq_zero {a b : BitVec 64}
    (ha : a % 4 = 0) (hb : b % 4 = 0) : (a + b) % 4 = 0 := by bv_decide

theorem FinBB_mul4_is_BV_mul4 {x : Fin BB} : x % 4 = 0 →
    (BitVec.ofNatLT (w := 64) x (by have := x.isLt; linarith)) % 4 = 0 := by
  intro h
  have h' : x.val % 4 = 0 := by simp [Fin.mod_def] at h; exact h
  simp [BitVec.umod_def, BitVec.toNat_ofNatLT, h']

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

lemma FinBB_mul4_means_LS2B_0 (x : Fin BB) :
    let vx := (BitVec.ofNatLT (w := 64) x (by have := x.isLt; linarith))
    x % 4 = 0 → vx[0] = false ∧ vx[1] = false := by
  extract_lets vx
  intro hx
  simp [vx]
  exact mul4_means_0_1_are_0 (FinBB_mul4_is_BV_mul4 hx)

end BitVec

namespace Nat

lemma bitVec_helper_xor (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) ^^^ (bv_c + bv_d <<< 16) =
      (bv_a ^^^ bv_c) + (bv_b ^^^ bv_d) <<< 16 := by
  apply shiftLeft_xor_shiftLeft16
  all_goals simp [BitVec.lt_def]; omega

lemma bitVec_helper_or (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) ||| (bv_c + bv_d <<< 16) =
      (bv_a ||| bv_c) + (bv_b ||| bv_d) <<< 16 := by
  apply shiftLeft_or_shiftLeft16
  all_goals simp [BitVec.lt_def]; omega

lemma bitVec_helper_and (a b c d : ℕ)
    (ha : a < 2^16) (hb : b < 2^16) (hc : c < 2^16) (hd : d < 2^16) :
    let bv_a := BitVec.ofNat 32 a; let bv_b := BitVec.ofNat 32 b
    let bv_c := BitVec.ofNat 32 c; let bv_d := BitVec.ofNat 32 d
    (bv_a + bv_b <<< 16) &&& (bv_c + bv_d <<< 16) =
      (bv_a &&& bv_c) + (bv_b &&& bv_d) <<< 16 := by
  apply shiftLeft_and_shiftLeft16
  all_goals simp [BitVec.lt_def]; omega

lemma lift_lt {a b : ℕ} (w : ℕ) : a < 2 ^ w → b < 2 ^ w → (a < b ↔ BitVec.ofNat w a < BitVec.ofNat w b) := by
  intro haw hbw
  constructor <;> intro lhs <;> simp_all
  . repeat rw [Nat.mod_eq_of_lt (by omega)]
    assumption
  . repeat rw [Nat.mod_eq_of_lt (by omega)] at lhs
    assumption

end Nat

namespace Word

lemma toBitVec64_mod_of_lt (w : Word (Fin BB)) (n : Fin 8) :
    (Word.toBitVec64 w) % BitVec.twoPow 64 n.val =
      (BitVec.ofNat 64 w[0]) % BitVec.twoPow 64 n.val := by
  simp [toBitVec64, toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  simp [BitVec.twoPow]
  let k := BitVec.ofNat 64 w[0]
  show (k + _ + _ + _) % _ = k % _
  fin_cases n
  · simp only [shiftLeft_zero, umod_one] -- trivial case
  all_goals {simp only [reduceHShiftLeft]; bv_decide}

@[simp] lemma toBitVec64_mod2 (w : Word (Fin BB)) :
    (Word.toBitVec64 w) % 2#64 = (BitVec.ofNat 64 w[0]) % 2#64 :=
  toBitVec64_mod_of_lt w 1

@[simp] lemma toBitVec64_mod4 (w : Word (Fin BB)) :
    (Word.toBitVec64 w) % 4#64 = (BitVec.ofNat 64 w[0]) % 4#64 :=
  toBitVec64_mod_of_lt w 2

@[simp] lemma toBitVec64_mod8 (w : Word (Fin BB)) :
    (Word.toBitVec64 w) % 8#64 = (BitVec.ofNat 64 w[0]) % 8#64 :=
  toBitVec64_mod_of_lt w 3

@[simp] lemma toBitVec64_add_mod4 (w : Word (Fin BB)) (x : BitVec 64) :
    (Word.toBitVec64 w + x) % 4#64 = (BitVec.ofNat 64 w[0] + x) % 4#64 := by
  simp [toBitVec64, Word.toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  let k := BitVec.ofNat 64 w[0]
  show (k + _ + _ + _ + _) % 4 = (k + _) % 4
  bv_decide

@[simp] lemma add_toBitVec64_mod4 (w : Word (Fin BB)) (x : BitVec 64) :
    (x + Word.toBitVec64 w) % 4#64 = (x + BitVec.ofNat 64 w[0]) % 4#64 := by
  simp [toBitVec64, Word.toNat]
  simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  let k := BitVec.ofNat 64 w[0]
  show (_ + (k + _ + _ + _)) % 4 = (_ + k) % 4
  bv_decide

end Word

namespace BitVec

theorem useless_signExtend {x : Fin BB} {hx : x.val < 2^12}
  : let bx64 : BitVec 64 := BitVec.ofNatLT x (by linarith)
  bx64 % 4 = (BitVec.signExtend 64 (BitVec.ofNatLT (w := 12) x (by linarith))) % 4
  := by
    extract_lets bx64
    have hx_bb : x.val < BB := x.isLt
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

theorem useless_signExtend_add {x : Fin BB} {hx : x.val < 2^12} {y : BitVec 64}
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

end BitVec
