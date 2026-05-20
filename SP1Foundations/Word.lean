import SP1Foundations.Field
-- import SP1Foundations.Tactics

@[simp] notation "BYTE_DWORD_SIZE" => 16
@[simp] notation "BYTE_WORD_SIZE" => 8
@[simp] notation "BYTE_HWORD_SIZE" => 4
@[simp] notation "DWORD_SIZE" => 8
@[simp] notation "WORD_SIZE" => 4
@[simp] notation "HWORD_SIZE" => 2

@[reducible] def HWord (T : Type) := Vector T HWORD_SIZE
@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def DWord (T : Type) := Vector T DWORD_SIZE
@[reducible] def BHWord (T : Type) := Vector T BYTE_HWORD_SIZE
set_option linter.style.setOption false
set_option linter.style.longLine false

@[reducible] def BWord (T : Type) := Vector T BYTE_WORD_SIZE
@[reducible] def BDWord (T : Type) := Vector T BYTE_DWORD_SIZE

namespace BitVec

lemma setWidth_idem {m n : ℕ} {bv : BitVec m} :
  (m ≤ n) → (BitVec.setWidth n bv).toNat = bv.toNat
    := by
  intro hle; simp
  rw [Nat.mod_eq_of_lt]
  apply lt_of_lt_of_le (b := 2 ^ m)
  · unfold BitVec.toNat; apply bv.toFin.isLt
  · apply Nat.pow_le_pow_right (by simp) (by assumption)

end BitVec

open BitVec

namespace HWord

/-- Prove two `HWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : HWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1
  | n + 2, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `HWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : HWord T}
    (h : ∀ i : Fin HWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : HWord T) : w = #v[w[0], w[1]] := ext_cases rfl rfl

lemma eq_pointwise (w w' : HWord T) : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `HWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : HWord T → Prop}
    (mk : ∀ x1 x2 : T, C #v[x1, x2]) (w : HWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

def isU32 {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop :=
  ∀ i : Fin HWORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU32_of_cases {p : ℕ} [NeZero p] {w : HWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16) : w.isU32
  := by intro i; fin_cases i <;> simpa [isU32]

@[aesop unsafe forward]
lemma lt_cases_of_isU32 {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

def toNat {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16

lemma toNat_lt_of_isU32 {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32) : w.toNat < 2 ^ 32 := by
  have := lt_cases_of_isU32 hw
  unfold toNat
  omega

def toBitVec32 {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat w)

lemma toBitVec32_toNat {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU32 hw
  omega

def toBitVec64 {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 64 :=
  BitVec.signExtend 64 (toBitVec32 w)

@[grind] def isNegative {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop := w[1].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : HWord (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, toBitVec32, toNat, BitVec.msb_eq_decide]
  omega

def toInt {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

lemma toInt_lb {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32) :
  -2147483648 ≤ w.toInt := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32 is_U32_w
  unfold HWord.toInt HWord.isNegative HWord.toNat
  split_ifs <;> push_cast <;> omega

lemma toInt_ub {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32) :
  w.toInt < 2147483648 := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32 is_U32_w
  unfold HWord.toInt HWord.isNegative HWord.toNat
  split_ifs <;> push_cast <;> omega

/-- Uses `ZMod.val_injective` per limb to recover pointwise equality from
the `.val`-bound facts. -/
lemma eq_toInt_eq {p : ℕ} [NeZero p] {wx wy : HWord (ZMod p)}
    (is32_wx : wx.isU32) (is32_wy : wy.isU32) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · apply HWord.lt_cases_of_isU32 at is32_wx
    apply HWord.lt_cases_of_isU32 at is32_wy
    unfold HWord.toInt HWord.isNegative HWord.toNat; intro heq
    rw [← HWord.eq_pointwise]
    refine ⟨?_, ?_⟩ <;> apply ZMod.val_injective <;> omega

lemma toBitVec32_toInt {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    have := toNat_lt_of_isU32 h_w_isU32
    unfold toBitVec32 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat at * <;> push_cast <;> simp_all <;> omega

lemma toBitVec64_toInt {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    simp [toBitVec64, BitVec.toInt_signExtend]
    rw [toBitVec32_toInt h_w_isU32]
    unfold toInt isNegative toNat
    refine Int.bmod_eq_of_le ?_ ?_ <;> push_cast <;> omega

lemma isNegative_toInt {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (is32_w : HWord.isU32 w) :
    w.isNegative ↔ w.toInt < 0 := by
  have := lt_cases_of_isU32 is32_w
  unfold HWord.toInt HWord.isNegative HWord.toNat
  split_ifs <;> push_cast <;> omega

lemma sign_cases {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (is32_w : HWord.isU32 w) :
    w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [HWord.isNegative_toInt is32_w]
  exact Int.sign_cases w.toInt

end conversions

end HWord

namespace Word

/-- Prove two `Word`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : Word T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : Word T}
    (h : ∀ i : Fin WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : Word T) : w = #v[w[0], w[1], w[2], w[3]] := ext_cases rfl rfl rfl rfl

lemma eq_pointwise {w w' : Word T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : Word T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the `Word` is properly bounded.
Used by `SP1Constraint.toProp`. -/
def isU64 {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop :=
  ∀ i : Fin WORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU64_of_cases {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16) : w.isU64
  := by intro i; fin_cases i <;> simpa [isU64]

@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU64 {p : ℕ} [NeZero p] {w : Word (ZMod p)} (hw : w.isU64) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

/-- Common enough to want a lemma. -/
@[simp]
lemma four_isU64 {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] :
    Word.isU64 (#v[4, 0, 0, 0] : Word (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  apply Word.isU64_of_cases <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h4_val : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [h4_val]; omega
  all_goals (rw [ZMod.val_zero]; omega)

end U64

section conversions

/-- Companion to `isU64`; used by `SP1Constraint.toStateProp`. Defined
directly since the proof obligations live at the operation iff layer,
where the unfolded form is preferred. -/
def toNat {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48

/-- `toNat` is defined directly (no opaque wrapper), so this is `rfl`. -/
lemma toNat_def {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    w.toNat = w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 := rfl

lemma toNat_lt_of_isU64 {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64) : w.toNat < 2 ^ 64 := by
  have := lt_cases_of_isU64 hw
  unfold toNat
  omega

lemma eq_toNat_eq {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : wx.isU64) (is64_wy : wy.isU64) :
    wx = wy ↔ wx.toNat = wy.toNat := by
  constructor
  · simp_all
  · have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is64_wx
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is64_wy
    unfold toNat; intro heq
    rw [← Word.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ZMod.val_injective <;> omega

/-- The reconstructed vector uses `((N : ℕ) : ZMod p)` natural-cast
literals. -/
lemma toNat_reconstruct {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} {x : ℕ} (is64_w : Word.isU64 w) :
  w.toNat = x →
    w = #v[((x % 65536 : ℕ) : ZMod p), ((x / 65536 % 65536 : ℕ) : ZMod p),
           ((x / 4294967296 % 65536 : ℕ) : ZMod p),
           ((x / 281474976710656 % 65536 : ℕ) : ZMod p)] := by
  intro toNat; rw [← toNat]; clear toNat
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is64_w
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  rw [← Word.eq_pointwise]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ] <;>
    apply ZMod.val_injective
  all_goals
    rw [ZMod.val_natCast_of_lt (by omega)]
    unfold toNat
    omega

/-- Companion to `toNat`; used by `SP1Constraint.toStateProp`. -/
def toBitVec64 {p : ℕ} [NeZero p] (w : Word (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat w)

lemma toBitVec64_toNat {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU64 hw
  omega

/-- Adding a small Nat constant `k` to a Word's BitVec representation is the
same as adding `k` to the low limb, provided the low limb plus `k` fits in
17 bits (so the ZMod-level `(a + k).val = a.val + k` lift is clean). The
other limbs are unconstrained — BitVec arithmetic associativity handles the
mod 2^64 carries regardless. Used by chip-side `correct_*` proofs to bridge
`Word.toBitVec64 #v[..] + 4#64 = Word.toBitVec64 #v[low+4, ..]`
when normalizing `+ 4` between the BitVec and limb forms (e.g. PC update). -/
lemma toBitVec64_lowLimb_add_nat
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]--[Fact (2 ^ 17 < p)]
    (a b c d : ZMod p) (k : ℕ) (hak : a.val + k < p) :
    Word.toBitVec64 #v[a, b, c, d] + BitVec.ofNat 64 k =
      Word.toBitVec64 #v[a + (k : ZMod p), b, c, d] := by
  have hk_val : (k : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
  have hak_val : (a + (k : ZMod p)).val = a.val + k := by
    rw [ZMod.val_add_of_lt (by rw [hk_val]; omega), hk_val]
  simp [Word.toBitVec64, Word.toNat_def]
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      hak_val, ← Nat.add_mod]
  congr 1; ring

@[grind] def isNegative {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop := w[3].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : Word (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, toBitVec64, toNat, BitVec.msb_eq_decide]
  omega

def low {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[0], w[1]]

lemma isU64_low_isU32 {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64) : w.low.isU32 := by
  have ⟨h0, h1, _, _⟩ := lt_cases_of_isU64 hw
  intro i; fin_cases i <;> simp [low, HWord.isU32] <;> assumption

lemma low_toNat {p : ℕ} [NeZero p] {b0 b1 : ZMod p}
    (hw : HWord.isU32 #v[b0, b1]) :
    (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat = HWord.toNat #v[b0, b1] := by
  rw [Word.toBitVec64_toNat]
  · simp [Word.toNat, HWord.toNat, ZMod.val_zero]
  · apply HWord.lt_cases_of_isU32 at hw
    apply Word.isU64_of_cases <;> simp_all [ZMod.val_zero]

lemma setWidth_eq_low {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low, Word.toNat,
          HWord.toBitVec32, HWord.toNat]
    omega

def high {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[2], w[3]]

lemma isU64_high_isU32 {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64) : w.high.isU32 := by
  have ⟨_, _, h2, h3⟩ := lt_cases_of_isU64 hw
  intro i; fin_cases i <;> simp [high, HWord.isU32] <;> assumption

lemma setWidth_rshift_eq_high {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
              high, Word.toNat, HWord.toBitVec32, HWord.toNat]
    omega

def toInt {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma eq_toInt_eq {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
    wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is64_wx
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is64_wy
    unfold Word.toInt Word.isNegative Word.toNat; intro heq
    rw [← Word.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      apply ZMod.val_injective <;>
      (push_cast at heq; split_ifs at heq <;> omega)

lemma toInt_lb {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64) :
  -9223372036854775808 ≤ w.toInt := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64 is_U64_w
  unfold Word.toInt Word.isNegative Word.toNat
  split_ifs <;> push_cast <;> omega

lemma toInt_ub {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64) :
  w.toInt < 9223372036854775808 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64 is_U64_w
  unfold Word.toInt Word.isNegative Word.toNat
  split_ifs <;> push_cast <;> omega

lemma isU64_toInt {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64 w) :
    - 2 ^ 63 ≤ w.toInt ∧ w.toInt < 2 ^ 63 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64 is64_w
  unfold Word.toInt Word.isNegative Word.toNat
  split_ifs <;> push_cast <;> omega

lemma toBitVec64_toInt {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, Word.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

lemma isNegative_toInt {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64 w) :
    w.isNegative ↔ w.toInt < 0 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64 is64_w
  unfold Word.toInt Word.isNegative Word.toNat
  split_ifs <;> push_cast <;> omega

lemma sign_cases {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (is64_w : Word.isU64 w) :
    w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [Word.isNegative_toInt is64_w]
  exact Int.sign_cases w.toInt

end conversions

end Word

namespace DWord

/-- Prove two `DWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : DWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5])
    (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | n + 8, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `DWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : DWord T}
    (h : ∀ i : Fin DWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : DWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : DWord T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧ (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `DWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : DWord T → Prop}
    (mk : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : T, C #v[x1, x2, x3, x4, x5, x6, x7, x8]) (w : DWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

def isU128 {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop :=
  ∀ i : Fin DWORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU128_of_cases {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16)
    (h4 : w[4].val < 2 ^ 16) (h5 : w[5].val < 2 ^ 16)
    (h6 : w[6].val < 2 ^ 16) (h7 : w[7].val < 2 ^ 16) : w.isU128
  := by intro i; fin_cases i <;> simpa [isU128]

@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU128 {p : ℕ} [NeZero p] {w : DWord (ZMod p)} (hw : w.isU128) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 ∧
    w[4].val < 2 ^ 16 ∧ w[5].val < 2 ^ 16 ∧ w[6].val < 2 ^ 16 ∧ w[7].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7⟩

end U128

section conversions

@[aesop unsafe forward]
def toNat {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 +
  w[4].val * 2 ^ 64 + w[5].val * 2 ^ 80 + w[6].val * 2 ^ 96 + w[7].val * 2 ^ 112

def toBitVec128 {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat w)

lemma toBitVec128_toNat {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [DWord.toBitVec128, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU128 hw
  omega

@[grind] def isNegative {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop := w[7].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : DWord (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, toBitVec128, toNat, BitVec.msb_eq_decide]
  omega

def low {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

def high {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

def toInt {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 128 else w.toNat

lemma eq_toInt_eq {p : ℕ} [NeZero p] {wx wy : DWord (ZMod p)}
    (is128_wx : DWord.isU128 wx) (is128_wy : DWord.isU128 wy) :
    wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · have ⟨_, _, _, _, _, _, _, _⟩ := DWord.lt_cases_of_isU128 is128_wx
    have ⟨_, _, _, _, _, _, _, _⟩ := DWord.lt_cases_of_isU128 is128_wy
    unfold DWord.toInt DWord.isNegative DWord.toNat; intro heq
    rw [← DWord.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      apply ZMod.val_injective <;>
      (push_cast at heq; split_ifs at heq <;> omega)

lemma isU128_toInt {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128 w) :
    - 2 ^ 127 ≤ w.toInt ∧ w.toInt < 2 ^ 127 := by
  have := DWord.lt_cases_of_isU128 is128_w
  unfold DWord.toInt DWord.isNegative DWord.toNat
  split_ifs <;> push_cast <;> omega

lemma toBitVec128_toInt {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    rw [BitVec.toInt, DWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU128] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec128_toNat h_w_isU128] at * <;>
    omega

lemma isNegative_toInt {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128 w) :
    w.isNegative ↔ w.toInt < 0 := by
  have := DWord.lt_cases_of_isU128 is128_w
  unfold DWord.toInt DWord.isNegative DWord.toNat
  split_ifs <;> push_cast <;> omega

lemma sign_cases {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (is128_w : DWord.isU128 w) :
    w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [DWord.isNegative_toInt is128_w]
  exact Int.sign_cases w.toInt

end conversions

end DWord

namespace BHWord

/-- Prove two `BHWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BHWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BHWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BHWord T}
    (h : ∀ i : Fin BYTE_HWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BHWord T) : w = #v[w[0], w[1], w[2], w[3]]
  := ext_cases rfl rfl rfl rfl

lemma eq_pointwise {w w' : BHWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BHWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BHWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 : T, C #v[x0, x1, x2, x3]) (w : BHWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

def isU32 {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_HWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU32_of_cases {p : ℕ} [NeZero p] {w : BHWord (ZMod p)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256) : w.isU32
  := by intro i; fin_cases i <;> simpa [isU32]

@[aesop unsafe forward]
lemma lt_cases_of_isU32 {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} (hbhw : w.isU32) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256
    :=
  ⟨hbhw 0, hbhw 1, hbhw 2, hbhw 3⟩

end U32

section conversions

def toNat {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24

lemma toNat_lt_of_isU32 {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32) : w.toNat < 2 ^ 32 := by
  have := lt_cases_of_isU32 hw
  unfold toNat
  omega

def toBitVec32 {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat w)

lemma toBitVec32_toNat {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU32 hw
  omega

@[grind] def isNegative {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop := w[3].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, BHWord.toBitVec32, BHWord.toNat, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {p : ℕ} [NeZero p]
  {w : BHWord (ZMod p)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2 ^ 32 := by
  rw [isNegative_msb h_w_isU32]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec32_toNat h_w_isU32]
  omega

def toInt {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

lemma toBitVec32_toInt {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (h_w_isU32 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    have : w.toNat < 2 ^ 32 := toNat_lt_of_isU32 h_w_isU32
    simp_all [toBitVec32, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU32] at * <;> omega

end conversions

end BHWord

namespace BWord

/-- Prove two `BWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | n + 8, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BWord T}
    (h : ∀ i : Fin BYTE_WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : BWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7]) (w : BWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

def isU64 {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2 ^ 8

@[aesop unsafe apply]
lemma isU64_of_cases {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 8) (h1 : w[1].val < 2 ^ 8)
    (h2 : w[2].val < 2 ^ 8) (h3 : w[3].val < 2 ^ 8)
    (h4 : w[4].val < 2 ^ 8) (h5 : w[5].val < 2 ^ 8)
    (h6 : w[6].val < 2 ^ 8) (h7 : w[7].val < 2 ^ 8) : w.isU64
  := by intro i; fin_cases i <;> simpa [isU64]

@[aesop unsafe forward]
lemma lt_cases_of_isU64 {p : ℕ} [NeZero p] {w : BWord (ZMod p)} (hbw : w.isU64) :
    w[0].val < 2 ^ 8 ∧ w[1].val < 2 ^ 8 ∧ w[2].val < 2 ^ 8 ∧ w[3].val < 2 ^ 8 ∧
    w[4].val < 2 ^ 8 ∧ w[5].val < 2 ^ 8 ∧ w[6].val < 2 ^ 8 ∧ w[7].val < 2 ^ 8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

end U64

section conversions

/-- The body only uses ring operations and `OfNat`, so `[CommRing F]` is
sufficient — no `Field` hypothesis needed. -/
def toWord {F : Type} [CommRing F] (w : BWord F) : Word F :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

def toNat {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56

/-- Helper: `(a + b * 256).val = a.val + b.val * 256` when `a.val, b.val < 2^8`,
under `[Fact (2^17 < p)]`. The byte-pair packing primitive used by
`toNat_toWord`, `toWord_U64`, and downstream lemmas. -/
private lemma val_byte_combine {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b : ZMod p) (ha : a.val < 2 ^ 8) (hb : b.val < 2 ^ 8) :
    (a + b * 256).val = a.val + b.val * 256 := by
  have h256 : (256 : ZMod p).val = 256 := val_256_zmod_p
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  have hbm : (b * 256).val = b.val * 256 := by
    rw [ZMod.val_mul_of_lt]
    · rw [h256]
    · rw [h256]; omega
  rw [ZMod.val_add_of_lt, hbm]
  · rw [hbm]; omega

lemma toNat_toWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toNat = Word.toNat (w.toWord) := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  simp only [BWord.toNat, BWord.toWord, Word.toNat_def,
             Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  rw [val_byte_combine, val_byte_combine, val_byte_combine, val_byte_combine] <;> omega

lemma toWord_U64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toWord.isU64 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  simp only [toWord]
  apply Word.isU64_of_cases
  all_goals
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ]
    rw [val_byte_combine] <;> omega

def toBitVec64 {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat w)

lemma toBitVec64_toNat {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [BWord.toBitVec64, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU64 hw
  omega

lemma toWord_toBitVec64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toWord.toBitVec64 = w.toBitVec64 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_toNat (toWord_U64 h_w_isU64)]
  rw [BWord.toBitVec64_toNat h_w_isU64]
  rw [toNat_toWord h_w_isU64]

@[grind] def isNegative {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop := w[7].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BWord (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, BWord.toBitVec64, BWord.toNat, BitVec.msb_eq_decide]
  omega

def toInt {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma toBitVec64_toInt {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, BWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

def low {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

lemma isU64_low_isU32 {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64) : w.low.isU32 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 hw
  apply BHWord.isU32_of_cases <;> simp [low] <;> omega

lemma setWidth_eq_low {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  simp [toBitVec64, ← BitVec.toNat_inj, low,
        BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
  omega

def high {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

lemma isU64_high_isU32 {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64) : w.high.isU32 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 hw
  apply BHWord.isU32_of_cases <;> simp [high] <;> omega

lemma setWidth_rshift_eq_high {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
            high, BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
  omega

end conversions

end BWord

namespace BDWord

/-- Prove two `BDWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BDWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7])
    (h8 : w[8] = w'[8]) (h9 : w[9] = w'[9]) (h10 : w[10] = w'[10]) (h11 : w[11] = w'[11])
    (h12 : w[12] = w'[12]) (h13 : w[13] = w'[13]) (h14 : w[14] = w'[14]) (h15 : w[15] = w'[15]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | 8, _ => h8 | 9, _ => h9 | 10, _ => h10 | 11, _ => h11 | 12, _ => h12 | 13, _ => h13 | 14, _ => h14 | 15, _ => h15
  | n + 16, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BDWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BDWord T}
    (h : ∀ i : Fin BYTE_DWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BDWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]
  := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : BDWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ∧
    (w[8] = w'[8]) ∧ (w[9] = w'[9]) ∧ (w[10] = w'[10]) ∧ (w[11] = w'[11]) ∧
    (w[12] = w'[12]) ∧ (w[13] = w'[13]) ∧ (w[14] = w'[14]) ∧ (w[15] = w'[15])
    ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BDWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BDWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]) (w : BDWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

def isU128 {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU128_of_cases {p : ℕ} [NeZero p] {w : BDWord (ZMod p)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.isU128
  := by intro i; fin_cases i <;> simpa [isU128]

@[aesop unsafe forward]
lemma lt_cases_of_isU128 {p : ℕ} [NeZero p] {w : BDWord (ZMod p)} (hbdw : w.isU128) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256 ∧
    w[4].val < 256 ∧ w[5].val < 256 ∧ w[6].val < 256 ∧ w[7].val < 256 ∧
    w[8].val < 256 ∧ w[9].val < 256 ∧ w[10].val < 256 ∧ w[11].val < 256 ∧
    w[12].val < 256 ∧ w[13].val < 256 ∧ w[14].val < 256 ∧ w[15].val < 256
    :=
  ⟨hbdw 0, hbdw 1, hbdw 2, hbdw 3, hbdw 4, hbdw 5, hbdw 6, hbdw 7, hbdw 8, hbdw 9, hbdw 10, hbdw 11, hbdw 12, hbdw 13, hbdw 14, hbdw 15⟩

end U128

section conversions

def low {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]

lemma isU128_low_isU64 {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128) : w.low.isU64 := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128 hw
  intro i; fin_cases i <;> simp [low, BWord.isU64] <;> omega

def high {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

lemma isU128_high_isU64 {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128) : w.high.isU64 := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128 hw
  intro i; fin_cases i <;> simp [high, BWord.isU64] <;> omega

def toNat {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56 +
  w[8].val * 2 ^ 64 + w[9].val * 2 ^ 72 + w[10].val * 2 ^ 80 + w[11].val * 2 ^ 88 +
  w[12].val * 2 ^ 96 + w[13].val * 2 ^ 104 + w[14].val * 2 ^ 112 + w[15].val * 2 ^ 120

lemma toNat_lt_of_isU128 {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128) : w.toNat < 2 ^ 128 := by
  have := lt_cases_of_isU128 hw
  unfold toNat
  omega

def toBitVec128 {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat w)

lemma toBitVec128_toNat {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [BDWord.toBitVec128, BitVec.toNat_ofNat, toNat]
  have := lt_cases_of_isU128 hw
  omega

@[grind] def isNegative {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop := w[15].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BDWord (ZMod p)} : Decidable (isNegative w) := by
  unfold isNegative; infer_instance

lemma isNegative_msb {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, BDWord.toBitVec128, BDWord.toNat, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {p : ℕ} [NeZero p]
  {w : BDWord (ZMod p)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2 ^ 128 := by
  rw [isNegative_msb h_w_isU128]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec128_toNat h_w_isU128]
  omega

def toInt {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 128 else w.toNat

set_option maxRecDepth 200000

set_option maxRecDepth 200000 in
lemma toBitVec128_toInt {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    have := lt_cases_of_isU128 h_w_isU128
    have : w.toNat < 2 ^ 128 := toNat_lt_of_isU128 h_w_isU128
    simp_all [toBitVec128, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU128] at * <;> omega

lemma low_as_extract {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128) :
    (w.low).toBitVec64 = BitVec.extractLsb 63 0 (w.toBitVec128) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128 h_w_isU128
  simp [BDWord.low, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

lemma high_as_extract {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128) :
    (w.high).toBitVec64 = BitVec.extractLsb 127 64 (w.toBitVec128) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128 h_w_isU128
  simp [BDWord.high, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

end conversions

end BDWord

namespace HWord

/-- Polymorphic companion of `sign_extend_32_to_64_msb`. The 32-bit
sign extension of `HWord` `w` (viewed as `BitVec 64`) is the `Word`
whose two high limbs are `65535` if `w`'s top bit is set, else `0`. -/
lemma sign_extend_32_to_64_msb {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
    w.isU32 →
    BitVec.signExtend 64 w.toBitVec32 = Word.toBitVec64
      #v[w[0], w[1],
         if w.toBitVec32.msb = true then 65535 else 0,
         if w.toBitVec32.msb = true then 65535 else 0] := by
  intro is_U32_w
  have ⟨hw0, hw1⟩ := lt_cases_of_isU32 is_U32_w
  have hp : 2 ^ 17 < p := Fact.out
  have h_w32 : w.toBitVec32.toNat = w[0].val + w[1].val * 2 ^ 16 := by
    rw [HWord.toBitVec32_toNat is_U32_w]; simp [HWord.toNat]
  have h_w32_lt : w.toBitVec32.toNat < 2 ^ 32 := by rw [h_w32]; omega
  have h_msb_decide : w.toBitVec32.msb = decide (2 ^ 31 ≤ w.toBitVec32.toNat) := by
    simp [BitVec.msb_eq_decide]
  have h65535_val : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_natCast_of_lt (by omega)]
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_signExtend, Word.toBitVec64]
  simp only [BitVec.toNat_ofNat, if_pos (show (32 : ℕ) ≤ 64 from by omega),
    BitVec.toNat_setWidth, Word.toNat_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [Nat.mod_eq_of_lt (show w.toBitVec32.toNat < 2 ^ 64 from by omega), h_w32]
  by_cases h_msb : w.toBitVec32.msb = true
  · have h_msb_nat : (2 ^ 31 : ℕ) ≤ w[0].val + w[1].val * 2 ^ 16 := by
      rw [h_msb_decide] at h_msb; rw [h_w32] at h_msb; simpa using h_msb
    simp only [h_msb, if_true, h65535_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [Bool.not_eq_true] at h_msb
    have h_msb_nat : w[0].val + w[1].val * 2 ^ 16 < 2 ^ 31 := by
      rw [h_msb_decide] at h_msb; rw [h_w32] at h_msb; simpa using h_msb
    simp only [h_msb, Bool.false_eq_true, if_false, h0_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Sign-extends a 32-bit `HWord` to a 64-bit `Word` (when `sgn = true`);
zero-extends otherwise. -/
def extend {p : ℕ} [NeZero p] (w : HWord (ZMod p)) (sgn : Bool) : Word (ZMod p) :=
  let ext := (if sgn then (if w.isNegative then (1 : ZMod p) else 0) else 0) * 65535
  #v[w[0], w[1], ext, ext]

lemma extend_U32_U64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} (is_U32_w : w.isU32) (sgn : Bool) :
    (w.extend sgn).isU64 := by
  have ⟨_, _⟩ := lt_cases_of_isU32 is_U32_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply Word.isU64_of_cases <;>
    simp [extend] <;> (try split_ifs) <;>
    (try simp [h65535, h0]) <;> omega

/-- Mirrors `Word.extend_true_is_signExtend`'s recipe at smaller
dimension via `BitVec.toInt_inj` + `HWord.toBitVec32_toInt` /
`Word.toBitVec64_toInt`. -/
lemma extend_true_is_signExtend {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
  w.isU32 →
  (w.extend true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32
    := by
  set sw := extend w true
  intro is_U32_w
  have ⟨_, _⟩ := lt_cases_of_isU32 is_U32_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have is_U64_hw : sw.isU64 := by
    subst sw; simp [extend]
    apply Word.isU64_of_cases <;> split_ifs <;>
      simp [h65535, h0] <;> omega
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, Word.isNegative]
    by_cases h : 32768 ≤ w[1].val <;> simp [h, h65535, h0]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [HWord.toBitVec32_toInt is_U32_w,
      Word.toBitVec64_toInt is_U64_hw]
  rw [HWord.toInt, Word.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, Word.toNat, HWord.toNat] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h65535, h0]) <;>
  push_cast <;> omega

lemma extend_false_is_setWidth {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
  w.isU32 →
  (w.extend false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32
    := by
  set sw := extend w false
  intro is_U32_w
  have ⟨_, _⟩ := lt_cases_of_isU32 is_U32_w
  have is_U64_hw : sw.isU64 := by
    subst sw; simp [extend]
    apply Word.isU64_of_cases <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_toNat is_U64_hw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [HWord.toBitVec32_toNat is_U32_w]
  simp [sw, Word.toNat, extend, HWord.toNat]

end HWord

namespace Word

/-- Decomposes each 16-bit limb into low/high bytes via `.val`-level
arithmetic (since `/` on `ZMod p` is field-division, not byte-extraction). -/
def toBWord {p : ℕ} [NeZero p] (w : Word (ZMod p)) : BWord (ZMod p) :=
  #v[((w[0].val % 256 : ℕ) : ZMod p), ((w[0].val / 256 : ℕ) : ZMod p),
     ((w[1].val % 256 : ℕ) : ZMod p), ((w[1].val / 256 : ℕ) : ZMod p),
     ((w[2].val % 256 : ℕ) : ZMod p), ((w[2].val / 256 : ℕ) : ZMod p),
     ((w[3].val % 256 : ℕ) : ZMod p), ((w[3].val / 256 : ℕ) : ZMod p)]

lemma toBWord_toU64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toBWord.isU64 := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  apply BWord.isU64_of_cases <;> simp [toBWord] <;>
    (rw [Nat.mod_eq_of_lt (show _ < p by omega)]; omega)

lemma toNat_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toNat = BWord.toNat (w.toBWord) := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  simp only [toNat_def, toBWord, BWord.toNat]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  repeat rw [ZMod.val_natCast_of_lt (show _ < p by omega)]
  omega

lemma isNegative_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.isNegative ↔ BWord.isNegative (w.toBWord) := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  simp only [isNegative, BWord.isNegative, toBWord]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (show w[3].val / 256 < p by omega)]
  omega

lemma toBitVec64_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64) :
    w.toBWord.toBitVec64 = w.toBitVec64 := by
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_toNat (toBWord_toU64 h_w_isU64)]
  rw [Word.toBitVec64_toNat h_w_isU64]
  rw [toNat_toBWord h_w_isU64]

def extend {p : ℕ} [NeZero p] (w : Word (ZMod p)) (sgn : Bool) : DWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative then (1 : ZMod p) else 0) else 0) * 65535
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

lemma extend_U64_U128 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (is_U64_w : w.isU64) (sgn : Bool) :
    (w.extend sgn).isU128 := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply DWord.isU128_of_cases <;>
    simp [extend] <;> (try split_ifs) <;>
    (try simp [h65535, h0]) <;> omega

lemma extend_false_is_setWidth {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64 →
  (w.extend false).toBitVec128 = BitVec.setWidth 128 w.toBitVec64
    := by
  set sw := extend w false
  intro is_U64_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  have is_U128_bdw : sw.isU128 := by
    subst sw; simp [extend]
    apply DWord.isU128_of_cases <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [DWord.toBitVec128_toNat is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [Word.toBitVec64_toNat is_U64_w]
  simp [sw, DWord.toNat, extend, Word.toNat]

-- Earlier proof routed everything through `BitVec.toNat_signExtend` and a
-- `simp only` chain over `BitVec.setWidth`, tripping the kernel's `whnf`
-- re-check (deep recursion); the refactor below splits on
-- `w.isNegative` first and dispatches each case to one of the two
-- structural rewrites of `BitVec.signExtend` (`signExtend_eq_setWidth_of_msb_false`
-- / `signExtend_eq_not_setWidth_not_of_msb_true`), bringing the goal back
-- to a `setWidth`-shaped equality that `extend_false_is_setWidth` (or
-- a parallel computation in the negative case) closes. This keeps the
-- elaborated proof term shallow enough that the kernel re-checks without
-- `set_option debug.skipKernelTC`. See `docs/SKIP_KERNEL_TC.md` for prior
-- history.
lemma extend_true_is_signExtend {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64 →
  (w.extend true).toBitVec128 = BitVec.signExtend 128 w.toBitVec64
    := by
  intro is_U64_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  by_cases h : w.isNegative
  · -- negative case: signExtend = ~~~ setWidth (~~~ x); compute both toNats
    rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true
        ((Word.isNegative_msb is_U64_w).mp h)]
    have is_U128_sw : (w.extend true).isU128 := by
      simp [extend]
      apply DWord.isU128_of_cases <;> split_ifs <;>
        simp [h65535, h0] <;> omega
    rw [← BitVec.toNat_inj, DWord.toBitVec128_toNat is_U128_sw]
    simp [extend, DWord.toNat, Word.toNat, h, h65535, h0,
          BitVec.toNat_not, BitVec.toNat_setWidth,
          Word.toBitVec64_toNat is_U64_w]
    omega
  · -- non-negative case: extend w true = extend w false in this
    -- branch, and signExtend = setWidth, so reduce to extend_false case.
    have hmsb : w.toBitVec64.msb = false :=
      Bool.not_eq_true _ |>.mp (fun hm => h ((Word.isNegative_msb is_U64_w).mpr hm))
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
    have heq : w.extend true = w.extend false := by
      simp [extend, h]
    rw [heq]
    exact extend_false_is_setWidth is_U64_w

end Word

namespace BWord

def extend {p : ℕ} [NeZero p] (w : BWord (ZMod p)) (sgn : Bool) : BDWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative then (1 : ZMod p) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], ext, ext, ext, ext, ext, ext, ext, ext]

lemma extend_U64_U128 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (is_U64_w : w.isU64) (sgn : Bool) :
    (w.extend sgn).isU128 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply BDWord.isU128_of_cases <;>
    simp [extend] <;> (try split_ifs) <;>
    (try simp [h255, h0]) <;> omega

lemma extend_false_is_setWidth {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64 →
  (w.extend false).toBitVec128 = BitVec.setWidth 128 w.toBitVec64
    := by
  set sw := extend w false
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  have is_U128_bdw : sw.isU128 := by
    subst sw; simp [extend]
    apply BDWord.isU128_of_cases <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [BDWord.toBitVec128_toNat is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BWord.toBitVec64_toNat is_U64_w]
  simp [sw, BDWord.toNat, extend, BWord.toNat]

-- Mirrors the `Word.extend_true_is_signExtend` refactor: case-split on
-- `w.isNegative`, dispatch each case via `signExtend_eq_setWidth_of_msb_false`
-- / `signExtend_eq_not_setWidth_not_of_msb_true`, and reduce the
-- non-negative case to `extend_false_is_setWidth`. Avoids the
-- `BitVec.toNat_signExtend` chain that previously tripped the kernel
-- "deep recursion" re-check on the 8-limb BWord structure.
lemma extend_true_is_signExtend {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64 →
  (w.extend true).toBitVec128 = BitVec.signExtend 128 w.toBitVec64
    := by
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  by_cases h : w.isNegative
  · rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true
        ((BWord.isNegative_msb is_U64_w).mp h)]
    have is_U128_sw : (w.extend true).isU128 := by
      simp [extend]
      apply BDWord.isU128_of_cases <;> split_ifs <;>
        simp [h255, h0] <;> omega
    rw [← BitVec.toNat_inj, BDWord.toBitVec128_toNat is_U128_sw]
    simp [extend, BDWord.toNat, BWord.toNat, h, h255, h0,
          BitVec.toNat_not, BitVec.toNat_setWidth,
          BWord.toBitVec64_toNat is_U64_w]
    omega
  · have hmsb : w.toBitVec64.msb = false :=
      Bool.not_eq_true _ |>.mp (fun hm => h ((BWord.isNegative_msb is_U64_w).mpr hm))
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
    have heq : w.extend true = w.extend false := by
      simp [extend, h]
    rw [heq]
    exact extend_false_is_setWidth is_U64_w

lemma low_as_setWidth {p : ℕ} [NeZero p] {w : BWord (ZMod p)} :
  w.isU64 →
  w.low.toBitVec32 = BitVec.setWidth 32 w.toBitVec64
    := by
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64 is_U64_w
  simp [BWord.low, BHWord.toBitVec32, BHWord.toNat,
        BWord.toBitVec64, BWord.toNat]
  simp [← BitVec.toNat_inj]
  omega

end BWord

namespace BHWord

def extend {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) (sgn : Bool) : BWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative then (1 : ZMod p) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

/-- Mirrors `BWord.extend_U64_U128`'s recipe at smaller dimension. -/
lemma extend_U32_U64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} (is_U32_w : w.isU32) (sgn : Bool) :
    (w.extend sgn).isU64 := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32 is_U32_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply BWord.isU64_of_cases <;>
    simp [extend] <;> (try split_ifs) <;>
    (try simp [h255, h0_val]) <;> omega

/-- Mirrors `BWord.extend_true_is_signExtend`'s recipe at smaller
dimension via `BitVec.toInt_inj` + `BHWord.toBitVec32_toInt` /
`BWord.toBitVec64_toInt`. -/
lemma extend_true_is_signExtend {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} :
  w.isU32 →
  (w.extend true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32
    := by
  set sw := extend w true
  intro is_U32_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32 is_U32_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have is_U64_bhw : sw.isU64 := by
    subst sw; simp [extend]
    apply BWord.isU64_of_cases <;> split_ifs <;>
      simp [h255, h0_val] <;> omega
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, BWord.isNegative]
    by_cases h : 128 ≤ w[3].val <;> simp [h, h255, h0_val]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [BHWord.toBitVec32_toInt is_U32_w,
      BWord.toBitVec64_toInt is_U64_bhw]
  rw [BHWord.toInt, BWord.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, BWord.toNat, BHWord.toNat] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h255, h0_val]) <;>
  push_cast <;> omega

lemma extend_false_is_setWidth {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} :
  w.isU32 →
  (w.extend false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32
    := by
  set sw := extend w false
  intro is_U32_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32 is_U32_w
  have is_U64_bhw : sw.isU64 := by
    subst sw; simp [extend]
    apply BWord.isU64_of_cases <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_toNat is_U64_bhw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BHWord.toBitVec32_toNat is_U32_w]
  simp [sw, BWord.toNat, extend, BHWord.toNat]

end BHWord

section Bitwise

namespace Word

lemma and_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64 → b.isU64 →
    a.toBitVec64 &&& b.toBitVec64 =
      a.toBWord.toBitVec64 &&& b.toBWord.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord h_a_64, Word.toBitVec64_toBWord h_b_64]

lemma or_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64 → b.isU64 →
    a.toBitVec64 ||| b.toBitVec64 =
      a.toBWord.toBitVec64 ||| b.toBWord.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord h_a_64, Word.toBitVec64_toBWord h_b_64]

lemma xor_toBWord {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64 → b.isU64 →
    a.toBitVec64 ^^^ b.toBitVec64 =
      a.toBWord.toBitVec64 ^^^ b.toBWord.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord h_a_64, Word.toBitVec64_toBWord h_b_64]

end Word

end Bitwise

lemma shiftRight_eq_sub_mod (x : ℕ) {n : ℕ} :
    x >>> n = (x - (x % 2 ^ n)) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_sub_mod_div

/-- Branch-target limb range check `(x * 4⁻¹).val < 16384` in `ZMod p`
lifts to `x.val < 65536`. -/
lemma lt_65536_of_mul_inv_4_lt {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (x : ZMod p) (h : (x * (4 : ZMod p)⁻¹).val < 16384) :
    x.val < 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p).val = 4 := val_4_zmod_p
    intro hz; rw [hz, ZMod.val_zero] at this; omega
  have hinv : x * (4 : ZMod p)⁻¹ * 4 = x := by field_simp
  have h4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  apply_fun ZMod.val at hinv
  rw [ZMod.val_mul, h4] at hinv
  have hp : 2 ^ 17 < p := Fact.out
  have hbound : (x * (4 : ZMod p)⁻¹).val * 4 < 65536 := by omega
  have : (x * (4 : ZMod p)⁻¹).val * 4 % p = (x * (4 : ZMod p)⁻¹).val * 4 :=
    Nat.mod_eq_of_lt (by omega)
  rw [this] at hinv
  omega

/-- The byte-slice of an 8-bit `ofNat` equals itself modulo 256. -/
lemma bitVec_ofNat8_eq_of_mod (a b : ℕ) (h : a % 256 = b % 256) :
    BitVec.ofNat 8 a = BitVec.ofNat 8 b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simpa using h

lemma signExtend64_ofNat8_of_ge_128 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (x : ZMod p) (hlt : x.val < 256) (hge : 128 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x + 65280, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h65280 : (65280 : ZMod p).val = 65280 := by
    have : (65280 : ZMod p).val = 65280 % p := by
      rw [show (65280 : ZMod p) = ((65280 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hxk_lt : x.val + (65280 : ZMod p).val < p := by rw [h65280]; omega
  have hxk_val : (x + 65280 : ZMod p).val = x.val + 65280 := by
    rw [ZMod.val_add_of_lt hxk_lt, h65280]
  rw [hxk_val, h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

lemma nat_decomp_of_inv8_decomp {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (lo hi x : ZMod p)
    (h : lo + hi * (2 ^ 8 : ZMod p) = x)
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    x.val = lo.val + hi.val * 256 := by
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h256 : ((2 ^ 8 : ZMod p).val = 256) := by
    have h1 : (2 ^ 8 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hmul : (hi * (2 ^ 8 : ZMod p)).val = hi.val * 256 := by
    rw [ZMod.val_mul, h256, Nat.mod_eq_of_lt (by
      have : hi.val * 256 < 256 * 256 := by
        have : hi.val * 256 ≤ 255 * 256 := Nat.mul_le_mul_right _ (by omega); omega
      omega)]
  have hadd : (lo + hi * (2 ^ 8 : ZMod p)).val = lo.val + hi.val * 256 := by
    rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]
  rw [← h, hadd]

lemma setWidth64_ofNat8 {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 256) :
    BitVec.setWidth 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

lemma signExtend64_ofNat8_of_lt_128 {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 256) (hge : x.val < 128) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- toNat of `hi ++ lo` as bytes equals `(hi.toNat) * 256 + (lo.toNat)`. Specialized form. -/
private lemma toNat_append_bytes (hi lo : BitVec 8) :
    (hi ++ lo).toNat = hi.toNat * 256 + lo.toNat := by
  rw [BitVec.toNat_append]
  have hlo : lo.toNat < 2 ^ 8 := lo.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hlo, Nat.shiftLeft_eq]

private lemma toNat_concat_halfword_bytes {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) :
    (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat = x.val := by
  rw [toNat_append_bytes, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h256 : (2 ^ 8 : ℕ) = 256 := rfl
  rw [h256]
  omega

lemma setWidth64_ofNat16_concat {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

lemma signExtend64_ofNat16_concat_of_lt_32768 {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) (hmsb : x.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes x hlt]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 15
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

lemma signExtend64_ofNat16_concat_of_ge_32768 {p : ℕ} [NeZero p]
    [Fact (2 ^ 17 < p)]
    (x : ZMod p) (hlt : x.val < 65536) (hmsb : 32768 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes x hlt]
    simp only [decide_eq_true_eq]
    change 2 ^ 15 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
      omega
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + (2 ^ 64 - 2^(8 + 8)) = x.val + 65535 * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

private lemma toNat_concat_word_bytes {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat =
      x.val + y.val * 65536 := by
  have hx_hi : x.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_hi : y.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hx_decomp : x.val % 256 + (x.val >>> 8) * 256 = x.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_decomp : y.val % 256 + (y.val >>> 8) * 256 = y.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat,
    show (2 ^ 8 : ℕ) = 256 from rfl]
  have hx_hi_mod : x.val >>> 8 % 256 = x.val >>> 8 := Nat.mod_eq_of_lt hx_hi
  have hy_hi_mod : y.val >>> 8 % 256 = y.val >>> 8 := Nat.mod_eq_of_lt hy_hi
  rw [hx_hi_mod, hy_hi_mod]
  rw [show y.val >>> 8 <<< 8 ||| y.val % 256 = y.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  rw [show y.val <<< 8 ||| x.val >>> 8 = y.val * 256 + x.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hx_hi, Nat.shiftLeft_eq]]
  rw [show (y.val * 256 + x.val >>> 8) <<< 8 ||| x.val % 256 =
      (y.val * 256 + x.val >>> 8) * 256 + x.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := hx_decomp
  omega

lemma setWidth64_ofNat32_concat {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

lemma signExtend64_ofNat32_concat_of_lt_32768 {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : y.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 31
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

lemma signExtend64_ofNat32_concat_of_ge_32768 {p : ℕ} [NeZero p]
    [Fact (2 ^ 17 < p)]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : 32768 ≤ y.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_true_eq]
    change 2 ^ 31 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + y.val * 2 ^ 16 + (2 ^ 64 - 2^(8 + 8 + 8 + 8)) =
       x.val + y.val * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

section getByte

namespace BitVec

def getByte {n : ℕ} (bv : BitVec n) (i : ℕ) : ℕ := (bv.extractLsb (i * 8 + 7) (i * 8)).toNat

lemma getByte_is_byte : getByte bv i < 256 := by simp [getByte]; omega

end BitVec

end getByte

section cross_product

def cp {p : ℕ} [NeZero p] {n : ℕ} (a b : Vector (ZMod p) n) (k : ℕ) (hk : k < n) : ZMod p :=
  let product := ((Vector.ofFn (fun i => a.get ⟨i.val, by omega⟩ * b.get ⟨k - i.val, by
                     have h : i.val < (k + 1) := i.isLt
                     omega⟩)) : Vector (ZMod p) (k + 1)).toList
  product.foldl (· + ·) 0

end cross_product
