import Mathlib

abbrev BabyBearPrime : ℕ := 2013265921

lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := by
  -- norm_num doesn't work on OSX?
  sorry

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance

lemma fin_val_simp {n : ℕ} (Hlt : n < BabyBearPrime) :
  (@Fin.val BabyBearPrime (@OfNat.ofNat.{0} BabyBear n (@Fin.instOfNat BabyBearPrime instNeZeroNatBabyBearPrime n))) = n := by
  simp [BabyBearPrime, OfNat.ofNat] at *; assumption

abbrev base := 65536

structure U16 where
  val : BabyBear
  in_range : val < base

instance : Add U16 where
  add a b := sorry

abbrev WORD_SIZE := 2

abbrev Word (T : Type) := Vector T WORD_SIZE

def Word.toUInt32_BB (w : Word BabyBear) : UInt32 :=
  UInt32.ofNat (w[0] + w[1] * base)

def Word.toUInt32_U16 (w : Word U16) : UInt32 :=
  UInt32.ofNatLT (w[0].val + w[1].val * base) (by
    let wn0 : Nat := w[0].val.val
    let wn1 : Nat := w[1].val.val
    show wn0 + wn1 * base < UInt32.size
    have wn0_in_range : wn0 < base := w[0].in_range
    have wn1_in_range : wn1 < base := w[1].in_range
    simp [UInt32.size, base] at *
    omega)

structure AddOperation where
  value : Word U16

def AddOperation.spec
  (cols : AddOperation)
  (a : Word U16)
  (b : Word U16) : Prop :=
    a.toUInt32_U16 + b.toUInt32_U16 = cols.value.toUInt32_U16

def AddOperation.constraints
    (cols : AddOperation)
    (a : Word U16)
    (b : Word U16) : Prop :=
  /- let carry0 : BabyBear := 0 -/
  /- let carry1 := (a[0].val + b[0].val - cols.value[0].val + carry0) * 2013235201 -/
  /- let carry2 := (a[1].val + b[1].val - cols.value[1].val + carry1) * 2013235201 -/
  /- -- actual constraints -/
  /- carry1 * (carry1 - 1) = 0 ∧ -/
  /- carry2 * (carry2 - 1) = 0 -/
    (((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201) * (((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201) - 1)) = 0 ∧
    (((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) * (((((a[1].val + b[1].val) - cols.value[1].val) + ((((a[0].val + b[0].val) - cols.value[0].val) + 0) * 2013235201)) * 2013235201) - 1)) = 0

-- this may be wrong!
theorem split_add_mod
  {a b c : ℕ}
  {ha : a < UInt32.size}
  {hb : b < UInt32.size}
  {hc : c < UInt32.size}
  : (a + b) % UInt32.size = c % UInt32.size
  → UInt32.ofNatLT a ha + UInt32.ofNatLT b hb = UInt32.ofNatLT c hc :=
    by
      intro wrap_add
      by_cases h_sum : a + b < UInt32.size
      · rw [←(UInt32.ofNatLT_add h_sum)]
        rw [(UInt32.ofNatLT_eq_ofNat (a + b)), (UInt32.ofNatLT_eq_ofNat c)]
        refine UInt32.ext ?_
        simpa
      · rw [UInt32.ext_iff]
        simp
        refine wrap_add.trans ?_
        exact Nat.mod_eq_of_lt hc


theorem AddOperation.correct (cols : AddOperation)
  (a : Word U16)
  (b : Word U16)
  : cols.constraints a b → cols.spec a b :=
    by
      intro ⟨q1, q2⟩
      simp at *
      show a.toUInt32_U16 + b.toUInt32_U16 = cols.value.toUInt32_U16
      let an0 : ℕ := a[0].val.val
      let an0_in_range : an0 < base := a[0].in_range
      let an1 : ℕ := a[1].val.val
      let an1_in_range : an1 < base := a[1].in_range
      let bn0 : ℕ := b[0].val.val
      let bn0_in_range : bn0 < base := b[0].in_range
      let bn1 : ℕ := b[1].val.val
      let bn1_in_range : bn1 < base := b[1].in_range
      let cn0 : ℕ := cols.value[0].val.val
      let cn0_in_range : cn0 < base := cols.value[0].in_range
      let cn1 : ℕ := cols.value[1].val.val
      let cn1_in_range : cn1 < base := cols.value[1].in_range
      simp only [Word.toUInt32_U16]
      apply split_add_mod
-- ⊢ (↑a[0].val + ↑a[1].val * base + (↑b[0].val + ↑b[1].val * base)) % 32 =
--   (↑cols.value[0].val + ↑cols.value[1].val * base) % 32
      show (an0 + an1 * base + (bn0 + bn1 * base)) % UInt32.size = (cn0 + cn1 * base) % UInt32.size
      simp [UInt32.size, base] at *
      cases q1 <;> cases q2
      · omega
      · omega
      · omega
      · omega
