import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # `AddwOperation` — the arithmetic core (`RawSpec` + carry-chain lemmas)

Two-limb carry-bool + range form `RawSpec`; `addwSemantics_of_carries` (forward) and
`carries_of_addwSemantics` (backward) are the soundness/completeness keystones, applying
`toBitVec64_signExtend_word`. Faithful to `sp1/crates/core/machine/src/operations/addw.rs`. -/

namespace SP1Clean.AddwOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The carry-bool + low-limb-range form of the two-limb add chain, against the witnessed
low limbs `cols.value[0]`, `cols.value[1]`. -/
def RawSpec (a b : Word (ZMod p)) (cols : Columns (ZMod p)) : Prop :=
  let c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * 65536⁻¹
  (c0 = 0 ∨ c0 = 1) ∧ (c1 = 0 ∨ c1 = 1) ∧
  cols.value[0].val < 65536 ∧ cols.value[1].val < 65536

set_option maxHeartbeats 16000000 in
/-- Forward (soundness) core: the two-limb carry chain + the sign bit imply the reconstructed
result is a 64-bit value equal to the sign extension of the low-32 add. -/
theorem addwSemantics_of_carries {a b : Word (ZMod p)} {cols : Columns (ZMod p)}
    (ha : a.isU64) (hb : b.isU64) (h_raw : RawSpec a b cols)
    (h_msb : cols.msb.msb = if cols.value[1].val ≥ 32768 then 1 else 0) :
    (resultWord cols).isU64 ∧
    Word.toBitVec64 (resultWord cols) =
      (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)).signExtend 64 := by
  obtain ⟨hc0, hc1, hv0, hv1⟩ := h_raw
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
  simp only [ZMod.val_zero, add_zero] at n0
  have hmsb_lt : (cols.msb.msb * 65535 : ZMod p).val < 2 ^ 16 := by
    rw [h_msb]; split_ifs with h
    · rw [one_mul, val_65535_zmod_p]; omega
    · rw [zero_mul, ZMod.val_zero]; omega
  have h_isU64_v : (resultWord cols).isU64 :=
    Word.isU64_of_cases hv0 hv1 hmsb_lt hmsb_lt
  refine ⟨h_isU64_v, ?_⟩
  have hX : (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)).toNat
      = cols.value[0].val + cols.value[1].val * 2 ^ 16 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, Word.toBitVec64_toNat ha,
        Word.toBitVec64_toNat hb, Word.toNat_def, Word.toNat_def]
    omega
  exact toBitVec64_signExtend_word (resultWord cols)
    (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)) cols.msb.msb
    hv0 hv1 h_msb rfl rfl hX

set_option maxHeartbeats 16000000 in
/-- Backward (completeness) core — the converse of `addwSemantics_of_carries`: a 64-bit value equal to
the sign extension of the low-32 add witnesses the unique boolean carry chain + ranges **and** the sign
bit. Needed because `AddwOperation` is a `FormalAssertion` (its completeness must reconstruct the U16MSB
sub-assertion's `Spec` from the semantic add Spec). -/
theorem carries_of_addwSemantics {a b : Word (ZMod p)} {cols : Columns (ZMod p)}
    (ha : a.isU64) (hb : b.isU64)
    (hU : (resultWord cols).isU64)
    (hbv : Word.toBitVec64 (resultWord cols)
      = (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)).signExtend 64) :
    RawSpec a b cols ∧ cols.msb.msb = if cols.value[1].val ≥ 32768 then 1 else 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hv0, hv1, hm2, _⟩ := Word.lt_cases_of_isU64 hU
  simp only [resultWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hv0 hv1 hm2
  set v0 := cols.value[0] with hv0def
  set v1 := cols.value[1] with hv1def
  set m := cols.msb.msb with hmdef
  -- `M` is made an *opaque* variable (not a `set`/`let`): the kernel must never reduce `(m*65535).val`
  -- through `ZMod`'s `Nat.rec`-based multiplication (it deep-recurses), so we generalize it away.
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, (m * 65535 : ZMod p).val = M := ⟨_, rfl⟩
  have hm2' : M < 2 ^ 16 := hMdef ▸ hm2
  -- the operand low-32 sum (mod 2^32)
  have hsum32 : (Word.toBitVec64 a + Word.toBitVec64 b).toNat % 2 ^ 32
      = (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 := by
    rw [BitVec.toNat_add, Word.toBitVec64_toNat ha, Word.toBitVec64_toNat hb,
        Word.toNat_def, Word.toNat_def]
    omega
  -- the big nat equation from `hbv`, with the sign-extension correction left as an `if`
  have hbvN : v0.val + v1.val * 2 ^ 16 + M * 2 ^ 32 + M * 2 ^ 48
      = (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32
        + (if (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)).msb = true
            then (2 ^ 64 - 2 ^ 32 : ℕ) else 0) := by
    have h := congrArg BitVec.toNat hbv
    rw [Word.toBitVec64_toNat hU, Word.toNat_def, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
        BitVec.toNat_setWidth] at h
    simp only [resultWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ← hv0def, ← hv1def, ← hmdef, hMdef] at h
    rw [h, Nat.mod_eq_of_lt (a := (Word.toBitVec64 a + Word.toBitVec64 b).toNat % 2 ^ 32)
      (by have := Nat.mod_lt (Word.toBitVec64 a + Word.toBitVec64 b).toNat (show 0 < 2 ^ 32 by norm_num); omega),
      hsum32]
  -- the carry chain (from the low-32 relation), lifted to `ZMod`
  have hcarries : v0.val + v1.val * 2 ^ 16
      = (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 → RawSpec a b cols := by
    intro hlow
    set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
    set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
    have hq0 : q0 ≤ 1 := by rw [hq0_def]; omega
    have hq1 : q1 ≤ 1 := by rw [hq1_def]; omega
    have e0n : a[0].val + b[0].val = v0.val + q0 * 65536 := by rw [hq0_def]; omega
    have e1n : a[1].val + b[1].val + q0 = v1.val + q1 * 65536 := by rw [hq1_def]; omega
    have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ val_65536_ne_zero
    have hc0_lift : (a[0] : ZMod p) + b[0] = v0 + (q0 : ZMod p) * 65536 := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
      push_cast at hcast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
      rw [hv0def]; linear_combination hcast
    have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p) = v1 + (q1 : ZMod p) * 65536 := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
      push_cast at hcast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
      rw [hv1def]; linear_combination hcast
    have hc0_eq : (a[0] + b[0] - v0) * (65536 : ZMod p)⁻¹ = (q0 : ZMod p) := by
      have h : a[0] + b[0] - v0 = (q0 : ZMod p) * 65536 := by linear_combination hc0_lift
      rw [h, mul_assoc, h65inv, mul_one]
    have hc1_eq : (a[1] + b[1] - v1 + (a[0] + b[0] - v0) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹
        = (q1 : ZMod p) := by
      rw [hc0_eq]
      have h : a[1] + b[1] - v1 + (q0 : ZMod p) = (q1 : ZMod p) * 65536 := by linear_combination hc1_lift
      rw [h, mul_assoc, h65inv, mul_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (a[0] + b[0] - cols.value[0]) * 65536⁻¹ = 0 ∨ (a[0] + b[0] - cols.value[0]) * 65536⁻¹ = 1
      rw [← hv0def, hc0_eq]; interval_cases q0 <;> simp
    · show (a[1] + b[1] - cols.value[1] + (a[0] + b[0] - cols.value[0]) * 65536⁻¹) * 65536⁻¹ = 0 ∨ _ = 1
      rw [← hv0def, ← hv1def, hc1_eq]; interval_cases q1 <;> simp
    · rw [← hv0def]; omega
    · rw [← hv1def]; omega
  -- split on the sign bit
  by_cases hcond : (BitVec.setWidth 32 (Word.toBitVec64 a + Word.toBitVec64 b)).msb = true
  · rw [if_pos hcond] at hbvN
    have hmsbge : 2 ^ 31 ≤ (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 := by
      have h := hcond
      rw [BitVec.msb_eq_decide, decide_eq_true_eq, BitVec.toNat_setWidth, hsum32] at h
      exact h
    have hlow : v0.val + v1.val * 2 ^ 16
        = (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 := by omega
    have hge : v1.val ≥ 32768 := by omega
    refine ⟨hcarries hlow, ?_⟩
    rw [if_pos hge]
    have hMval : M = 65535 := by omega
    have hvaleq : (m * 65535 : ZMod p).val = (65535 : ZMod p).val := by
      rw [hMdef, hMval, val_65535_zmod_p]
    have hmul : m * 65535 = (1 : ZMod p) * 65535 := by rw [one_mul]; exact (ZMod.val_injective _) hvaleq
    exact mul_right_cancel₀ val_65535_ne_zero hmul
  · rw [if_neg hcond] at hbvN
    have hmsblt : (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 < 2 ^ 31 := by
      have h := hcond
      rw [BitVec.msb_eq_decide, decide_eq_true_eq, BitVec.toNat_setWidth, hsum32] at h
      omega
    have hlow : v0.val + v1.val * 2 ^ 16
        = (a[0].val + b[0].val + (a[1].val + b[1].val) * 2 ^ 16) % 2 ^ 32 := by omega
    have hlt : ¬ v1.val ≥ 32768 := by omega
    refine ⟨hcarries hlow, ?_⟩
    rw [if_neg hlt]
    have hMval : M = 0 := by omega
    have hvaleq : (m * 65535 : ZMod p).val = (0 : ZMod p).val := by
      rw [hMdef, hMval, ZMod.val_zero]
    have hmul : m * 65535 = (0 : ZMod p) * 65535 := by rw [zero_mul]; exact (ZMod.val_injective _) hvaleq
    exact mul_right_cancel₀ val_65535_ne_zero hmul

end SP1Clean.AddwOperation
