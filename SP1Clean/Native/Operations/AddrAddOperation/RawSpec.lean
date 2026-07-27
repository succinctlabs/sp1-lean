import SP1Clean.Math.Word
import SP1Clean.Extracted.AddrAddOperation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # `AddrAddOperation` — the arithmetic core (`RawSpec` + carry-chain lemmas)

The structural carry-bool + limb-range form `RawSpec` for the 48-bit (3-limb) address add, and the
two native carry-chain theorems the gadget's soundness/completeness route through:
`addrAddSemantics_of_carries` (forward) and `carries_of_addrAddSemantics` (backward). The high carry
runs against `0` (the result keeps only 48 bits); its booleanity is exactly what the address-fits
side condition supplies in the backward direction. The hand-maintained native circuit (`Inputs` + `main` +
`elaborated`) lives in `Defs`; the `populate` witness lives in `Populate`; the
`FormalAssertion` contract (`Assumptions`/`Spec`/soundness/completeness/`circuit`) in `Formal`. -/

namespace SP1Clean.AddrAddOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The carry-bool + limb-range form (the literal meaning of the extracted constraint list at
`is_real = 1`), stated against the 3-limb result `value`. The high carry runs against `0`. -/
def RawSpec (a b : Word (ZMod p)) (cols : Extracted.AddrAddOperation (ZMod p)) : Prop :=
  let c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * 65536⁻¹
  let c2 : ZMod p := (a[2] + b[2] - cols.value[2] + c1) * 65536⁻¹
  let c3 : ZMod p := (a[3] + b[3] + c2) * 65536⁻¹
  (c0 = 0 ∨ c0 = 1) ∧ (c1 = 0 ∨ c1 = 1) ∧ (c2 = 0 ∨ c2 = 1) ∧ (c3 = 0 ∨ c3 = 1) ∧
  cols.value[0].val < 65536 ∧ cols.value[1].val < 65536 ∧ cols.value[2].val < 65536

omit [Fact p.Prime] in
/-- `2 ^ 16 < p`, the side condition the limb range checks need. -/
lemma hn16 : 2 ^ 16 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 16 < 2 ^ 17 := by norm_num
  omega

set_option maxHeartbeats 16000000 in
/-- Forward (soundness) core: the 3-limb carry-bool + range form implies the witnessed low-48-bit
result is `(a + b) mod 2^48`. The high carry `c3` runs against `0` (no `value[3]` column); soundness
needs only its booleanity (from `RawSpec`), not the address-fits assumption. Stated over plain words
`a`, `b` (not `Inputs`) so the implicit args unify with a composing soundness goal. -/
theorem addrAddSemantics_of_carries {a b : Word (ZMod p)}
    {cols : Extracted.AddrAddOperation (ZMod p)}
    (ha : Word.isU64 a) (hb : Word.isU64 b)
    (h_raw : RawSpec a b cols) :
    cols.value[0].val + 65536 * cols.value[1].val + 65536 ^ 2 * cols.value[2].val =
      (Word.toNat a + Word.toNat b) % 2 ^ 48 := by
  obtain ⟨hc0, hc1, hc2, hc3, hv0, hv1, hv2⟩ := h_raw
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  simp only [Word.toNat_def]
  set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p := (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p := (a[2] + b[2] - cols.value[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (a[3] + b[3] + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
    rw [hc0_def]; linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
    rw [hc1_def]; linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
  have e2 : a[2] + b[2] + c1 = cols.value[2] + c2 * 65536 := by
    rw [hc2_def]; linear_combination -1 * (a[2] + b[2] - cols.value[2] + c1) * h65inv
  have e3 : a[3] + b[3] + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]; linear_combination -1 * (a[3] + b[3] + c2) * h65inv
  have hc_zero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have hzlt : ((0 : ZMod p)).val < 2 ^ 16 := by rw [ZMod.val_zero]; norm_num
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hc_zero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ ha2 hbb2 hv2 hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ ha3 hbb3 hzlt hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero] at n0 n3
  have hc0_lt : c0.val ≤ 1 := by rcases hc0 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc1_lt : c1.val ≤ 1 := by rcases hc1 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc2_lt : c2.val ≤ 1 := by rcases hc2 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc3_lt : c3.val ≤ 1 := by rcases hc3 with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  omega

set_option maxHeartbeats 16000000 in
/-- The high carry's boolean constraint forces the 64-bit-truncated sum to contain no bits above
the three-limb address. This is an AIR conclusion, not a soundness precondition: the fourth carry
runs against zero, so any satisfying row necessarily represents a 48-bit address. -/
theorem addrAddFits_of_carries {a b : Word (ZMod p)}
    {cols : Extracted.AddrAddOperation (ZMod p)}
    (ha : Word.isU64 a) (hb : Word.isU64 b)
    (h_raw : RawSpec a b cols) :
    (Word.toNat a + Word.toNat b) % 2 ^ 64 < 2 ^ 48 := by
  obtain ⟨hc0, hc1, hc2, hc3, hv0, hv1, hv2⟩ := h_raw
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  set c0 : ZMod p := (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ with hc0_def
  set c1 : ZMod p :=
    (a[1] + b[1] - cols.value[1] + c0) * (65536 : ZMod p)⁻¹ with hc1_def
  set c2 : ZMod p :=
    (a[2] + b[2] - cols.value[2] + c1) * (65536 : ZMod p)⁻¹ with hc2_def
  set c3 : ZMod p := (a[3] + b[3] + c2) * (65536 : ZMod p)⁻¹ with hc3_def
  have e0 : a[0] + b[0] + (0 : ZMod p) = cols.value[0] + c0 * 65536 := by
    rw [hc0_def]
    linear_combination -1 * (a[0] + b[0] - cols.value[0]) * h65inv
  have e1 : a[1] + b[1] + c0 = cols.value[1] + c1 * 65536 := by
    rw [hc1_def]
    linear_combination -1 * (a[1] + b[1] - cols.value[1] + c0) * h65inv
  have e2 : a[2] + b[2] + c1 = cols.value[2] + c2 * 65536 := by
    rw [hc2_def]
    linear_combination -1 * (a[2] + b[2] - cols.value[2] + c1) * h65inv
  have e3 : a[3] + b[3] + c2 = (0 : ZMod p) + c3 * 65536 := by
    rw [hc3_def]
    linear_combination -1 * (a[3] + b[3] + c2) * h65inv
  have hcZero : (0 : ZMod p) = 0 ∨ (0 : ZMod p) = 1 := Or.inl rfl
  have zeroLt : ((0 : ZMod p)).val < 2 ^ 16 := by
    rw [ZMod.val_zero]
    norm_num
  have n0 := limb_lift _ _ _ _ _ ha0 hbb0 hv0 hcZero hc0 e0
  have n1 := limb_lift _ _ _ _ _ ha1 hbb1 hv1 hc0 hc1 e1
  have n2 := limb_lift _ _ _ _ _ ha2 hbb2 hv2 hc1 hc2 e2
  have n3 := limb_lift _ _ _ _ _ ha3 hbb3 zeroLt hc2 hc3 e3
  simp only [ZMod.val_zero, add_zero] at n0 n3
  have sumEq : Word.toNat a + Word.toNat b =
      cols.value[0].val + cols.value[1].val * 2 ^ 16 +
        cols.value[2].val * 2 ^ 32 + c3.val * 2 ^ 64 := by
    simp only [Word.toNat_def]
    omega
  have lowLt : cols.value[0].val + cols.value[1].val * 2 ^ 16 +
      cols.value[2].val * 2 ^ 32 < 2 ^ 48 := by
    omega
  rw [sumEq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  exact lowLt

set_option maxHeartbeats 16000000 in
/-- Backward (completeness) core: a 3-limb result equal to `(a + b) mod 2^48` (with each limb in
range), together with the address-fits side condition, witnesses the unique boolean carry chain.
The low carries `c0, c1, c2` are pinned by the value equation; the high carry `c3 = (a[3]+b[3]+c2)·
65536⁻¹` runs against `0` and is *not* fixed by the result — its booleanity is exactly what `hfit`
(the 64-bit-truncated sum keeps no bits above 48) provides. -/
theorem carries_of_addrAddSemantics {a b : Word (ZMod p)}
    {cols : Extracted.AddrAddOperation (ZMod p)}
    (ha : Word.isU64 a) (hb : Word.isU64 b)
    (hfit : (Word.toNat a + Word.toNat b) % 2 ^ 64 < 2 ^ 48)
    (hr0 : cols.value[0].val < 2 ^ 16) (hr1 : cols.value[1].val < 2 ^ 16)
    (hr2 : cols.value[2].val < 2 ^ 16)
    (h_val : cols.value[0].val + 65536 * cols.value[1].val + 65536 ^ 2 * cols.value[2].val =
      (Word.toNat a + Word.toNat b) % 2 ^ 48) :
    RawSpec a b cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 ha
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 hb
  set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
  set q2 : ℕ := (a[2].val + b[2].val + q1) / 65536 with hq2_def
  set lo0 : ℕ := (a[0].val + b[0].val) % 65536 with hlo0_def
  set lo1 : ℕ := (a[1].val + b[1].val + q0) % 65536 with hlo1_def
  set lo2 : ℕ := (a[2].val + b[2].val + q1) % 65536 with hlo2_def
  have hlo0_lt : lo0 < 65536 := by rw [hlo0_def]; omega
  have hlo1_lt : lo1 < 65536 := by rw [hlo1_def]; omega
  have hlo2_lt : lo2 < 65536 := by rw [hlo2_def]; omega
  have hq0 : q0 ≤ 1 := by rw [hq0_def]; omega
  have hq1 : q1 ≤ 1 := by rw [hq1_def]; omega
  have hq2 : q2 ≤ 1 := by rw [hq2_def]; omega
  have e0n : a[0].val + b[0].val = lo0 + q0 * 65536 := by rw [hlo0_def, hq0_def]; omega
  have e1n : a[1].val + b[1].val + q0 = lo1 + q1 * 65536 := by rw [hlo1_def, hq1_def]; omega
  have e2n : a[2].val + b[2].val + q1 = lo2 + q2 * 65536 := by rw [hlo2_def, hq2_def]; omega
  -- the full sum's base-2^16 digits, with `a[3]+b[3]+q2` the carry-out of the low 48 bits
  have hsum48 : Word.toNat a + Word.toNat b
      = lo0 + lo1 * 2 ^ 16 + lo2 * 2 ^ 32 + (a[3].val + b[3].val + q2) * 2 ^ 48 := by
    simp only [Word.toNat_def]; omega
  have hmod : (Word.toNat a + Word.toNat b) % 2 ^ 48 = lo0 + lo1 * 2 ^ 16 + lo2 * 2 ^ 32 := by
    rw [hsum48]; omega
  -- the result limbs are exactly the low digits (uniqueness of base-2^16 representation)
  rw [hmod] at h_val
  have hv0 : cols.value[0].val = lo0 := by omega
  have hv1 : cols.value[1].val = lo1 := by omega
  have hv2 : cols.value[2].val = lo2 := by omega
  -- lift the limb equations to the field
  have e0nv : a[0].val + b[0].val = cols.value[0].val + q0 * 65536 := by rw [hv0]; omega
  have e1nv : a[1].val + b[1].val + q0 = cols.value[1].val + q1 * 65536 := by rw [hv1]; omega
  have e2nv : a[2].val + b[2].val + q1 = cols.value[2].val + q2 * 65536 := by rw [hv2]; omega
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ val_65536_ne_zero
  have hc0_lift : (a[0] : ZMod p) + b[0] = cols.value[0] + (q0 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0nv
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p) = cols.value[1] + (q1 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1nv
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc2_lift : (a[2] : ZMod p) + b[2] + (q1 : ZMod p) = cols.value[2] + (q2 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e2nv
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc0_eq : (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ = (q0 : ZMod p) := by
    have h : a[0] + b[0] - cols.value[0] = (q0 : ZMod p) * 65536 := by linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + b[1] - cols.value[1] + (q0 : ZMod p) = (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc2_eq : (a[2] + b[2] - cols.value[2] + ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹ = (q2 : ZMod p) := by
    rw [hc1_eq]
    have h : a[2] + b[2] - cols.value[2] + (q1 : ZMod p) = (q2 : ZMod p) * 65536 := by
      linear_combination hc2_lift
    rw [h, mul_assoc, h65inv, mul_one]
  -- the high carry: address-fits forces `a[3].val + b[3].val + q2 ∈ {0, 65536}`
  have hq3cases : a[3].val + b[3].val + q2 = 0 ∨ a[3].val + b[3].val + q2 = 65536 := by
    rw [hsum48] at hfit; omega
  set q3 : ℕ := (a[3].val + b[3].val + q2) / 65536 with hq3_def
  have hq3 : q3 ≤ 1 := by rw [hq3_def]; omega
  have e3nv : a[3].val + b[3].val + q2 = q3 * 65536 := by rw [hq3_def]; omega
  have hc3_lift : (a[3] : ZMod p) + b[3] + (q2 : ZMod p) = (q3 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e3nv
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc3_eq : (a[3] + b[3] + ((a[2] + b[2] - cols.value[2] +
      ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹ = (q3 : ZMod p) := by
    rw [hc2_eq]
    have h : a[3] + b[3] + (q2 : ZMod p) = (q3 : ZMod p) * 65536 := by
      linear_combination hc3_lift
    rw [h, mul_assoc, h65inv, mul_one]
  refine ⟨?_, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · rw [hc0_eq]; interval_cases q0 <;> simp
  · rw [hc1_eq]; interval_cases q1 <;> simp
  · rw [hc2_eq]; interval_cases q2 <;> simp
  · rw [hc3_eq]; interval_cases q3 <;> simp

end SP1Clean.AddrAddOperation
