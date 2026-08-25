import SP1Clean.Proofs.Chips.ShiftLeftChip.Populate

/-! # `ShiftRightChip` — native witness generation (`populate`)

SP1's `ShiftRightChip::event_to_row` (`alu/sr/mod.rs`) ported to Lean: honest witness assignments
for the right-shift column block — the shift-amount bits `c_bits` (shared with `ShiftLeftChip`'s
`cBits`), the **inverted** `v_01/v_012/v_0123` power encodings (`2^(4-s), 2^(8-s), 2^(16-s)`), the
`b_msb`/`srw_msb`/`sra_msb_v0123` sign witnesses, the `lower/higher_limb` bit-split (the top two
limbs gated by `e14 = is_srl + is_sra` — the word variants zero them, matching the `e14`-factored
split constraints), the `limb_result` reassembly, the `shift_u16` one-hot, and the placed result
`a` (the constraints' own placement with the `sraFill`/`bmsbFill`/`srwFill` sign-fills). The four
variant flags come from the `"shift_right_flags"` `ProverHint` (one-hot on real rows, all-zero on
padding); the committed `is_w_imm` is derived as `(is_srlw + is_sraw) · imm_c`.

On all-zero inputs + empty hint these reproduce SP1's `padded_row_template`
(`v_01 = 16, v_012 = 256, v_0123 = 65536`, everything else zero) — checked, with the real rows,
by the `TraceGenTests/ShiftRightChipTraceWitness.lean` anchor. -/

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The four honest variant flags (`is_srl`, `is_sra`, `is_srlw`, `is_sraw`) the prover supplies
via the `"shift_right_flags"` hint key (one-hot for the active variant, all-zero on padding). -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 4 :=
  ((h "shift_right_flags" 4)[0]?).getD #v[0, 0, 0, 0]

/-- The inverted power encodings, in the **witnessed order** `v[0] = v_0123, v[1] = v_012,
v[2] = v_01` (`Defs.lean` binds `let v_0123 := v[0]` …): `2^(16-(c&15)), 2^(8-(c&7)), 2^(4-(c&3))`.
Ungated — on `c0 = 0` they give SP1's padding template `65536, 256, 16`. -/
def vPowersInv (c0 : ZMod p) : Vector (ZMod p) 3 :=
  #v[((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p), ((2 ^ (8 - c0.val % 8) : ℕ) : ZMod p),
     ((2 ^ (4 - c0.val % 4) : ℕ) : ZMod p)]

/-- Per-limb bit-split, low part: `lower_limb[i] = bᵉᶠᶠ[i] mod 2^bitShift`, where the top two
effective limbs carry the `e14 = is_srl + is_sra` factor (the word variants' split constraints are
`e14`-gated, so their honest witness is the split of `e14 · b[i]` — zero on word rows and padding). -/
def lowerLimb (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : Vector (ZMod p) 4 :=
  let s := c0.val % 16
  #v[((b[0].val % 2 ^ s : ℕ) : ZMod p), ((b[1].val % 2 ^ s : ℕ) : ZMod p),
     ((((f[0] + f[1]) * b[2]).val % 2 ^ s : ℕ) : ZMod p),
     ((((f[0] + f[1]) * b[3]).val % 2 ^ s : ℕ) : ZMod p)]

/-- Per-limb bit-split, high part: `higher_limb[i] = bᵉᶠᶠ[i] / 2^bitShift`. -/
def higherLimb (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : Vector (ZMod p) 4 :=
  let s := c0.val % 16
  #v[((b[0].val / 2 ^ s : ℕ) : ZMod p), ((b[1].val / 2 ^ s : ℕ) : ZMod p),
     ((((f[0] + f[1]) * b[2]).val / 2 ^ s : ℕ) : ZMod p),
     ((((f[0] + f[1]) * b[3]).val / 2 ^ s : ℕ) : ZMod p)]

/-- The `limb_result` reassembly in ℕ: `lr[i] = higher[i] + lower[i+1]·2^(16-s)`
(`lr[3] = higher[3]`) — each entry `< 2^16`. -/
def limbResultNat (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : Vector ℕ 4 :=
  let s := c0.val % 16
  #v[b[0].val / 2 ^ s + b[1].val % 2 ^ s * 2 ^ (16 - s),
     b[1].val / 2 ^ s + ((f[0] + f[1]) * b[2]).val % 2 ^ s * 2 ^ (16 - s),
     ((f[0] + f[1]) * b[2]).val / 2 ^ s + ((f[0] + f[1]) * b[3]).val % 2 ^ s * 2 ^ (16 - s),
     ((f[0] + f[1]) * b[3]).val / 2 ^ s]

/-- The `limb_result` reassembly as committed field values. -/
def limbResult (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : Vector (ZMod p) 4 :=
  (limbResultNat b c0 f).map (fun n : ℕ => (n : ZMod p))

/-- The arithmetic sign bit: `is_sra · msb(b[3]) + is_sraw · msb(b[1])` (zero on the logical
variants and padding — the `(is_srl + is_srlw) · b_msb = 0` gate). -/
def bMsb (b : Word (ZMod p)) (f : Vector (ZMod p) 4) : ZMod p :=
  f[1] * U16MSBOperation.populate_msb b[3] + f[3] * U16MSBOperation.populate_msb b[1]

/-- The committed `sra_msb_v0123 = b_msb · v_0123` product column. -/
def sraMsbV0123 (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : ZMod p :=
  bMsb b f * (vPowersInv c0)[0]

/-- The byte-level shift amount `(c≫4)&1 + 2·((c≫5)&1)·not_word` (bit 5 only participates for the
64-bit `SRL`/`SRA`). -/
def byteShiftNat (c0 : ZMod p) (f : Vector (ZMod p) 4) : ℕ :=
  (c0.val >>> 4) % 2 + 2 * ((c0.val >>> 5) % 2) * (if f[0] + f[1] = 1 then 1 else 0)

/-- The `shift_u16` byte-shift selector: one-hot at `byteShiftNat`, gated by the four-flag sum. -/
def shiftU16 (c0 : ZMod p) (f : Vector (ZMod p) 4) : Vector (ZMod p) 4 :=
  let g := f[0] + f[1] + f[2] + f[3]
  let k := byteShiftNat c0 f
  #v[if k = 0 then g else 0, if k = 1 then g else 0, if k = 2 then g else 0, if k = 3 then g else 0]

/-- The result word `a`: the constraints' own per-byteShift placement of `limb_result` with the
sign-fills (`sraFill = b_msb·(65536 - v_0123)` on the top surviving limb, `b_msb·65535` above it
for the 64-bit variants; `srw_msb·65535` upper halves for the word variants), flag-gated to zero
on padding. Agrees with SP1's `event.a` — checked by the `TraceGenTests` anchor. -/
def populateA (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : Word (ZMod p) :=
  let lr := limbResult b c0 f
  let m := bMsb b f
  let sraFill := m * 65536 - m * (vPowersInv c0)[0]
  let mFill := m * 65535
  if f[0] + f[1] = 1 then
    match byteShiftNat c0 f with
    | 0 => #v[lr[0], lr[1], lr[2], lr[3] + sraFill]
    | 1 => #v[lr[1], lr[2], lr[3] + sraFill, mFill]
    | 2 => #v[lr[2], lr[3] + sraFill, mFill, mFill]
    | _ => #v[lr[3] + sraFill, mFill, mFill, mFill]
  else if f[2] + f[3] = 1 then
    let lo : Vector (ZMod p) 2 :=
      if byteShiftNat c0 f = 0 then #v[lr[0], lr[1] + sraFill] else #v[lr[1] + sraFill, mFill]
    let sm := U16MSBOperation.populate_msb lo[1]
    #v[lo[0], lo[1], sm * 65535, sm * 65535]
  else #v[0, 0, 0, 0]

/-- The word-variant sign bit: the MSB of the placed `a[1]` limb, gated to `is_srlw + is_sraw`. -/
def srwMsb (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) : ZMod p :=
  if f[2] + f[3] = 1 then U16MSBOperation.populate_msb (populateA b c0 f)[1] else 0

/-! ## Value-level constraint lemmas (the `Formal.lean` completeness bundles) -/

section ValueLemmas

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The small field numerals `2`/`3`/`4` are neither `0` nor `1` (`p > 2^17`) — the one-hot
contradiction kernel for the four-flag case bashes. -/
private lemma numeral_ne_01 :
    ((2 : ZMod p) ≠ 0 ∧ (2 : ZMod p) ≠ 1) ∧ ((3 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 1) ∧
    ((4 : ZMod p) ≠ 0 ∧ (4 : ZMod p) ≠ 1) := by
  have key : ∀ {x : ZMod p} {n : ℕ}, x.val = n → 1 < n → x ≠ 0 ∧ x ≠ 1 := by
    intro x n hx hn
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hx
    · rw [ZMod.val_zero] at hx; omega
    · rw [ZMod.val_one] at hx; omega
  exact ⟨key val_2_zmod_p one_lt_two, key val_3_zmod_p (by norm_num),
    key val_4_zmod_p (by norm_num)⟩

/-- Binary flags with a binary sum are one-hot: each set flag forces the other three to zero. -/
theorem one_hot_resolve (f : Vector (ZMod p) 4)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) :
    (f[0] = 1 → f[1] = 0 ∧ f[2] = 0 ∧ f[3] = 0) ∧
    (f[1] = 1 → f[0] = 0 ∧ f[2] = 0 ∧ f[3] = 0) ∧
    (f[2] = 1 → f[0] = 0 ∧ f[1] = 0 ∧ f[3] = 0) ∧
    (f[3] = 1 → f[0] = 0 ∧ f[1] = 0 ∧ f[2] = 0) := by
  obtain ⟨⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩⟩ := numeral_ne_01 (p := p)
  rcases hf0 with h0 | h0 <;> rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2 <;>
    rcases hf3 with h3 | h3 <;>
    simp only [h0, h1, h2, h3] at hsum01 ⊢ <;>
    first
      | (simp; done)
      | (exfalso; norm_num at hsum01; rcases hsum01 with h | h <;>
          first | exact a2 h | exact b2 h | exact a3 h | exact b3 h | exact a4 h | exact b4 h)

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- ℕ core of the inverted `v_01` encoding. -/
private lemma two_pow_inv_four (x : ℕ) :
    2 ^ (4 - x % 4) = (1 - x % 2 + 1) * 2 * ((1 - x / 2 % 2) * 3 + 1) := by
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h0 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 2) with h1 | h1 <;>
    · rw [show x % 4 = x % 2 + 2 * (x / 2 % 2) from by omega, h0, h1]; norm_num

omit [Fact (2 ^ 17 < p)] in
/-- The three inverted `v_*` power-encoding asserts, in goal form (witnessed order
`v[0] = v_0123, v[1] = v_012, v[2] = v_01`). -/
theorem vInv_asserts (c0 : ZMod p) :
    (vPowersInv c0)[2] + -((1 + -(ShiftLeftChip.cBits c0)[0] + 1) * 2
      * ((1 + -(ShiftLeftChip.cBits c0)[1]) * 3 + 1)) = 0 ∧
    (vPowersInv c0)[1]
      + -((vPowersInv c0)[2] * ((1 + -(ShiftLeftChip.cBits c0)[2]) * 15 + 1)) = 0 ∧
    (vPowersInv c0)[0]
      + -((vPowersInv c0)[1] * ((1 + -(ShiftLeftChip.cBits c0)[3]) * 255 + 1)) = 0 := by
  simp only [vPowersInv, ShiftLeftChip.cBits, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.shiftRight_eq_div_pow, pow_zero, pow_one,
    Nat.div_one]
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one c0.val with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one (c0.val / 2) with h1 | h1 <;>
      · rw [show c0.val % 4 = c0.val % 2 + 2 * (c0.val / 2 % 2) from by omega, h0, h1]
        norm_num
  · rcases Nat.mod_two_eq_zero_or_one (c0.val / 4) with h | h
    · rw [show c0.val % 8 = c0.val % 4 from by omega, h,
        show 8 - c0.val % 4 = 4 - c0.val % 4 + 4 from by omega, pow_add]
      push_cast
      ring
    · rw [show c0.val % 8 = c0.val % 4 + 4 from by omega, h,
        show 8 - (c0.val % 4 + 4) = 4 - c0.val % 4 from by omega]
      push_cast
      ring
  · rcases Nat.mod_two_eq_zero_or_one (c0.val / 8) with h | h
    · rw [show c0.val % 16 = c0.val % 8 from by omega, h,
        show 16 - c0.val % 8 = 8 - c0.val % 8 + 8 from by omega, pow_add]
      push_cast
      ring
    · rw [show c0.val % 16 = c0.val % 8 + 8 from by omega, h,
        show 16 - (c0.val % 8 + 8) = 8 - c0.val % 8 from by omega]
      push_cast
      ring

omit [Fact (2 ^ 17 < p)] in
/-- One limb's right-shift bit-split assert: `x·2^(16-s) = (x/2^s)·2^16 + (x mod 2^s)·2^(16-s)`. -/
private lemma split_cell (c0 x : ZMod p) :
    x * (vPowersInv c0)[0]
      + -(((x.val / 2 ^ (c0.val % 16) : ℕ) : ZMod p) * 65536
          + ((x.val % 2 ^ (c0.val % 16) : ℕ) : ZMod p) * (vPowersInv c0)[0]) = 0 := by
  simp only [vPowersInv, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  have hpow : 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) = 65536 := by
    rw [← pow_add]
    have h : c0.val % 16 + (16 - c0.val % 16) = 16 := by omega
    rw [h]; norm_num
  have key : x.val * 2 ^ (16 - c0.val % 16)
      = x.val / 2 ^ (c0.val % 16) * 65536
        + x.val % 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) := by
    have hsplit := Nat.div_add_mod x.val (2 ^ (c0.val % 16))
    calc x.val * 2 ^ (16 - c0.val % 16)
        = (2 ^ (c0.val % 16) * (x.val / 2 ^ (c0.val % 16))
            + x.val % 2 ^ (c0.val % 16)) * 2 ^ (16 - c0.val % 16) := by rw [hsplit]
      _ = x.val / 2 ^ (c0.val % 16) * (2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16))
            + x.val % 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) := by ring
      _ = _ := by rw [hpow]
  have hx_eq : x * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p)
      = ((x.val * 2 ^ (16 - c0.val % 16) : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hx_eq, key]
  push_cast
  ring

omit [Fact (2 ^ 17 < p)] in
/-- The four per-limb bit-split asserts, in goal form (top two limbs carry the `e14` factor). -/
theorem split_asserts (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) :
    b[0] * (vPowersInv c0)[0]
      + -((higherLimb b c0 f)[0] * 65536 + (lowerLimb b c0 f)[0] * (vPowersInv c0)[0]) = 0 ∧
    b[1] * (vPowersInv c0)[0]
      + -((higherLimb b c0 f)[1] * 65536 + (lowerLimb b c0 f)[1] * (vPowersInv c0)[0]) = 0 ∧
    b[2] * (vPowersInv c0)[0] * (f[0] + f[1])
      + -((higherLimb b c0 f)[2] * 65536 + (lowerLimb b c0 f)[2] * (vPowersInv c0)[0]) = 0 ∧
    b[3] * (vPowersInv c0)[0] * (f[0] + f[1])
      + -((higherLimb b c0 f)[3] * 65536 + (lowerLimb b c0 f)[3] * (vPowersInv c0)[0]) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [lowerLimb, higherLimb, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact split_cell c0 b[0]
  · exact split_cell c0 b[1]
  · rw [show b[2] * (vPowersInv c0)[0] * (f[0] + f[1])
        = ((f[0] + f[1]) * b[2]) * (vPowersInv c0)[0] from by ring]
    exact split_cell c0 ((f[0] + f[1]) * b[2])
  · rw [show b[3] * (vPowersInv c0)[0] * (f[0] + f[1])
        = ((f[0] + f[1]) * b[3]) * (vPowersInv c0)[0] from by ring]
    exact split_cell c0 ((f[0] + f[1]) * b[3])

omit [Fact (2 ^ 17 < p)] in
/-- The four `limb_result` reassembly asserts, in goal form. -/
theorem limbResult_asserts (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4) :
    (limbResult b c0 f)[0]
      + -((higherLimb b c0 f)[0] + (lowerLimb b c0 f)[1] * (vPowersInv c0)[0]) = 0 ∧
    (limbResult b c0 f)[1]
      + -((higherLimb b c0 f)[1] + (lowerLimb b c0 f)[2] * (vPowersInv c0)[0]) = 0 ∧
    (limbResult b c0 f)[2]
      + -((higherLimb b c0 f)[2] + (lowerLimb b c0 f)[3] * (vPowersInv c0)[0]) = 0 ∧
    (limbResult b c0 f)[3] + -(higherLimb b c0 f)[3] = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [limbResult, limbResultNat, vPowersInv, lowerLimb, higherLimb,
        Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      push_cast
      ring

/-- The three sign-witness asserts: the logical-variant `b_msb` gate, the `sra_msb_v0123` product
bind, and the off-word `srw_msb` gate, in goal form (for one-hot flags). -/
theorem msb_asserts (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) :
    (f[0] + f[2]) * bMsb b f = 0 ∧
    sraMsbV0123 b c0 f + -(bMsb b f * (vPowersInv c0)[0]) = 0 ∧
    (f[2] + f[3] + -1) * srwMsb b c0 f = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := one_hot_resolve f hf0 hf1 hf2 hf3 hsum01
  refine ⟨?_, by rw [sraMsbV0123]; exact add_neg_cancel _, ?_⟩
  · unfold bMsb
    rcases hf1 with hb1 | hb1
    · rcases hf3 with hb3 | hb3
      · rw [hb1, hb3]; ring
      · obtain ⟨hz0, -, hz2⟩ := h3 hb3
        rw [hb1, hz0, hz2]; ring
    · obtain ⟨hz0, hz2, hz3⟩ := h1 hb1
      rw [hz0, hz2, hz3, hb1]; ring
  · by_cases h : f[2] + f[3] = 1
    · rw [h]; ring
    · rw [srwMsb, if_neg h, mul_zero]

set_option linter.unusedSectionVars false in
/-- `byteShiftNat < 4` (each contributing bit is ≤ 1). -/
theorem byteShiftNat_lt (c0 : ZMod p) (f : Vector (ZMod p) 4) : byteShiftNat c0 f < 4 := by
  have h4 := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
  have h5 := Nat.mod_lt (c0.val >>> 5) (show 0 < 2 by norm_num)
  unfold byteShiftNat
  split <;> omega

set_option linter.unusedSectionVars false in
/-- The four `byteShiftNat` cases, as the case bashes consume them. -/
private lemma byteShift_cases (c0 : ZMod p) (f : Vector (ZMod p) 4) :
    byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
      ∨ byteShiftNat c0 f = 3 := by
  have := byteShiftNat_lt c0 f
  omega

/-- The 22 result-placement asserts (16 `e14`-gated SRL/SRA + 6 `e13`-gated SRLW/SRAW), in goal
form: at the populate values every placement product vanishes (for one-hot flags). -/
theorem place_asserts (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) :
    (f[0] + f[1]) * ((shiftU16 c0 f)[0]
      * ((populateA b c0 f)[0] + -(limbResult b c0 f)[0])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[0]
      * ((populateA b c0 f)[1] + -(limbResult b c0 f)[1])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[0]
      * ((populateA b c0 f)[2] + -(limbResult b c0 f)[2])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[3]
      + -((limbResult b c0 f)[3] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[1]
      * ((populateA b c0 f)[0] + -(limbResult b c0 f)[1])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[1]
      * ((populateA b c0 f)[1] + -(limbResult b c0 f)[2])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[2]
      + -((limbResult b c0 f)[3] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[1]
      * ((populateA b c0 f)[3] + -(bMsb b f * 65535))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[2]
      * ((populateA b c0 f)[0] + -(limbResult b c0 f)[2])) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[2] * ((populateA b c0 f)[1]
      + -((limbResult b c0 f)[3] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[2]
      * ((populateA b c0 f)[2] + -(bMsb b f * 65535))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[2]
      * ((populateA b c0 f)[3] + -(bMsb b f * 65535))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[3] * ((populateA b c0 f)[0]
      + -((limbResult b c0 f)[3] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[3]
      * ((populateA b c0 f)[1] + -(bMsb b f * 65535))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[3]
      * ((populateA b c0 f)[2] + -(bMsb b f * 65535))) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[3]
      * ((populateA b c0 f)[3] + -(bMsb b f * 65535))) = 0 ∧
    (f[2] + f[3]) * ((shiftU16 c0 f)[0]
      * ((populateA b c0 f)[0] + -(limbResult b c0 f)[0])) = 0 ∧
    (f[2] + f[3]) * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[1]
      + -((limbResult b c0 f)[1] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[2] + f[3]) * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[0]
      + -((limbResult b c0 f)[1] + (bMsb b f * 65536 + -sraMsbV0123 b c0 f)))) = 0 ∧
    (f[2] + f[3]) * ((shiftU16 c0 f)[1]
      * ((populateA b c0 f)[1] + -(bMsb b f * 65535))) = 0 ∧
    (f[2] + f[3]) * ((populateA b c0 f)[2] + -(srwMsb b c0 f * 65535)) = 0 ∧
    (f[2] + f[3]) * ((populateA b c0 f)[3] + -(srwMsb b c0 f * 65535)) = 0 := by
  obtain ⟨ho0, ho1, ho2, ho3⟩ := one_hot_resolve f hf0 hf1 hf2 hf3 hsum01
  rcases hf0 with h0 | h0
  · rcases hf1 with h1 | h1
    · -- word variants or padding: `e14 = 0`, so bit 5 never participates
      have hk2 : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 := by
        have := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
        unfold byteShiftNat
        rw [h0, h1, if_neg (by rw [zero_add]; exact zero_ne_one)]
        omega
      rcases hf2 with h2 | h2
      · rcases hf3 with h3 | h3
        · -- padding
          simp [h0, h1, h2, h3, populateA, srwMsb, shiftU16]
        · -- SRAW
          obtain ⟨-, -, hz2⟩ := ho3 h3
          rcases hk2 with hbs | hbs <;>
            · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h0, h1, hz2, h3, hbs]
              norm_num
              ring
      · -- SRLW
        obtain ⟨-, -, hz3⟩ := ho2 h2
        rcases hk2 with hbs | hbs <;>
          · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h0, h1, h2, hz3, hbs]
            norm_num
            ring
    · -- SRA
      obtain ⟨hz0, hz2, hz3⟩ := ho1 h1
      rcases byteShift_cases c0 f with hbs | hbs | hbs | hbs <;>
        · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h1, hz0, hz2, hz3, hbs]
          norm_num
          ring
  · -- SRL
    obtain ⟨hz1, hz2, hz3⟩ := ho0 h0
    rcases byteShift_cases c0 f with hbs | hbs | hbs | hbs <;>
      · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h0, hz1, hz2, hz3, hbs]
        norm_num
        ring

omit [Fact (2 ^ 17 < p)] in
/-- An `e14`-gated effective limb is still a u16 value (`e14` binary). -/
private lemma effVal_lt (x g : ZMod p) (hg : g = 0 ∨ g = 1) (hx : x.val < 2 ^ 16) :
    (g * x).val < 2 ^ 16 := by
  rcases hg with h | h <;> rw [h]
  · rw [zero_mul, ZMod.val_zero]; norm_num
  · rw [one_mul]; exact hx

/-- ℕ core of the split's high part: a u16 divided by `2^s` is below `2^(16-s)`. -/
private lemma div_pow_lt {s x : ℕ} (hs : s ≤ 16) (hx : x < 2 ^ 16) :
    x / 2 ^ s < 2 ^ (16 - s) :=
  Nat.div_lt_of_lt_mul (by rw [← pow_add, show s + (16 - s) = 16 from by omega]; exact hx)

/-- Each `lower_limb` entry's `.val` is below `2^bitShift`. -/
theorem lowerLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (i : ℕ) (hi : i < 4) : (lowerLimb b c0 f)[i].val < 2 ^ (c0.val % 16) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hpos : 0 < 2 ^ (c0.val % 16) := pow_pos (by norm_num) _
  have hle : 2 ^ (c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : ∀ x : ZMod p,
      ((x.val % 2 ^ (c0.val % 16) : ℕ) : ZMod p).val < 2 ^ (c0.val % 16) := fun x => by
    rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt x.val hpos; omega)]
    exact Nat.mod_lt _ hpos
  interval_cases i <;>
    · simp only [lowerLimb, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      exact key _

/-- Each `higher_limb` entry's `.val` is below `2^(16 - bitShift)` (u16 effective limbs). -/
theorem higherLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1)
    (i : ℕ) (hi : i < 4) : (higherLimb b c0 f)[i].val < 2 ^ (16 - c0.val % 16) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have key : ∀ x : ℕ, x < 2 ^ 16 → x / 2 ^ (c0.val % 16) < 2 ^ (16 - c0.val % 16) :=
    fun _ hx => div_pow_lt (by omega) hx
  have hsmall : ∀ x : ℕ, x < 2 ^ 16 → x / 2 ^ (c0.val % 16) < p := by
    intro x hx
    have h1 := key x hx
    have h2 : 2 ^ (16 - c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  have he2 := effVal_lt (b[2]) (f[0] + f[1]) he14 hb2
  have he3 := effVal_lt (b[3]) (f[0] + f[1]) he14 hb3
  interval_cases i <;>
    simp only [higherLimb, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb0)]; exact key _ hb0
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb1)]; exact key _ hb1
  · rw [ZMod.val_natCast_of_lt (hsmall _ he2)]; exact key _ he2
  · rw [ZMod.val_natCast_of_lt (hsmall _ he3)]; exact key _ he3

set_option linter.unusedSectionVars false in
/-- Each `limb_result` ℕ entry is `< 2^16`. -/
theorem limbResultNat_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1)
    (i : ℕ) (hi : i < 4) : (limbResultNat b c0 f)[i] < 2 ^ 16 := by
  have key : ∀ (x y : ℕ), x < 2 ^ 16 → y < 2 ^ 16 →
      x / 2 ^ (c0.val % 16) + y % 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) < 2 ^ 16 := by
    intro x y hx _
    have hpow : 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) = 65536 := by
      rw [← pow_add, show 16 - c0.val % 16 + c0.val % 16 = 16 from by omega]; norm_num
    exact ShiftBounds.lo_hi_lt hpow (div_pow_lt (by omega) hx)
      (Nat.mod_lt _ (pow_pos (by norm_num) _))
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  have he2 := effVal_lt (b[2]) (f[0] + f[1]) he14 hb2
  have he3 := effVal_lt (b[3]) (f[0] + f[1]) he14 hb3
  interval_cases i <;>
    simp only [limbResultNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact key _ _ hb0 hb1
  · exact key _ _ hb1 he2
  · exact key _ _ he2 he3
  · exact lt_of_le_of_lt (Nat.le_add_right _ _) (key _ _ he3 he3)

/-- Each `limb_result` field entry has `.val < 2^16`. -/
theorem limbResult_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1)
    (i : ℕ) (hi : i < 4) : (limbResult b c0 f)[i].val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have h := limbResultNat_lt b c0 f hb he14 i hi
  simp only [limbResult, Vector.getElem_map]
  rw [ZMod.val_natCast_of_lt (by omega)]
  exact h

/-- The arithmetic sign witness is boolean (one-hot flags, u16 operand limbs). -/
theorem bMsb_bool (b : Word (ZMod p)) (f : Vector (ZMod p) 4) (hb : Word.isU64 b)
    (hf1 : f[1] = 0 ∨ f[1] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hone : f[1] = 1 → f[3] = 0) : bMsb b f = 0 ∨ bMsb b f = 1 := by
  obtain ⟨-, hb1, -, hb3⟩ := Word.lt_cases_of_isU64 hb
  unfold bMsb
  rcases hf1 with h1 | h1
  · rcases hf3 with h3 | h3
    · left; rw [h1, h3]; ring
    · rw [h1, h3, zero_mul, zero_add, one_mul]
      exact U16MSBOperation.populate_msb_bool hb1
  · rw [h1, hone h1, zero_mul, add_zero, one_mul]
    exact U16MSBOperation.populate_msb_bool hb3

omit [Fact (2 ^ 17 < p)] in
/-- The committed byte-shift expression equals the cast of `byteShiftNat` (for binary `e14`). -/
theorem byteShift_expr_eq (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) :
    (ShiftLeftChip.cBits c0)[4] + (ShiftLeftChip.cBits c0)[5] * 2 * (f[0] + f[1])
      = ((byteShiftNat c0 f : ℕ) : ZMod p) := by
  rcases he14 with h | h <;>
    simp only [ShiftLeftChip.cBits, byteShiftNat, h, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, if_pos, zero_ne_one, if_false] <;>
    push_cast <;> ring

/-- The eight `shift_u16` selector/boolean asserts plus the gated one-hot sum, in goal form. -/
theorem shiftU16_asserts (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) :
    (shiftU16 c0 f)[0] * ((ShiftLeftChip.cBits c0)[4]
      + (ShiftLeftChip.cBits c0)[5] * 2 * (f[0] + f[1])) = 0 ∧
    (shiftU16 c0 f)[0] * ((shiftU16 c0 f)[0] + -1) = 0 ∧
    (shiftU16 c0 f)[1] * ((ShiftLeftChip.cBits c0)[4]
      + (ShiftLeftChip.cBits c0)[5] * 2 * (f[0] + f[1]) + -1) = 0 ∧
    (shiftU16 c0 f)[1] * ((shiftU16 c0 f)[1] + -1) = 0 ∧
    (shiftU16 c0 f)[2] * ((ShiftLeftChip.cBits c0)[4]
      + (ShiftLeftChip.cBits c0)[5] * 2 * (f[0] + f[1]) + -2) = 0 ∧
    (shiftU16 c0 f)[2] * ((shiftU16 c0 f)[2] + -1) = 0 ∧
    (shiftU16 c0 f)[3] * ((ShiftLeftChip.cBits c0)[4]
      + (ShiftLeftChip.cBits c0)[5] * 2 * (f[0] + f[1]) + -3) = 0 ∧
    (shiftU16 c0 f)[3] * ((shiftU16 c0 f)[3] + -1) = 0 ∧
    (f[0] + f[1] + f[2] + f[3]) * ((shiftU16 c0 f)[0] + (shiftU16 c0 f)[1]
      + (shiftU16 c0 f)[2] + (shiftU16 c0 f)[3] + -1) = 0 := by
  rw [byteShift_expr_eq c0 f he14]
  have hk4 := byteShiftNat_lt c0 f
  simp only [shiftU16, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  set k := byteShiftNat c0 f with hk
  clear_value k
  interval_cases k <;>
    · norm_num
      all_goals
        rcases hsum01 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; ring)

/-- The sign-fill bound: a `limb_result` entry below `2^(16-s)` plus the `sraFill` stays a u16. -/
private lemma fill_bound (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hbm : bMsb b f = 0 ∨ bMsb b f = 1) (j : ℕ) (hj : j < 4)
    (hjlt : (limbResultNat b c0 f)[j] < 2 ^ (16 - c0.val % 16)) :
    ((limbResult b c0 f)[j]
      + (bMsb b f * 65536 - bMsb b f * (vPowersInv c0)[0])).val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hlrj : (limbResult b c0 f)[j] = (((limbResultNat b c0 f)[j] : ℕ) : ZMod p) := by
    simp [limbResult, Vector.getElem_map]
  have hle16 : 2 ^ (16 - c0.val % 16) ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hbm with h | h <;> rw [h]
  · simp only [zero_mul, sub_zero, add_zero, hlrj]
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega
  · rw [one_mul, one_mul, hlrj]
    rw [show ((vPowersInv c0)[0] : ZMod p) = ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p) from by
      simp [vPowersInv]]
    rw [← Nat.cast_sub (le_trans hle16 (by norm_num)), ← Nat.cast_add,
      ZMod.val_natCast_of_lt (by omega)]
    omega

/-- `limb_result[3]` is below `2^(16-s)` (it is a bare `higher` part). -/
private lemma lr3_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) :
    (limbResultNat b c0 f)[3] < 2 ^ (16 - c0.val % 16) := by
  have he3 := effVal_lt (b[3]) (f[0] + f[1]) he14 (Word.lt_cases_of_isU64 hb).2.2.2
  simp only [limbResultNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]
  exact div_pow_lt (by omega) he3

/-- `limb_result[1]` is below `2^(16-s)` on word rows (`e14 = 0` zeroes its `lower` summand). -/
private lemma lr1_lt_word (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (hz : f[0] + f[1] = 0) :
    (limbResultNat b c0 f)[1] < 2 ^ (16 - c0.val % 16) := by
  have hb1 := (Word.lt_cases_of_isU64 hb).2.1
  simp only [limbResultNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, hz, zero_mul, ZMod.val_zero, Nat.zero_mod, add_zero]
  exact div_pow_lt (by omega) hb1

/-- Each placed result limb has `.val < 2^16`. -/
theorem populateA_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1)
    (i : ℕ) (hi : i < 4) : (populateA b c0 f)[i].val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  obtain ⟨ho0, ho1, -, -⟩ := one_hot_resolve f hf0 hf1 hf2 hf3 hsum01
  have hbm := bMsb_bool b f hb hf1 hf3 (fun h => (ho1 h).2.2)
  have hzero : (0 : ZMod p).val < 2 ^ 16 := by rw [ZMod.val_zero]; norm_num
  have hmul65535 : ∀ x : ZMod p, x = 0 ∨ x = 1 → (x * 65535).val < 2 ^ 16 := by
    rintro x (h | h) <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, val_65535_zmod_p]; norm_num
  by_cases h14 : f[0] + f[1] = 1
  · have he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1 := Or.inr h14
    have hlr := fun j hj => limbResult_val_lt b c0 f hb he14 j hj
    have hfill := fill_bound b c0 f hbm 3 (by norm_num) (lr3_lt b c0 f hb he14)
    rcases byteShift_cases c0 f with hbs | hbs | hbs | hbs <;>
      · simp only [populateA, h14, if_true, hbs, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        interval_cases i <;>
          first
            | exact hlr _ (by norm_num)
            | exact hfill
            | exact hmul65535 _ hbm
  · have hz14 : f[0] + f[1] = 0 := by
      rcases hf0 with h0 | h0
      · rcases hf1 with h1 | h1
        · rw [h0, h1, add_zero]
        · exact absurd (show f[0] + f[1] = 1 by rw [h0, h1, zero_add]) h14
      · obtain ⟨h1z, -, -⟩ := ho0 h0
        exact absurd (show f[0] + f[1] = 1 by rw [h0, h1z, add_zero]) h14
    have he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1 := Or.inl hz14
    have hlr := fun j hj => limbResult_val_lt b c0 f hb he14 j hj
    have hfill := fill_bound b c0 f hbm 1 (by norm_num) (lr1_lt_word b c0 f hb hz14)
    by_cases h13 : f[2] + f[3] = 1
    · have hsm : ∀ x : ZMod p, x.val < 2 ^ 16 →
          (U16MSBOperation.populate_msb x * 65535).val < 2 ^ 16 := fun x hx =>
        hmul65535 _ (U16MSBOperation.populate_msb_bool hx)
      by_cases hbs : byteShiftNat c0 f = 0 <;>
        · simp only [populateA, h14, if_false, h13, if_true, hbs, Vector.getElem_mk,
            List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
          interval_cases i <;>
            first
              | exact hlr _ (by norm_num)
              | exact hfill
              | exact hmul65535 _ hbm
              | exact hsm _ hfill
              | exact hsm _ (hmul65535 _ hbm)
    · simp only [populateA, h14, h13, if_false]
      interval_cases i <;> exact hzero

/-- The witnessed word-variant sign bit is boolean. -/
theorem srwMsb_bool (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hf2 : f[2] = 0 ∨ f[2] = 1) (hf3 : f[3] = 0 ∨ f[3] = 1)
    (hsum01 : f[0] + f[1] + f[2] + f[3] = 0 ∨ f[0] + f[1] + f[2] + f[3] = 1) :
    srwMsb b c0 f = 0 ∨ srwMsb b c0 f = 1 := by
  unfold srwMsb
  split
  · exact U16MSBOperation.populate_msb_bool
      (populateA_val_lt b c0 f hb hf0 hf1 hf2 hf3 hsum01 1 (by norm_num))
  · exact Or.inl rfl

omit [Fact (2 ^ 17 < p)] in
/-- On `SRA` rows the sign witness is the MSB of the top operand limb. -/
theorem bMsb_eq_sra (b : Word (ZMod p)) (f : Vector (ZMod p) 4)
    (h1 : f[1] = 1) (hz3 : f[3] = 0) :
    bMsb b f = U16MSBOperation.populate_msb b[3] := by
  unfold bMsb; rw [h1, hz3]; ring

omit [Fact (2 ^ 17 < p)] in
/-- On `SRAW` rows the sign witness is the MSB of operand limb 1. -/
theorem bMsb_eq_sraw (b : Word (ZMod p)) (f : Vector (ZMod p) 4)
    (h3 : f[3] = 1) (hz1 : f[1] = 0) :
    bMsb b f = U16MSBOperation.populate_msb b[1] := by
  unfold bMsb; rw [h3, hz1]; ring

/-- The `lower_limb` byte-range pull rows (`< 2^bitShift`) are in the table (field-numeral
normal form; the completeness use-site `convert`s the circuit's ℕ-cast numerals onto it). -/
theorem byteRow_lower (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (i : ℕ) (hi : i < 4) :
    ByteRowSpec (⟨6, (lowerLimb b c0 f)[i],
      (ShiftLeftChip.cBits c0)[0] * (1 : ZMod p) + (ShiftLeftChip.cBits c0)[1] * (2 : ZMod p)
        + (ShiftLeftChip.cBits c0)[2] * (4 : ZMod p) + (ShiftLeftChip.cBits c0)[3] * (8 : ZMod p),
      0⟩ : ByteRow (ZMod p)) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  rw [ShiftLeftChip.cBits_bitShift_sum]
  refine ShiftLeftChip.byteRowSpec_range_intro ?_
  rw [ZMod.val_natCast_of_lt (show c0.val % 16 < p by omega)]
  exact lowerLimb_val_lt b c0 f i hi

/-- The `higher_limb` byte-range pull rows (`< 2^(16 - bitShift)`) are in the table
(field-numeral normal form). -/
theorem byteRow_higher (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) (i : ℕ) (hi : i < 4) :
    ByteRowSpec (⟨6, (higherLimb b c0 f)[i],
      (16 : ZMod p) + -((ShiftLeftChip.cBits c0)[0] * (1 : ZMod p)
        + (ShiftLeftChip.cBits c0)[1] * (2 : ZMod p) + (ShiftLeftChip.cBits c0)[2] * (4 : ZMod p)
        + (ShiftLeftChip.cBits c0)[3] * (8 : ZMod p)),
      0⟩ : ByteRow (ZMod p)) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hw : (16 : ZMod p) + -((ShiftLeftChip.cBits c0)[0] * (1 : ZMod p)
      + (ShiftLeftChip.cBits c0)[1] * (2 : ZMod p) + (ShiftLeftChip.cBits c0)[2] * (4 : ZMod p)
      + (ShiftLeftChip.cBits c0)[3] * (8 : ZMod p))
      = ((16 - c0.val % 16 : ℕ) : ZMod p) := by
    rw [ShiftLeftChip.cBits_bitShift_sum, ← sub_eq_add_neg,
      show ((16 : ZMod p)) = ((16 : ℕ) : ZMod p) by push_cast; rfl,
      ← Nat.cast_sub (by omega)]
  rw [hw]
  refine ShiftLeftChip.byteRowSpec_range_intro ?_
  rw [ZMod.val_natCast_of_lt (show 16 - c0.val % 16 < p by omega)]
  exact higherLimb_val_lt b c0 f hb he14 i hi

end ValueLemmas

/-! ## Witness IR

The exportable twins of the eleven witness payloads (`ShiftLeftChip`'s recipe, plus the
right-shift specifics): the split modulus is `2^bitShift = 1 <<< s`, the inverted powers are
`{65536,256,16} >>> (c & mask)`, the *effective* top limbs carry the `(is_srl + is_sra)` field
factor through `FExpr.val`, and the arithmetic sign fill `m·65536 − m·2^(16−s)` is the
subtraction-free u64 form `m · ((65535 / v) · v)` for `v = 2^(16−s)`. Deliberately **not**
`@[circuit_norm]`. -/

section WitnessIR

/-- The four hint-flag reads (`is_srl`, `is_sra`, `is_srlw`, `is_sraw`), as IR leaves. -/
def hintF (k : Fin 4) : Witgen.FExpr (ZMod p) := .hintGet "shift_right_flags" 4 0 k

/-- The three inverted power encodings, as IR (`2^n >>> s = 2^(n−s)`). -/
def vPowersInvIR (c0e : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 3 :=
  .ofFExprs #v[((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16)).toField,
               ((256 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 8)).toField,
               ((16 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 4)).toField]

/-- The bit-split modulus `2^bitShift`, u64-sorted. -/
def bitModU (c0e : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16)

/-- The effective limb `i` (`i ∈ {2,3}` carries the `is_srl + is_sra` factor), u64-sorted. -/
def effU (b : Word (Expression (ZMod p))) (i : ℕ) : Witgen.U64Expr (ZMod p) :=
  [Witgen.U64Expr.val (.expr b[0]), Witgen.U64Expr.val (.expr b[1]),
   .val (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) * .expr b[2]),
   .val (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) * .expr b[3])].getD i 0

/-- The per-limb low bit-split, as IR. -/
def lowerLimbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[(effU b 0 % bitModU c0e).toField, (effU b 1 % bitModU c0e).toField,
               (effU b 2 % bitModU c0e).toField, (effU b 3 % bitModU c0e).toField]

/-- The per-limb high bit-split, as IR. -/
def higherLimbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[(effU b 0 / bitModU c0e).toField, (effU b 1 / bitModU c0e).toField,
               (effU b 2 / bitModU c0e).toField, (effU b 3 / bitModU c0e).toField]

/-- The `limb_result` cell `i` as a bare `FExpr` (`higher[i] + lower[i+1] · 2^(16−s)`). -/
def lrF (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) (i : ℕ) :
    Witgen.FExpr (ZMod p) :=
  [(effU b 0 / bitModU c0e
     + effU b 1 % bitModU c0e * ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16))).toField,
   (effU b 1 / bitModU c0e
     + effU b 2 % bitModU c0e * ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16))).toField,
   (effU b 2 / bitModU c0e
     + effU b 3 % bitModU c0e * ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16))).toField,
   (effU b 3 / bitModU c0e).toField].getD i 0

/-- The `limb_result` reassembly, as IR. -/
def limbResultIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[lrF b c0e 0, lrF b c0e 1, lrF b c0e 2, lrF b c0e 3]

/-- The arithmetic sign bit, as a bare `FExpr`. -/
def bMsbF (b : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  hintF 1 * U16MSBOperation.populate_msbF (.expr b[3])
    + hintF 3 * U16MSBOperation.populate_msbF (.expr b[1])

/-- The sign bit as a one-cell payload. -/
def bMsbIR (b : Word (Expression (ZMod p))) : Witgen.WitgenIR (ZMod p) 1 :=
  .ofFExprs #v[bMsbF b]

/-- The committed `b_msb · v_0123` product, as a one-cell payload. -/
def sraMsbV0123IR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 1 :=
  .ofFExprs #v[bMsbF b * ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16)).toField]

/-- The arithmetic sign fill `m·(65536 − 2^(16−s))`, subtraction-free
(`65536 − v = (65535 / v) · v` for the power-of-two `v = 2^(16−s)`). -/
def sraFillF (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.FExpr (ZMod p) :=
  bMsbF b * (((65535 : Witgen.U64Expr (ZMod p))
      / ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16)))
    * ((65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16))).toField

/-- The 64-bit sign fill `m · 65535`. -/
def mFillF (b : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  bMsbF b * (65535 : ZMod p)

/-- The byte-level shift amount, u64-sorted (bit 5 gated by the 64-bit flag sum). -/
def byteShiftU (c0e : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (c0e.val >>> 4) % 2 + 2 * ((c0e.val >>> 5) % 2)
    * (.ite (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) =? (1 : ZMod p)) 1 0)

/-- The flag-gated one-hot byte-shift selector, as IR. -/
def shiftU16IR (c0e : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[.ite (byteShiftU c0e =? (0 : ℕ)) (hintF 0 + hintF 1 + hintF 2 + hintF 3) 0,
               .ite (byteShiftU c0e =? (1 : ℕ)) (hintF 0 + hintF 1 + hintF 2 + hintF 3) 0,
               .ite (byteShiftU c0e =? (2 : ℕ)) (hintF 0 + hintF 1 + hintF 2 + hintF 3) 0,
               .ite (byteShiftU c0e =? (3 : ℕ)) (hintF 0 + hintF 1 + hintF 2 + hintF 3) 0]

/-- The placed `a[1]` limb of the word branch (`lo[1]`). -/
def loF1 (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) : Witgen.FExpr (ZMod p) :=
  .ite (byteShiftU c0e =? (0 : ℕ)) (lrF b c0e 1 + sraFillF b c0e) (mFillF b)

/-- Result-word cell `j`, mirroring `populateA`'s dispatch: the 64-bit branch places
`limb_result` diagonally by the byte shift with the sign fill on the top surviving limb and
`m·65535` above; the word branch places the low pair and sign-fills with the placed-limb MSB. -/
def aF (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) : ℕ → Witgen.FExpr (ZMod p)
  | 0 => .ite (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) =? (1 : ZMod p))
      (.listGet [lrF b c0e 0, lrF b c0e 1, lrF b c0e 2, lrF b c0e 3 + sraFillF b c0e]
        (byteShiftU c0e))
      (.ite (((hintF 2 : Witgen.FExpr (ZMod p)) + hintF 3) =? (1 : ZMod p))
        (.ite (byteShiftU c0e =? (0 : ℕ)) (lrF b c0e 0) (lrF b c0e 1 + sraFillF b c0e)) 0)
  | 1 => .ite (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) =? (1 : ZMod p))
      (.listGet [lrF b c0e 1, lrF b c0e 2, lrF b c0e 3 + sraFillF b c0e, mFillF b]
        (byteShiftU c0e))
      (.ite (((hintF 2 : Witgen.FExpr (ZMod p)) + hintF 3) =? (1 : ZMod p)) (loF1 b c0e) 0)
  | 2 => .ite (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) =? (1 : ZMod p))
      (.listGet [lrF b c0e 2, lrF b c0e 3 + sraFillF b c0e, mFillF b, mFillF b]
        (byteShiftU c0e))
      (.ite (((hintF 2 : Witgen.FExpr (ZMod p)) + hintF 3) =? (1 : ZMod p))
        (U16MSBOperation.populate_msbF (loF1 b c0e) * (65535 : ZMod p)) 0)
  | 3 => .ite (((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1) =? (1 : ZMod p))
      (.listGet [lrF b c0e 3 + sraFillF b c0e, mFillF b, mFillF b, mFillF b]
        (byteShiftU c0e))
      (.ite (((hintF 2 : Witgen.FExpr (ZMod p)) + hintF 3) =? (1 : ZMod p))
        (U16MSBOperation.populate_msbF (loF1 b c0e) * (65535 : ZMod p)) 0)
  | _ => 0

/-- The result word `a`, as IR. -/
def populateAIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[aF b c0e 0, aF b c0e 1, aF b c0e 2, aF b c0e 3]

/-- The word-variant sign bit, as a one-cell payload. -/
def srwMsbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 1 :=
  .ofFExprs #v[.ite (((hintF 2 : Witgen.FExpr (ZMod p)) + hintF 3) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (aF b c0e 1)) 0]

/-- The five committed flag cells (`is_srl`…`is_sraw`, `(is_srlw + is_sraw)·imm_c`), as IR. -/
def flagsIR (imm_c : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 5 :=
  .ofFExprs #v[hintF 0, hintF 1, hintF 2, hintF 3, (hintF 2 + hintF 3) * .expr imm_c]

/-! ### Eval lemmas (the boundary: IR evaluation = the value-level witness functions) -/

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating a hint-flag leaf is the `hintFlags` accessor cell. -/
theorem hintF_eval (env : ProverEnvironment (ZMod p)) (k : Fin 4) :
    Witgen.FExpr.eval { env := env } (hintF k) = (hintFlags env.hint)[k] := by
  have hdefault : (default : Vector (ZMod p) 4) = #v[0, 0, 0, 0] := rfl
  rw [hintFlags, ← hdefault]
  fin_cases k <;> simp only [hintF, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the inverted power encodings is `vPowersInv` (`2^n >>> s = 2^(n−s)`). -/
theorem vPowersInvIR_eval (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p))
    (c0 : ZMod p) (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    (vPowersInvIR c0e).eval env = vPowersInv c0 := by
  have h16 : 2 ^ (16 - c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  have h8 : 2 ^ (8 - c0.val % 8) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 ^ (4 - c0.val % 4) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  apply Vector.ext
  intro i hi
  simp only [vPowersInvIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · simp only [vPowersInv, circuit_norm, hc0]
    rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.two_pow_shiftRight (by omega)]
  · simp only [vPowersInv, circuit_norm, hc0]
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.two_pow_shiftRight (by omega)]
  · simp only [vPowersInv, circuit_norm, hc0]
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.two_pow_shiftRight (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- The u64 split modulus evaluates to `2^bitShift`. -/
theorem bitModU_toNat (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p))
    (c0 : ZMod p) (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    ((bitModU c0e).eval { env := env }).toNat = 2 ^ (c0.val % 16) := by
  have hs : 2 ^ (c0.val % 16) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [bitModU, circuit_norm, hc0]
  rw [Nat.shiftLeft_eq, one_mul]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the low bit-split is `lowerLimb` (the one-hot bound keeps the effective limbs'
`val`s from wrapping). -/
theorem lowerLimbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1) :
    (lowerLimbIR b c0e).eval env = lowerLimb vb c0 (hintFlags env.hint) := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  have he2 := effVal_lt vb[2] _ he14 u2
  have he3 := effVal_lt vb[3] _ he14 u3
  have hsl : (1 : ℕ) <<< (c0.val % 16) = 2 ^ (c0.val % 16) := by
    rw [Nat.shiftLeft_eq, one_mul]
  have hs64 : 2 ^ (c0.val % 16) < 2 ^ 64 := by
    calc 2 ^ (c0.val % 16) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
      _ < 2 ^ 64 := by norm_num
  apply Vector.ext
  intro i hi
  simp only [lowerLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · simp only [effU, bitModU, lowerLimb, List.getD, List.getElem?_cons_zero,
      Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, circuit_norm, h0]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
  · simp only [effU, bitModU, lowerLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, h1]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
  · simp only [effU, bitModU, lowerLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hintF_eval, h2]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
    norm_num
    congr 2
    omega
  · simp only [effU, bitModU, lowerLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hintF_eval, h3]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
    norm_num
    congr 2
    omega

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the high bit-split is `higherLimb`. -/
theorem higherLimbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1) :
    (higherLimbIR b c0e).eval env = higherLimb vb c0 (hintFlags env.hint) := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  have he2 := effVal_lt vb[2] _ he14 u2
  have he3 := effVal_lt vb[3] _ he14 u3
  have hsl : (1 : ℕ) <<< (c0.val % 16) = 2 ^ (c0.val % 16) := by
    rw [Nat.shiftLeft_eq, one_mul]
  have hs64 : 2 ^ (c0.val % 16) < 2 ^ 64 := by
    calc 2 ^ (c0.val % 16) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
      _ < 2 ^ 64 := by norm_num
  apply Vector.ext
  intro i hi
  simp only [higherLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · simp only [effU, bitModU, higherLimb, List.getD, List.getElem?_cons_zero,
      Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, circuit_norm, h0]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
  · simp only [effU, bitModU, higherLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, h1]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
  · simp only [effU, bitModU, higherLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hintF_eval, h2]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
    norm_num
    congr 2
    omega
  · simp only [effU, bitModU, higherLimb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hintF_eval, h3]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]
    norm_num
    congr 2
    omega

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating a `limb_result` cell is `limbResult`'s cell (the recombined parts stay below
`2^16`). -/
theorem lrF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1)
    (i : ℕ) (hi : i < 4) :
    Witgen.FExpr.eval { env := env } (lrF b c0e i)
      = (limbResult vb c0 (hintFlags env.hint))[i] := by
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  have he2 := effVal_lt vb[2] _ he14 u2
  have he3 := effVal_lt vb[3] _ he14 u3
  have hsl : (1 : ℕ) <<< (c0.val % 16) = 2 ^ (c0.val % 16) := by
    rw [Nat.shiftLeft_eq, one_mul]
  have hs64 : 2 ^ (c0.val % 16) < 2 ^ 64 := by
    calc 2 ^ (c0.val % 16) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
      _ < 2 ^ 64 := by norm_num
  have hshift : (65536 : ℕ) >>> (c0.val % 16) = 2 ^ (16 - c0.val % 16) := by
    rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.two_pow_shiftRight (by omega)]
  have hApos : 0 < 2 ^ (c0.val % 16) := Nat.pow_pos (by omega)
  have hpow : 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) = 2 ^ 16 := by
    rw [← pow_add]
    congr 1
    omega
  have hBpos : 0 < 2 ^ (16 - c0.val % 16) := Nat.pow_pos (by omega)
  have hprod : ∀ x : ℕ, x % 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) < 2 ^ 16 := fun x =>
    lt_of_lt_of_le (mul_lt_mul_of_pos_right (Nat.mod_lt x hApos) hBpos) (le_of_eq hpow)
  have hp0 := hprod vb[0].val
  have hp1 := hprod vb[1].val
  have hp2 := hprod (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[2]).val
  have hp3 := hprod (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[3]).val
  have hd0 : vb[0].val / 2 ^ (c0.val % 16) ≤ vb[0].val := Nat.div_le_self _ _
  have hd1 : vb[1].val / 2 ^ (c0.val % 16) ≤ vb[1].val := Nat.div_le_self _ _
  have hd2 : (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[2]).val
      / 2 ^ (c0.val % 16) ≤ (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[2]).val :=
    Nat.div_le_self _ _
  have hd3 : (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[3]).val
      / 2 ^ (c0.val % 16) ≤ (((hintFlags env.hint)[0] + (hintFlags env.hint)[1]) * vb[3]).val :=
    Nat.div_le_self _ _
  have hF0 : Witgen.FExpr.eval { env := env } (hintF 0) = (hintFlags env.hint)[0] :=
    hintF_eval env 0
  have hF1 : Witgen.FExpr.eval { env := env } (hintF 1) = (hintFlags env.hint)[1] :=
    hintF_eval env 1
  interval_cases i
  · simp only [lrF, effU, bitModU, limbResult, limbResultNat, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      circuit_norm, h0, h1]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      hshift, Nat.mod_eq_of_lt (lt_trans hp1 (by norm_num)), Nat.mod_eq_of_lt (by omega)]
  · simp only [lrF, effU, bitModU, limbResult, limbResultNat, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      circuit_norm, hF0, hF1, h1, h2]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      hshift, Nat.mod_eq_of_lt (lt_trans hp2 (by norm_num)), Nat.mod_eq_of_lt (by omega)]
  · simp only [lrF, effU, bitModU, limbResult, limbResultNat, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      circuit_norm, hF0, hF1, h2, h3]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      hshift, Nat.mod_eq_of_lt (lt_trans hp3 (by norm_num)), Nat.mod_eq_of_lt (by omega)]
  · simp only [lrF, effU, bitModU, limbResult, limbResultNat, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      circuit_norm, hF0, hF1, h3]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the `limb_result` reassembly is `limbResult`. -/
theorem limbResultIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1) :
    (limbResultIR b c0e).eval env = limbResult vb c0 (hintFlags env.hint) := by
  apply Vector.ext
  intro i hi
  simp only [limbResultIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simpa using lrF_eval env b c0e vb c0 hW hc0 hbU hb he14 _ (by omega)

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the arithmetic sign bit is `bMsb`. -/
theorem bMsbF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (vb : Word (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hbU : vb.isU64) :
    Witgen.FExpr.eval { env := env } (bMsbF b) = bMsb vb (hintFlags env.hint) := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  have hexpr1 : Witgen.FExpr.eval { env := env } (Witgen.FExpr.expr b[1]) = vb[1] := by
    simp only [circuit_norm, hW 1 (by omega)]
  have hexpr3 : Witgen.FExpr.eval { env := env } (Witgen.FExpr.expr b[3]) = vb[3] := by
    simp only [circuit_norm, hW 3 (by omega)]
  have hm3 : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF (.expr b[3]))
      = U16MSBOperation.populate_msb vb[3] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexpr3]; exact u3), hexpr3]
  have hm1 : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF (.expr b[1]))
      = U16MSBOperation.populate_msb vb[1] := by
    rw [U16MSBOperation.populate_msbF_eval { env := env } _ (by rw [hexpr1]; exact u1), hexpr1]
  simp only [bMsbF, bMsb, circuit_norm, hintF_eval, hm3, hm1]

omit [Fact (2 ^ 17 < p)] in
/-- The sign bit as a one-cell payload. -/
theorem bMsbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (vb : Word (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hbU : vb.isU64) :
    (bMsbIR b).eval env = #v[bMsb vb (hintFlags env.hint)] := by
  apply Vector.ext
  intro i hi
  simp only [bMsbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simpa using bMsbF_eval env b vb hW hbU

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the committed `b_msb · v_0123` product is `sraMsbV0123`. -/
theorem sraMsbV0123IR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (sraMsbV0123IR b c0e).eval env = #v[sraMsbV0123 vb c0 (hintFlags env.hint)] := by
  have hbm := bMsbF_eval env b vb hW hbU
  have h16 : 2 ^ (16 - c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  apply Vector.ext
  intro i hi
  simp only [sraMsbV0123IR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simp only [sraMsbV0123, vPowersInv, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, circuit_norm, hbm, hc0]
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.two_pow_shiftRight (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the arithmetic sign fill is `m·65536 − m·2^(16−s)` (the `populateA` shape). -/
theorem sraFillF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } (sraFillF b c0e)
      = bMsb vb (hintFlags env.hint) * 65536
        - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p) := by
  have hbm := bMsbF_eval env b vb hW hbU
  have hfill : (65535 : ℕ) / 2 ^ (16 - c0.val % 16) * 2 ^ (16 - c0.val % 16)
      = 65536 - 2 ^ (16 - c0.val % 16) := by
    set t := c0.val % 16 with ht
    have ht16 : t < 16 := Nat.mod_lt _ (by omega)
    clear_value t
    interval_cases t <;> norm_num
  have h16 : 2 ^ (16 - c0.val % 16) ≤ 65536 := by
    calc 2 ^ (16 - c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 65536 := by norm_num
  simp only [sraFillF, circuit_norm, hbm, hc0]
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.two_pow_shiftRight (by omega)]
  rw [show (2 ^ 16 : ℕ) = 65536 by norm_num] at *
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self 65535 _) (by norm_num)), hfill,
    Nat.cast_sub h16]
  push_cast
  ring

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the u64 byte-shift amount is `byteShiftNat`. -/
theorem byteShiftU_toNat (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p))
    (c0 : ZMod p) (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    ((byteShiftU c0e).eval { env := env }).toNat = byteShiftNat c0 (hintFlags env.hint) := by
  simp only [byteShiftU, byteShiftNat, circuit_norm, hc0, hintF_eval, apply_ite UInt64.toNat]
  split_ifs <;> omega

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the byte-shift selector is `shiftU16`. -/
theorem shiftU16IR_eval (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p))
    (c0 : ZMod p) (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    (shiftU16IR c0e).eval env = shiftU16 c0 (hintFlags env.hint) := by
  have hbs := byteShiftU_toNat env c0e c0 hc0 hb
  apply Vector.ext
  intro i hi
  simp only [shiftU16IR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [shiftU16, circuit_norm, hintF_eval, hbs]

/-- Evaluating a result-word cell is `populateA`'s cell (the variant dispatch resolves branch by
branch; the 64-bit placement's `.listGet` lands in range by `byteShiftNat_lt`). -/
theorem aF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (hf0 : (hintFlags env.hint)[0] = 0 ∨ (hintFlags env.hint)[0] = 1)
    (hf1 : (hintFlags env.hint)[1] = 0 ∨ (hintFlags env.hint)[1] = 1)
    (hf2 : (hintFlags env.hint)[2] = 0 ∨ (hintFlags env.hint)[2] = 1)
    (hf3 : (hintFlags env.hint)[3] = 0 ∨ (hintFlags env.hint)[3] = 1)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1)
    (hone : (hintFlags env.hint)[1] = 1 → (hintFlags env.hint)[3] = 0)
    (hsum01 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 1)
    (j : ℕ) (hj : j < 4) :
    Witgen.FExpr.eval { env := env } (aF b c0e j)
      = (populateA vb c0 (hintFlags env.hint))[j] := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  have hbs := byteShiftU_toNat env c0e c0 hc0 hb
  have hlr := lrF_eval env b c0e vb c0 hW hc0 hbU hb he14
  have hbm := bMsbF_eval env b vb hW hbU
  have hfillE := sraFillF_eval env b c0e vb c0 hW hc0 hbU hb
  have hmfE : Witgen.FExpr.eval { env := env } (mFillF b)
      = bMsb vb (hintFlags env.hint) * 65535 := by
    simp only [mFillF, circuit_norm, hbm]
  have hF0 : Witgen.FExpr.eval { env := env } (hintF 0) = (hintFlags env.hint)[0] :=
    hintF_eval env 0
  have hF1 : Witgen.FExpr.eval { env := env } (hintF 1) = (hintFlags env.hint)[1] :=
    hintF_eval env 1
  have hF2 : Witgen.FExpr.eval { env := env } (hintF 2) = (hintFlags env.hint)[2] :=
    hintF_eval env 2
  have hF3 : Witgen.FExpr.eval { env := env } (hintF 3) = (hintFlags env.hint)[3] :=
    hintF_eval env 3
  have hmb := bMsb_bool vb (hintFlags env.hint) hbU hf1 hf3 hone
  have hlrv := fun i hi => limbResult_val_lt vb c0 (hintFlags env.hint) hbU he14 i hi
  have hk4 : byteShiftNat c0 (hintFlags env.hint) < 4 := byteShiftNat_lt c0 _
  set k := byteShiftNat c0 (hintFlags env.hint) with hkeq
  clear_value k
  have hvinv : ((vPowersInv c0)[0] : ZMod p) = ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p) := by
    simp [vPowersInv]
  interval_cases j <;> by_cases h64 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1
  · interval_cases k <;>
      (simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, if_true, hbs,
        Witgen.FExpr.evalList, hlr 0 (by omega), hlr 1 (by omega), hlr 2 (by omega),
        hlr 3 (by omega), hfillE, hvinv]
       norm_num [← hkeq])
  · by_cases hw : (hintFlags env.hint)[2] + (hintFlags env.hint)[3] = 1
    · simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_true, if_false,
        hbs, hlr 0 (by omega), hlr 1 (by omega), hfillE, hvinv]
      split_ifs
      all_goals first | rfl | omega
    · simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_false]
  · interval_cases k <;>
      (simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, if_true, hbs,
        Witgen.FExpr.evalList, hlr 1 (by omega), hlr 2 (by omega),
        hlr 3 (by omega), hfillE, hmfE, hvinv]
       norm_num [← hkeq])
  · by_cases hw : (hintFlags env.hint)[2] + (hintFlags env.hint)[3] = 1
    · simp only [aF, loF1, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_true,
        if_false, hbs, hlr 1 (by omega), hfillE, hmfE, hvinv]
      split_ifs <;> first | rfl | omega
    · simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_false]
  · interval_cases k <;>
      (simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, if_true, hbs,
        Witgen.FExpr.evalList, hlr 2 (by omega),
        hlr 3 (by omega), hfillE, hmfE, hvinv]
       norm_num [← hkeq])
  · by_cases hw : (hintFlags env.hint)[2] + (hintFlags env.hint)[3] = 1
    · have hval1 := populateA_val_lt vb c0 (hintFlags env.hint) hbU hf0 hf1 hf2 hf3 hsum01
        1 (by omega)
      have hplace : (populateA vb c0 (hintFlags env.hint))[1]
          = if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
              + (bMsb vb (hintFlags env.hint) * 65536
                - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
            else bMsb vb (hintFlags env.hint) * 65535 := by
        simp only [populateA, if_neg (by simpa using h64), if_pos hw, hvinv, ← hkeq,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
        split_ifs <;> rfl
      have hloE : Witgen.FExpr.eval { env := env } (loF1 b c0e)
          = if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
              + (bMsb vb (hintFlags env.hint) * 65536
                - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
            else bMsb vb (hintFlags env.hint) * 65535 := by
        simp only [loF1, circuit_norm, hbs, hlr 1 (by omega), hfillE, hmfE]
      have hmsbE : Witgen.FExpr.eval { env := env }
          (U16MSBOperation.populate_msbF (loF1 b c0e))
          = U16MSBOperation.populate_msb
              (if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
                  + (bMsb vb (hintFlags env.hint) * 65536
                    - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
                else bMsb vb (hintFlags env.hint) * 65535) := by
        rw [U16MSBOperation.populate_msbF_eval { env := env } _
          (by rw [hloE, ← hplace]; exact hval1), hloE]
      simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_true, if_false,
        hbs, hmsbE, hvinv]
      split_ifs <;> first | rfl | omega
    · simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_false]
  · interval_cases k <;>
      (simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, if_true, hbs,
        Witgen.FExpr.evalList,
        hlr 3 (by omega), hfillE, hmfE, hvinv]
       norm_num [← hkeq])
  · by_cases hw : (hintFlags env.hint)[2] + (hintFlags env.hint)[3] = 1
    · have hval1 := populateA_val_lt vb c0 (hintFlags env.hint) hbU hf0 hf1 hf2 hf3 hsum01
        1 (by omega)
      have hplace : (populateA vb c0 (hintFlags env.hint))[1]
          = if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
              + (bMsb vb (hintFlags env.hint) * 65536
                - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
            else bMsb vb (hintFlags env.hint) * 65535 := by
        simp only [populateA, if_neg (by simpa using h64), if_pos hw, hvinv, ← hkeq,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
        split_ifs <;> rfl
      have hloE : Witgen.FExpr.eval { env := env } (loF1 b c0e)
          = if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
              + (bMsb vb (hintFlags env.hint) * 65536
                - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
            else bMsb vb (hintFlags env.hint) * 65535 := by
        simp only [loF1, circuit_norm, hbs, hlr 1 (by omega), hfillE, hmfE]
      have hmsbE : Witgen.FExpr.eval { env := env }
          (U16MSBOperation.populate_msbF (loF1 b c0e))
          = U16MSBOperation.populate_msb
              (if k = 0 then (limbResult vb c0 (hintFlags env.hint))[1]
                  + (bMsb vb (hintFlags env.hint) * 65536
                    - bMsb vb (hintFlags env.hint) * ((2 ^ (16 - c0.val % 16) : ℕ) : ZMod p))
                else bMsb vb (hintFlags env.hint) * 65535) := by
        rw [U16MSBOperation.populate_msbF_eval { env := env } _
          (by rw [hloE, ← hplace]; exact hval1), hloE]
      simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_true, if_false,
        hbs, hmsbE, hvinv]
      split_ifs <;> first | rfl | omega
    · simp only [aF, populateA, circuit_norm, hF0, hF1, hF2, hF3, h64, hw, if_false]

/-- Evaluating the result word is `populateA`. -/
theorem populateAIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (hf0 : (hintFlags env.hint)[0] = 0 ∨ (hintFlags env.hint)[0] = 1)
    (hf1 : (hintFlags env.hint)[1] = 0 ∨ (hintFlags env.hint)[1] = 1)
    (hf2 : (hintFlags env.hint)[2] = 0 ∨ (hintFlags env.hint)[2] = 1)
    (hf3 : (hintFlags env.hint)[3] = 0 ∨ (hintFlags env.hint)[3] = 1)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1)
    (hone : (hintFlags env.hint)[1] = 1 → (hintFlags env.hint)[3] = 0)
    (hsum01 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 1) :
    (populateAIR b c0e).eval env = populateA vb c0 (hintFlags env.hint) := by
  apply Vector.ext
  intro i hi
  simp only [populateAIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simpa using aF_eval env b c0e vb c0 hW hc0 hbU hb hf0 hf1 hf2 hf3 he14 hone hsum01
      _ (by omega)

/-- Evaluating the word-variant sign bit is `srwMsb`. -/
theorem srwMsbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16)
    (hf0 : (hintFlags env.hint)[0] = 0 ∨ (hintFlags env.hint)[0] = 1)
    (hf1 : (hintFlags env.hint)[1] = 0 ∨ (hintFlags env.hint)[1] = 1)
    (hf2 : (hintFlags env.hint)[2] = 0 ∨ (hintFlags env.hint)[2] = 1)
    (hf3 : (hintFlags env.hint)[3] = 0 ∨ (hintFlags env.hint)[3] = 1)
    (he14 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] = 1)
    (hone : (hintFlags env.hint)[1] = 1 → (hintFlags env.hint)[3] = 0)
    (hsum01 : (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 0
      ∨ (hintFlags env.hint)[0] + (hintFlags env.hint)[1] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[3] = 1) :
    (srwMsbIR b c0e).eval env = #v[srwMsb vb c0 (hintFlags env.hint)] := by
  have ha1 := aF_eval env b c0e vb c0 hW hc0 hbU hb hf0 hf1 hf2 hf3 he14 hone hsum01
    1 (by omega)
  have ha1v := populateA_val_lt vb c0 (hintFlags env.hint) hbU hf0 hf1 hf2 hf3 hsum01
    1 (by omega)
  have hmsbA : Witgen.FExpr.eval { env := env }
      (U16MSBOperation.populate_msbF (aF b c0e 1))
      = U16MSBOperation.populate_msb (populateA vb c0 (hintFlags env.hint))[1] := by
    rw [U16MSBOperation.populate_msbF_eval _ _ (by rw [ha1]; exact ha1v), ha1]
  apply Vector.ext
  intro i hi
  simp only [srwMsbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simp only [srwMsb, circuit_norm, hintF_eval, hmsbA]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the committed flag cells is the flag/`is_srw_imm` quintuple. -/
theorem flagsIR_eval (env : ProverEnvironment (ZMod p)) (imm_c : Expression (ZMod p)) :
    (flagsIR imm_c).eval env
      = #v[(hintFlags env.hint)[0], (hintFlags env.hint)[1], (hintFlags env.hint)[2],
           (hintFlags env.hint)[3],
           ((hintFlags env.hint)[2] + (hintFlags env.hint)[3])
             * Expression.eval env.toEnvironment imm_c] := by
  apply Vector.ext
  intro i hi
  simp only [flagsIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [circuit_norm, hintF_eval]

/-! ### Congruence lemmas (environment-locality — the `ComputableWitnesses` counterparts; no
bounds, `-Witgen.u64Wrap` per the fold rule) -/

section Congr

omit [Fact (2 ^ 17 < p)]

variable (env env' : ProverEnvironment (ZMod p))

/-- Congruence for the inverted power encodings. -/
theorem vPowersInvIR_congr (c0e : Expression (ZMod p))
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (vPowersInvIR c0e).eval env = (vPowersInvIR c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [vPowersInvIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [circuit_norm, -Witgen.u64Wrap, hc]

/-- Congruence for the low bit-split. -/
theorem lowerLimbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (lowerLimbIR b c0e).eval env = (lowerLimbIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [lowerLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [effU, bitModU, hintF, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, circuit_norm, -Witgen.u64Wrap,
      hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega), hc, hh]

/-- Congruence for the high bit-split. -/
theorem higherLimbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (higherLimbIR b c0e).eval env = (higherLimbIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [higherLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [effU, bitModU, hintF, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, circuit_norm, -Witgen.u64Wrap,
      hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega), hc, hh]

/-- Congruence for a `limb_result` cell. -/
theorem lrF_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) (i : ℕ) :
    Witgen.FExpr.eval { env := env } (lrF b c0e i)
      = Witgen.FExpr.eval { env := env' } (lrF b c0e i) := by
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · interval_cases i <;>
      simp only [lrF, effU, bitModU, hintF, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, circuit_norm, -Witgen.u64Wrap,
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega), hc, hh]
  · have hz : lrF b c0e i = 0 := by
      simp only [lrF]
      rw [List.getD_eq_default]
      simp
      omega
    rw [hz]
    rfl

/-- Congruence for the `limb_result` reassembly. -/
theorem limbResultIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (limbResultIR b c0e).eval env = (limbResultIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [limbResultIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · exact lrF_congr env env' b c0e hB hc hh 0
  · exact lrF_congr env env' b c0e hB hc hh 1
  · exact lrF_congr env env' b c0e hB hc hh 2
  · exact lrF_congr env env' b c0e hB hc hh 3

/-- Congruence for the arithmetic sign bit. -/
theorem bMsbF_congr (b : Word (Expression (ZMod p)))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hh : env.hint = env'.hint) :
    Witgen.FExpr.eval { env := env } (bMsbF b)
      = Witgen.FExpr.eval { env := env' } (bMsbF b) := by
  have hm3 := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (.expr b[3]) (by simpa [circuit_norm] using hB 3 (by omega))
  have hm1 := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (.expr b[1]) (by simpa [circuit_norm] using hB 1 (by omega))
  simp only [bMsbF, hintF, circuit_norm, -Witgen.u64Wrap, hm3, hm1, hh]

/-- Congruence for the one-cell sign-bit payload. -/
theorem bMsbIR_congr (b : Word (Expression (ZMod p)))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hh : env.hint = env'.hint) :
    (bMsbIR b).eval env = (bMsbIR b).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [bMsbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simpa using bMsbF_congr env env' b hB hh

/-- Congruence for the `b_msb · v_0123` product. -/
theorem sraMsbV0123IR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (sraMsbV0123IR b c0e).eval env = (sraMsbV0123IR b c0e).eval env' := by
  have hbm := bMsbF_congr env env' b hB hh
  apply Vector.ext
  intro i hi
  simp only [sraMsbV0123IR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simp only [circuit_norm, -Witgen.u64Wrap, hbm, hc]

/-- Congruence for the arithmetic sign fill. -/
theorem sraFillF_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    Witgen.FExpr.eval { env := env } (sraFillF b c0e)
      = Witgen.FExpr.eval { env := env' } (sraFillF b c0e) := by
  have hbm := bMsbF_congr env env' b hB hh
  simp only [sraFillF, circuit_norm, -Witgen.u64Wrap, hbm, hc]

/-- Congruence for the 64-bit sign fill. -/
theorem mFillF_congr (b : Word (Expression (ZMod p)))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hh : env.hint = env'.hint) :
    Witgen.FExpr.eval { env := env } (mFillF b)
      = Witgen.FExpr.eval { env := env' } (mFillF b) := by
  have hbm := bMsbF_congr env env' b hB hh
  simp only [mFillF, circuit_norm, -Witgen.u64Wrap, hbm]

/-- Congruence for the byte-shift selector. -/
theorem shiftU16IR_congr (c0e : Expression (ZMod p))
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (shiftU16IR c0e).eval env = (shiftU16IR c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [shiftU16IR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [byteShiftU, hintF, circuit_norm, -Witgen.u64Wrap, hc, hh]

/-- Congruence for a result-word cell. -/
theorem aF_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) (j : ℕ) :
    Witgen.FExpr.eval { env := env } (aF b c0e j)
      = Witgen.FExpr.eval { env := env' } (aF b c0e j) := by
  have hlr0 := lrF_congr env env' b c0e hB hc hh 0
  have hlr1 := lrF_congr env env' b c0e hB hc hh 1
  have hlr2 := lrF_congr env env' b c0e hB hc hh 2
  have hlr3 := lrF_congr env env' b c0e hB hc hh 3
  have hfl := sraFillF_congr env env' b c0e hB hc hh
  have hmf := mFillF_congr env env' b hB hh
  have hEL : ∀ (n : ℕ) (l : List (Witgen.FExpr (ZMod p))),
      (∀ x ∈ l, Witgen.FExpr.eval { env := env } x = Witgen.FExpr.eval { env := env' } x) →
      Witgen.FExpr.evalList { env := env } n l = Witgen.FExpr.evalList { env := env' } n l := by
    intro n l
    induction l generalizing n with
    | nil => intro _; rfl
    | cons a t ih =>
      intro h
      cases n with
      | zero => exact h a (List.mem_cons_self ..)
      | succ m => exact ih m fun x hx => h x (List.mem_cons_of_mem _ hx)
  have hsum : ∀ i : ℕ, Witgen.FExpr.eval { env := env } (lrF b c0e i + sraFillF b c0e)
      = Witgen.FExpr.eval { env := env' } (lrF b c0e i + sraFillF b c0e) := fun i => by
    simp only [circuit_norm, -Witgen.u64Wrap, lrF_congr env env' b c0e hB hc hh i, hfl]
  have hloC : Witgen.FExpr.eval { env := env } (loF1 b c0e)
      = Witgen.FExpr.eval { env := env' } (loF1 b c0e) := by
    simp only [loF1, byteShiftU, hintF, circuit_norm, -Witgen.u64Wrap, hc, hh, hlr1, hfl, hmf]
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (loF1 b c0e) hloC
  rcases Nat.lt_or_ge j 4 with hlt | hge
  · interval_cases j <;>
      (simp only [aF, byteShiftU, hintF, circuit_norm, -Witgen.u64Wrap, hc, hh, hmsbC, hloC,
        hlr0, hlr1, hfl]
       rw [hEL _ _ (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          first
            | rfl
            | exact hlr0
            | exact hlr1
            | exact hlr2
            | exact hlr3
            | exact hsum 0
            | exact hsum 1
            | exact hsum 2
            | exact hsum 3
            | exact hmf)])
  · have hz : aF b c0e j = 0 := by
      unfold aF
      split <;> first | rfl | omega
    rw [hz]
    rfl

/-- Congruence for the result word. -/
theorem populateAIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (populateAIR b c0e).eval env = (populateAIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [populateAIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · exact aF_congr env env' b c0e hB hc hh 0
  · exact aF_congr env env' b c0e hB hc hh 1
  · exact aF_congr env env' b c0e hB hc hh 2
  · exact aF_congr env env' b c0e hB hc hh 3

/-- Congruence for the word-variant sign bit. -/
theorem srwMsbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (srwMsbIR b c0e).eval env = (srwMsbIR b c0e).eval env' := by
  have ha1 := aF_congr env env' b c0e hB hc hh 1
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (aF b c0e 1) ha1
  apply Vector.ext
  intro i hi
  simp only [srwMsbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simp only [hintF, circuit_norm, -Witgen.u64Wrap, hmsbC, hh]

/-- Congruence for the committed flag cells. -/
theorem flagsIR_congr (imm_c : Expression (ZMod p))
    (himm : Expression.eval env.toEnvironment imm_c = Expression.eval env'.toEnvironment imm_c)
    (hh : env.hint = env'.hint) :
    (flagsIR imm_c).eval env = (flagsIR imm_c).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [flagsIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [hintF, circuit_norm, -Witgen.u64Wrap, himm, hh]

end Congr

end WitnessIR

end SP1Clean.ShiftRightChip
