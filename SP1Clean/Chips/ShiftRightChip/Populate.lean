import SP1Clean.Chips.ShiftLeftChip.Populate

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
  have hp := Fact.out (p := 2 ^ 17 < p)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    · intro h
      first
        | (have := congrArg ZMod.val h
           rw [show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) by push_cast; rfl,
             ZMod.val_natCast_of_lt (by omega)] at this
           simp [ZMod.val_zero, ZMod.val_one] at this)
        | (have := congrArg ZMod.val h
           rw [show ((3 : ZMod p)) = ((3 : ℕ) : ZMod p) by push_cast; rfl,
             ZMod.val_natCast_of_lt (by omega)] at this
           simp [ZMod.val_zero, ZMod.val_one] at this)
        | (have := congrArg ZMod.val h
           rw [show ((4 : ZMod p)) = ((4 : ℕ) : ZMod p) by push_cast; rfl,
             ZMod.val_natCast_of_lt (by omega)] at this
           simp [ZMod.val_zero, ZMod.val_one] at this)

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
    · have h4 : x % 4 = x % 2 + 2 * (x / 2 % 2) := by omega
      rw [h4, h0, h1]; norm_num

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
      · have h4 : c0.val % 4 = c0.val % 2 + 2 * (c0.val / 2 % 2) := by omega
        rw [h4, h0, h1]
        norm_num
  · rcases Nat.mod_two_eq_zero_or_one (c0.val / 4) with h | h
    · have h8 : c0.val % 8 = c0.val % 4 := by omega
      have hd : 8 - c0.val % 4 = 4 - c0.val % 4 + 4 := by omega
      rw [h8, h, hd, pow_add]
      push_cast
      ring
    · have h8 : c0.val % 8 = c0.val % 4 + 4 := by omega
      have hd : 8 - (c0.val % 4 + 4) = 4 - c0.val % 4 := by omega
      rw [h8, h, hd]
      push_cast
      ring
  · rcases Nat.mod_two_eq_zero_or_one (c0.val / 8) with h | h
    · have h16 : c0.val % 16 = c0.val % 8 := by omega
      have hd : 16 - c0.val % 8 = 8 - c0.val % 8 + 8 := by omega
      rw [h16, h, hd, pow_add]
      push_cast
      ring
    · have h16 : c0.val % 16 = c0.val % 8 + 8 := by omega
      have hd : 16 - (c0.val % 8 + 8) = 8 - c0.val % 8 := by omega
      rw [h16, h, hd]
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
      · obtain ⟨hz0, hz1, hz2⟩ := h3 hb3
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
    · -- word variants or padding: `e14 = 0`
      rcases hf2 with h2 | h2
      · rcases hf3 with h3 | h3
        · -- padding
          simp [h0, h1, h2, h3, populateA, srwMsb, shiftU16]
        · -- SRAW
          obtain ⟨-, -, hz2⟩ := ho3 h3
          have hk2 : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 := by
            have := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
            unfold byteShiftNat
            rw [h0, h1, if_neg (by rw [zero_add]; exact zero_ne_one)]
            omega
          rcases hk2 with hbs | hbs <;>
            · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h0, h1, hz2, h3, hbs]
              norm_num
              ring
      · -- SRLW
        obtain ⟨-, -, hz3⟩ := ho2 h2
        have hk2 : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 := by
          have := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
          unfold byteShiftNat
          rw [h0, h1, if_neg (by rw [zero_add]; exact zero_ne_one)]
          omega
        rcases hk2 with hbs | hbs <;>
          · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h0, h1, h2, hz3, hbs]
            norm_num
            ring
    · -- SRA
      obtain ⟨hz0, hz2, hz3⟩ := ho1 h1
      have hk4 := byteShiftNat_lt c0 f
      have hcases : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
          ∨ byteShiftNat c0 f = 3 := by omega
      rcases hcases with hbs | hbs | hbs | hbs <;>
        · simp only [populateA, srwMsb, shiftU16, sraMsbV0123, h1, hz0, hz2, hz3, hbs]
          norm_num
          ring
  · -- SRL
    obtain ⟨hz1, hz2, hz3⟩ := ho0 h0
    have hk4 := byteShiftNat_lt c0 f
    have hcases : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
        ∨ byteShiftNat c0 f = 3 := by omega
    rcases hcases with hbs | hbs | hbs | hbs <;>
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

/-- Each `lower_limb` entry's `.val` is below `2^bitShift`. -/
theorem lowerLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (i : ℕ) (hi : i < 4) : (lowerLimb b c0 f)[i].val < 2 ^ (c0.val % 16) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hpos : 0 < 2 ^ (c0.val % 16) := pow_pos (by norm_num) _
  have hle : 2 ^ (c0.val % 16) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  interval_cases i <;>
    simp only [lowerLimb, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt (b[0]).val hpos; omega)]
    exact Nat.mod_lt _ hpos
  · rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt (b[1]).val hpos; omega)]
    exact Nat.mod_lt _ hpos
  · rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt ((f[0] + f[1]) * b[2]).val hpos; omega)]
    exact Nat.mod_lt _ hpos
  · rw [ZMod.val_natCast_of_lt (by have := Nat.mod_lt ((f[0] + f[1]) * b[3]).val hpos; omega)]
    exact Nat.mod_lt _ hpos

/-- Each `higher_limb` entry's `.val` is below `2^(16 - bitShift)` (u16 effective limbs). -/
theorem higherLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1)
    (i : ℕ) (hi : i < 4) : (higherLimb b c0 f)[i].val < 2 ^ (16 - c0.val % 16) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hpos : 0 < 2 ^ (c0.val % 16) := pow_pos (by norm_num) _
  have key : ∀ x : ℕ, x < 2 ^ 16 → x / 2 ^ (c0.val % 16) < 2 ^ (16 - c0.val % 16) := by
    intro x hx
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    have h16 : 16 - c0.val % 16 + c0.val % 16 = 16 := by omega
    rw [h16]; exact hx
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
  have hs : c0.val % 16 ≤ 15 := by omega
  have key : ∀ (x y : ℕ), x < 2 ^ 16 → y < 2 ^ 16 →
      x / 2 ^ (c0.val % 16) + y % 2 ^ (c0.val % 16) * 2 ^ (16 - c0.val % 16) < 2 ^ 16 := by
    intro x y hx _
    set s := c0.val % 16
    have hpos : 0 < 2 ^ s := pow_pos (by norm_num) _
    have hhigh : x / 2 ^ s < 2 ^ (16 - s) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
      have h16 : 16 - s + s = 16 := by omega
      rw [h16]; exact hx
    have hlow : y % 2 ^ s ≤ 2 ^ s - 1 :=
      Nat.le_sub_one_of_lt (Nat.mod_lt y hpos)
    have hpow : 2 ^ s * 2 ^ (16 - s) = 2 ^ 16 := by
      rw [← pow_add]; congr 1; omega
    calc x / 2 ^ s + y % 2 ^ s * 2 ^ (16 - s)
        ≤ (2 ^ (16 - s) - 1) + (2 ^ s - 1) * 2 ^ (16 - s) := by
          exact Nat.add_le_add (Nat.le_sub_one_of_lt hhigh) (Nat.mul_le_mul_right _ hlow)
      _ < 2 ^ 16 := by
          have h1 : (2 ^ s - 1) * 2 ^ (16 - s) = 2 ^ s * 2 ^ (16 - s) - 2 ^ (16 - s) := by
            rw [Nat.sub_mul, one_mul]
          rw [h1, hpow]
          have h2 : 2 ^ (16 - s) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3 : 1 ≤ 2 ^ (16 - s) := Nat.one_le_two_pow
          omega
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
  have hpos : 0 < 2 ^ (c0.val % 16) := pow_pos (by norm_num) _
  have he3 := effVal_lt (b[3]) (f[0] + f[1]) he14 (Word.lt_cases_of_isU64 hb).2.2.2
  simp only [limbResultNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero]
  rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
  have h16 : 16 - c0.val % 16 + c0.val % 16 = 16 := by omega
  rw [h16]; exact he3

omit [Fact p.Prime] in
/-- `limb_result[1]` is below `2^(16-s)` on word rows (`e14 = 0` zeroes its `lower` summand). -/
private lemma lr1_lt_word (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 4)
    (hb : Word.isU64 b) (hz : f[0] + f[1] = 0) :
    (limbResultNat b c0 f)[1] < 2 ^ (16 - c0.val % 16) := by
  have hpos : 0 < 2 ^ (c0.val % 16) := pow_pos (by norm_num) _
  have hb1 := (Word.lt_cases_of_isU64 hb).2.1
  simp only [limbResultNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, hz, zero_mul, ZMod.val_zero, Nat.zero_mod, add_zero]
  rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
  have h16 : 16 - c0.val % 16 + c0.val % 16 = 16 := by omega
  rw [h16]; exact hb1

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
    · rw [one_mul, show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]
      norm_num
  by_cases h14 : f[0] + f[1] = 1
  · have he14 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1 := Or.inr h14
    have hlr := fun j hj => limbResult_val_lt b c0 f hb he14 j hj
    have hfill := fill_bound b c0 f hbm 3 (by norm_num) (lr3_lt b c0 f hb he14)
    have hk4 := byteShiftNat_lt c0 f
    have hcases : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
        ∨ byteShiftNat c0 f = 3 := by omega
    rcases hcases with hbs | hbs | hbs | hbs <;>
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
  refine ⟨ByteOpcode.Range, by norm_cast, ?_⟩
  simp only [ByteOpcode.constrain]
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
  refine ⟨ByteOpcode.Range, by norm_cast, ?_⟩
  simp only [ByteOpcode.constrain]
  rw [ZMod.val_natCast_of_lt (show 16 - c0.val % 16 < p by omega)]
  exact higherLimb_val_lt b c0 f hb he14 i hi

end ValueLemmas

end SP1Clean.ShiftRightChip
