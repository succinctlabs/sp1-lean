import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Math.ShiftBounds
import SP1Clean.Native.Operations.U16MSBOperation.Populate

/-! # `ShiftLeftChip` — native witness generation (`populate`)

SP1's `ShiftLeftChip::event_to_row` (`alu/sll/mod.rs`) ported to Lean: the honest witness
assignments for the shift column block — the six shift-amount bits `c_bits`, the `v_01/v_012/v_0123`
power encodings, the `shift_u16` byte-shift one-hot selector, the `lower/higher_limb` bit-split, the
`limb_result` reassembly, the SLLW MSB sign-fill, and the result word `a` (computed by the
constraints' own placement formula, so the placement asserts are definitional at the witness). The
variant flags are **not** computable from the row inputs — the prover supplies them via the
`"shift_left_flags"` `ProverHint` key (one-hot on real rows, absent/all-zero on padding); the
committed `is_sllw_imm` is derived as `is_sllw · imm_c`.

Everything is computable (ℕ arithmetic on `.val`, cast back): the `SP1CleanTest` trace-gen anchors
derive whole trace rows from these closures and check them against SP1's real `generate_trace`. On
all-zero inputs + empty hint they reproduce SP1's `padded_row_template`
(`v_01 = v_012 = v_0123 = 1`, everything else zero) — the `v_*` encodings are computed ungated
because their constraints are ungated. -/

namespace SP1Clean.ShiftLeftChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The two honest variant flags (`is_sll`, `is_sllw`) the prover supplies via the
`"shift_left_flags"` hint key (one-hot for the active variant, all-zero on padding). Falls back to
all-zero when the key is absent. -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 2 :=
  ((h "shift_left_flags" 2)[0]?).getD #v[0, 0]

/-- The six low bits of the shift-amount source limb `c0` (= `op_c_memory.prev_value[0]`). -/
def cBits (c0 : ZMod p) : Vector (ZMod p) 6 :=
  #v[(((c0.val >>> 0) % 2 : ℕ) : ZMod p), (((c0.val >>> 1) % 2 : ℕ) : ZMod p),
     (((c0.val >>> 2) % 2 : ℕ) : ZMod p), (((c0.val >>> 3) % 2 : ℕ) : ZMod p),
     (((c0.val >>> 4) % 2 : ℕ) : ZMod p), (((c0.val >>> 5) % 2 : ℕ) : ZMod p)]

/-- The bit-level shift amount: the low four bits of `c0` (`bit_shift = c & 0xF`). -/
def bitShiftNat (c0 : ZMod p) : ℕ := c0.val % 16

/-- The `v_01/v_012/v_0123` power encodings (`2^(c&3), 2^(c&7), 2^(c&15)`), computed ungated —
their constraints are ungated, and on `c0 = 0` they give SP1's padding template `1, 1, 1`. -/
def vPowers (c0 : ZMod p) : Vector (ZMod p) 3 :=
  #v[((2 ^ (c0.val % 4) : ℕ) : ZMod p), ((2 ^ (c0.val % 8) : ℕ) : ZMod p),
     ((2 ^ (c0.val % 16) : ℕ) : ZMod p)]

/-- The byte-level shift amount `(c≫4)&1 + 2·((c≫5)&1)·is_sll` (bit 5 only participates for the
64-bit `SLL`; `SLLW` shifts within 32 bits). -/
def byteShiftNat (c0 : ZMod p) (f : Vector (ZMod p) 2) : ℕ :=
  (c0.val >>> 4) % 2 + 2 * ((c0.val >>> 5) % 2) * (if f[0] = 1 then 1 else 0)

/-- The `shift_u16` byte-shift selector: one-hot at `byteShiftNat`, gated by the flag sum (all-zero
on padding, matching SP1's zero padding template). -/
def shiftU16 (c0 : ZMod p) (f : Vector (ZMod p) 2) : Vector (ZMod p) 4 :=
  let g := f[0] + f[1]
  let k := byteShiftNat c0 f
  #v[if k = 0 then g else 0, if k = 1 then g else 0, if k = 2 then g else 0, if k = 3 then g else 0]

/-- Per-limb bit-split, low part: `lower_limb[i] = b[i] mod 2^(16-bitShift)` (ungated — the split
identity holds for any u16 limb, and gives zero on the all-zero padding row). -/
def lowerLimb (b : Word (ZMod p)) (c0 : ZMod p) : Vector (ZMod p) 4 :=
  let s := bitShiftNat c0
  #v[((b[0].val % 2 ^ (16 - s) : ℕ) : ZMod p), ((b[1].val % 2 ^ (16 - s) : ℕ) : ZMod p),
     ((b[2].val % 2 ^ (16 - s) : ℕ) : ZMod p), ((b[3].val % 2 ^ (16 - s) : ℕ) : ZMod p)]

/-- Per-limb bit-split, high part: `higher_limb[i] = b[i] / 2^(16-bitShift)` (the `bitShift` bits
that overflow into the next limb). -/
def higherLimb (b : Word (ZMod p)) (c0 : ZMod p) : Vector (ZMod p) 4 :=
  let s := bitShiftNat c0
  #v[((b[0].val / 2 ^ (16 - s) : ℕ) : ZMod p), ((b[1].val / 2 ^ (16 - s) : ℕ) : ZMod p),
     ((b[2].val / 2 ^ (16 - s) : ℕ) : ZMod p), ((b[3].val / 2 ^ (16 - s) : ℕ) : ZMod p)]

/-- The `limb_result` reassembly in ℕ: `lr[0] = lower[0]·2^s`, `lr[i] = lower[i]·2^s + higher[i-1]`
— each entry `< 2^16`. -/
def limbResultNat (b : Word (ZMod p)) (c0 : ZMod p) : Vector ℕ 4 :=
  let s := bitShiftNat c0
  #v[(b[0].val % 2 ^ (16 - s)) * 2 ^ s,
     (b[1].val % 2 ^ (16 - s)) * 2 ^ s + b[0].val / 2 ^ (16 - s),
     (b[2].val % 2 ^ (16 - s)) * 2 ^ s + b[1].val / 2 ^ (16 - s),
     (b[3].val % 2 ^ (16 - s)) * 2 ^ s + b[2].val / 2 ^ (16 - s)]

/-- The `limb_result` reassembly as committed field values. -/
def limbResult (b : Word (ZMod p)) (c0 : ZMod p) : Vector (ZMod p) 4 :=
  (limbResultNat b c0).map (fun n : ℕ => (n : ZMod p))

/-- The result word `a`: the constraints' own per-byteShift placement of `limb_result` (SLL shifts
all four limbs up by `byteShift`; SLLW places the low two and sign-fills the upper limbs with
`msb · 65535`), flag-gated to zero on padding. Agrees with SP1's `event.a` — checked cell-for-cell
by the `TraceGenTests` anchor. -/
def populateA (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 2) : Word (ZMod p) :=
  let lr := limbResult b c0
  if f[0] = 1 then
    match byteShiftNat c0 f with
    | 0 => #v[lr[0], lr[1], lr[2], lr[3]]
    | 1 => #v[0, lr[0], lr[1], lr[2]]
    | 2 => #v[0, 0, lr[0], lr[1]]
    | _ => #v[0, 0, 0, lr[0]]
  else if f[1] = 1 then
    let lo : Vector (ZMod p) 2 :=
      if byteShiftNat c0 f = 0 then #v[lr[0], lr[1]] else #v[0, lr[0]]
    let m := U16MSBOperation.populate_msb lo[1]
    #v[lo[0], lo[1], m * 65535, m * 65535]
  else #v[0, 0, 0, 0]

/-- The SLLW sign bit: the MSB of the placed `a[1]` limb, gated to the SLLW variant (zero on SLL
and padding rows, keeping the `U16MSBOperation` booleanness obligation trivial there). -/
def sllwMsb (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 2) : ZMod p :=
  if f[1] = 1 then U16MSBOperation.populate_msb (populateA b c0 f)[1] else 0

/-! ## Value-level constraint lemmas

The completeness proof (`Formal.lean`) pins every witnessed cell to its populate projection and
discharges each inline assertZero by one of these lemmas — all pure `ZMod p`/ℕ facts, stated in the
goal's `circuit_norm` (`+ -`) normal form so the in-context proof is assembly only. -/

section ValueLemmas

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- ℕ core of the `v_01` encoding: `2^(x mod 4)` from the two low bits. -/
private lemma two_pow_mod_four (x : ℕ) :
    2 ^ (x % 4) = (x % 2 + 1) * (x / 2 % 2 * 3 + 1) := by
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h0 <;>
    rcases Nat.mod_two_eq_zero_or_one (x / 2) with h1 | h1 <;>
    · have h4 : x % 4 = x % 2 + 2 * (x / 2 % 2) := by omega
      rw [h4, h0, h1]; norm_num

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- ℕ core of the `v_012` encoding: bit 2 contributes the factor `15 + 1`. -/
private lemma two_pow_mod_eight (x : ℕ) :
    2 ^ (x % 8) = 2 ^ (x % 4) * (x / 4 % 2 * 15 + 1) := by
  rcases Nat.mod_two_eq_zero_or_one (x / 4) with h | h
  · have h8 : x % 8 = x % 4 := by omega
    rw [h8, h]; ring
  · have h8 : x % 8 = x % 4 + 4 := by omega
    rw [h8, h, pow_add]; ring

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- ℕ core of the `v_0123` encoding: bit 3 contributes the factor `255 + 1`. -/
private lemma two_pow_mod_sixteen (x : ℕ) :
    2 ^ (x % 16) = 2 ^ (x % 8) * (x / 8 % 2 * 255 + 1) := by
  rcases Nat.mod_two_eq_zero_or_one (x / 8) with h | h
  · have h16 : x % 16 = x % 8 := by omega
    rw [h16, h]; ring
  · have h16 : x % 16 = x % 8 + 8 := by omega
    rw [h16, h, pow_add]; ring

/-- ℕ core of the split's high part: a u16 divided by `2^(16-s)` is below `2^s`. -/
private lemma div_pow_lt {s x : ℕ} (hs : s ≤ 16) (hx : x < 2 ^ 16) :
    x / 2 ^ (16 - s) < 2 ^ s :=
  Nat.div_lt_of_lt_mul (by rw [← pow_add, show 16 - s + s = 16 from by omega]; exact hx)

omit [Fact (2 ^ 17 < p)] in
/-- Each `c_bits` entry is binary (disjunction form, for the dispatch lemmas). -/
theorem cBits_bool (c0 : ZMod p) (i : ℕ) (hi : i < 6) :
    (cBits c0)[i] = 0 ∨ (cBits c0)[i] = 1 := by
  interval_cases i <;>
    · simp only [cBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rcases Nat.mod_two_eq_zero_or_one (c0.val >>> _) with h | h <;> rw [h] <;> simp

omit [Fact (2 ^ 17 < p)] in
/-- The six `c_bits` booleanness asserts, in goal form. -/
theorem cBits_asserts (c0 : ZMod p) :
    (cBits c0)[0] * ((cBits c0)[0] + -1) = 0 ∧ (cBits c0)[1] * ((cBits c0)[1] + -1) = 0 ∧
    (cBits c0)[2] * ((cBits c0)[2] + -1) = 0 ∧ (cBits c0)[3] * ((cBits c0)[3] + -1) = 0 ∧
    (cBits c0)[4] * ((cBits c0)[4] + -1) = 0 ∧ (cBits c0)[5] * ((cBits c0)[5] + -1) = 0 := by
  have h : ∀ i (hi : i < 6), (cBits c0)[i] * ((cBits c0)[i] + (-1 : ZMod p)) = 0 := fun i hi => by
    rcases cBits_bool c0 i hi with h | h <;> rw [h] <;> simp
  exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num)⟩

omit [Fact (2 ^ 17 < p)] in
/-- The committed byte-shift expression equals the cast of `byteShiftNat` (for binary `f[0]`). -/
theorem byteShift_expr_eq (c0 : ZMod p) (f : Vector (ZMod p) 2) (hf0 : f[0] = 0 ∨ f[0] = 1) :
    (cBits c0)[4] + (cBits c0)[5] * 2 * f[0] = ((byteShiftNat c0 f : ℕ) : ZMod p) := by
  rcases hf0 with h | h <;>
    simp only [cBits, byteShiftNat, h, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, if_pos, zero_ne_one, if_false] <;>
    push_cast <;> ring

set_option linter.unusedSectionVars false in
/-- `byteShiftNat < 4` (each contributing bit is ≤ 1). -/
theorem byteShiftNat_lt (c0 : ZMod p) (f : Vector (ZMod p) 2) : byteShiftNat c0 f < 4 := by
  have h4 := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
  have h5 := Nat.mod_lt (c0.val >>> 5) (show 0 < 2 by norm_num)
  unfold byteShiftNat
  split <;> omega

/-- The eight `shift_u16` selector/boolean asserts plus the gated one-hot sum, in goal form
(for binary `f[0]`, `f[1]` with binary sum). -/
theorem shiftU16_asserts (c0 : ZMod p) (f : Vector (ZMod p) 2)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hsum01 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) :
    (shiftU16 c0 f)[0] * ((cBits c0)[4] + (cBits c0)[5] * 2 * f[0]) = 0 ∧
    (shiftU16 c0 f)[0] * ((shiftU16 c0 f)[0] + -1) = 0 ∧
    (shiftU16 c0 f)[1] * ((cBits c0)[4] + (cBits c0)[5] * 2 * f[0] + -1) = 0 ∧
    (shiftU16 c0 f)[1] * ((shiftU16 c0 f)[1] + -1) = 0 ∧
    (shiftU16 c0 f)[2] * ((cBits c0)[4] + (cBits c0)[5] * 2 * f[0] + -2) = 0 ∧
    (shiftU16 c0 f)[2] * ((shiftU16 c0 f)[2] + -1) = 0 ∧
    (shiftU16 c0 f)[3] * ((cBits c0)[4] + (cBits c0)[5] * 2 * f[0] + -3) = 0 ∧
    (shiftU16 c0 f)[3] * ((shiftU16 c0 f)[3] + -1) = 0 ∧
    (f[0] + f[1]) * ((shiftU16 c0 f)[0] + (shiftU16 c0 f)[1] + (shiftU16 c0 f)[2]
      + (shiftU16 c0 f)[3] + -1) = 0 := by
  rw [byteShift_expr_eq c0 f hf0]
  have hk4 := byteShiftNat_lt c0 f
  simp only [shiftU16, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  set k := byteShiftNat c0 f with hk
  clear_value k
  interval_cases k <;>
    · norm_num
      rcases hsum01 with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; ring)

omit [Fact (2 ^ 17 < p)] in
/-- The three `v_*` power-encoding asserts, in goal form. -/
theorem v_asserts (c0 : ZMod p) :
    (vPowers c0)[0] + -(((cBits c0)[0] + 1) * ((cBits c0)[1] * 3 + 1)) = 0 ∧
    (vPowers c0)[1] + -((vPowers c0)[0] * ((cBits c0)[2] * 15 + 1)) = 0 ∧
    (vPowers c0)[2] + -((vPowers c0)[1] * ((cBits c0)[3] * 255 + 1)) = 0 := by
  simp only [vPowers, cBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.shiftRight_eq_div_pow, pow_zero, pow_one, Nat.div_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [two_pow_mod_four c0.val]; push_cast; ring
  · rw [two_pow_mod_eight c0.val]; push_cast; ring
  · rw [two_pow_mod_sixteen c0.val]; push_cast; ring

omit [Fact (2 ^ 17 < p)] in
/-- One limb's bit-split assert, in goal form: `x·2^s = (x/2^(16-s))·2^16 + (x mod 2^(16-s))·2^s`
(holds for any field element — the Euclidean split needs no bound). -/
private lemma split_cell (c0 x : ZMod p) :
    x * ((2 ^ (c0.val % 16) : ℕ) : ZMod p)
      + -(((x.val / 2 ^ (16 - bitShiftNat c0) : ℕ) : ZMod p) * 65536
          + ((x.val % 2 ^ (16 - bitShiftNat c0) : ℕ) : ZMod p)
            * ((2 ^ (c0.val % 16) : ℕ) : ZMod p)) = 0 := by
  have hpow : 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) = 65536 := by
    rw [← pow_add]
    have h : 16 - c0.val % 16 + c0.val % 16 = 16 := by omega
    rw [h]; norm_num
  have key : x.val * 2 ^ (c0.val % 16)
      = x.val / 2 ^ (16 - c0.val % 16) * 65536
        + x.val % 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) := by
    have hsplit := Nat.div_add_mod x.val (2 ^ (16 - c0.val % 16))
    calc x.val * 2 ^ (c0.val % 16)
        = (2 ^ (16 - c0.val % 16) * (x.val / 2 ^ (16 - c0.val % 16))
            + x.val % 2 ^ (16 - c0.val % 16)) * 2 ^ (c0.val % 16) := by rw [hsplit]
      _ = x.val / 2 ^ (16 - c0.val % 16) * (2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16))
            + x.val % 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) := by ring
      _ = _ := by rw [hpow]
  have hx_eq : x * ((2 ^ (c0.val % 16) : ℕ) : ZMod p)
      = ((x.val * 2 ^ (c0.val % 16) : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  unfold bitShiftNat
  rw [hx_eq, key]
  push_cast
  ring

omit [Fact (2 ^ 17 < p)] in
/-- The four per-limb bit-split asserts, in goal form (`b` the four operand limbs). -/
theorem split_asserts (b : Word (ZMod p)) (c0 : ZMod p) :
    b[0] * (vPowers c0)[2]
      + -((higherLimb b c0)[0] * 65536 + (lowerLimb b c0)[0] * (vPowers c0)[2]) = 0 ∧
    b[1] * (vPowers c0)[2]
      + -((higherLimb b c0)[1] * 65536 + (lowerLimb b c0)[1] * (vPowers c0)[2]) = 0 ∧
    b[2] * (vPowers c0)[2]
      + -((higherLimb b c0)[2] * 65536 + (lowerLimb b c0)[2] * (vPowers c0)[2]) = 0 ∧
    b[3] * (vPowers c0)[2]
      + -((higherLimb b c0)[3] * 65536 + (lowerLimb b c0)[3] * (vPowers c0)[2]) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [vPowers, lowerLimb, higherLimb, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact split_cell c0 _

omit [Fact (2 ^ 17 < p)] in
/-- The four `limb_result` reassembly asserts, in goal form. -/
theorem limbResult_asserts (b : Word (ZMod p)) (c0 : ZMod p) :
    (limbResult b c0)[0] + -((lowerLimb b c0)[0] * (vPowers c0)[2]) = 0 ∧
    (limbResult b c0)[1]
      + -((lowerLimb b c0)[1] * (vPowers c0)[2] + (higherLimb b c0)[0]) = 0 ∧
    (limbResult b c0)[2]
      + -((lowerLimb b c0)[2] * (vPowers c0)[2] + (higherLimb b c0)[1]) = 0 ∧
    (limbResult b c0)[3]
      + -((lowerLimb b c0)[3] * (vPowers c0)[2] + (higherLimb b c0)[2]) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [limbResult, limbResultNat, vPowers, lowerLimb, higherLimb, bitShiftNat,
        Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      push_cast
      ring

/-- `(2 : ZMod p)` is neither `0` nor `1` (so binary flags with a binary sum are one-hot). -/
lemma two_ne_zero_one : (2 : ZMod p) ≠ 0 ∧ (2 : ZMod p) ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have hv := congrArg ZMod.val h
      simp only [val_2_zmod_p, ZMod.val_zero, ZMod.val_one] at hv
      omega

/-- Binary flags with a binary sum are one-hot: `f[0] = 1` forces `f[1] = 0`. -/
lemma flag1_zero_of_flag0_one (f : Vector (ZMod p) 2) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hsum01 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) (h : f[0] = 1) : f[1] = 0 := by
  rcases hf1 with h1 | h1
  · exact h1
  · exfalso
    rw [h, h1] at hsum01
    have h2 := two_ne_zero_one (p := p)
    rcases hsum01 with hs | hs
    · exact h2.1 (by linear_combination hs)
    · exact h2.2 (by linear_combination hs)

/-- The 22 result-placement asserts (16 SLL + 4 SLLW low-limb + 2 SLLW msb sign-fill), in goal
form: at the populate values every placement product vanishes. -/
theorem place_asserts (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 2)
    (hf0 : f[0] = 0 ∨ f[0] = 1) (hf1 : f[1] = 0 ∨ f[1] = 1)
    (hsum01 : f[0] + f[1] = 0 ∨ f[0] + f[1] = 1) :
    f[0] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[0] + -(limbResult b c0)[0])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[1] + -(limbResult b c0)[1])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[2] + -(limbResult b c0)[2])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[3] + -(limbResult b c0)[3])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[1] * (populateA b c0 f)[0]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[1] + -(limbResult b c0)[0])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[2] + -(limbResult b c0)[1])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[3] + -(limbResult b c0)[2])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[2] * (populateA b c0 f)[0]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[2] * (populateA b c0 f)[1]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[2] * ((populateA b c0 f)[2] + -(limbResult b c0)[0])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[2] * ((populateA b c0 f)[3] + -(limbResult b c0)[1])) = 0 ∧
    f[0] * ((shiftU16 c0 f)[3] * (populateA b c0 f)[0]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[3] * (populateA b c0 f)[1]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[3] * (populateA b c0 f)[2]) = 0 ∧
    f[0] * ((shiftU16 c0 f)[3] * ((populateA b c0 f)[3] + -(limbResult b c0)[0])) = 0 ∧
    f[1] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[0] + -(limbResult b c0)[0])) = 0 ∧
    f[1] * ((shiftU16 c0 f)[0] * ((populateA b c0 f)[1] + -(limbResult b c0)[1])) = 0 ∧
    f[1] * ((shiftU16 c0 f)[1] * (populateA b c0 f)[0]) = 0 ∧
    f[1] * ((shiftU16 c0 f)[1] * ((populateA b c0 f)[1] + -(limbResult b c0)[0])) = 0 ∧
    f[1] * (sllwMsb b c0 f * 65535 + -(populateA b c0 f)[2]) = 0 ∧
    f[1] * (sllwMsb b c0 f * 65535 + -(populateA b c0 f)[3]) = 0 := by
  rcases hf0 with hf0 | hf0
  · rcases hf1 with hf1 | hf1
    · -- padding: both flags zero
      simp [hf0, hf1]
    · -- SLLW row: `f[0] = 0`, `f[1] = 1`
      have hk2 : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 := by
        have := Nat.mod_lt (c0.val >>> 4) (show 0 < 2 by norm_num)
        unfold byteShiftNat
        rw [if_neg (by rw [hf0]; exact zero_ne_one)]
        omega
      rcases hk2 with hbs | hbs <;>
        · simp only [populateA, sllwMsb, shiftU16, hf0, hf1, hbs]
          norm_num
  · -- SLL row: `f[0] = 1` (so `f[1] = 0` by one-hotness)
    have hf1z : f[1] = 0 := flag1_zero_of_flag0_one f hf1 hsum01 hf0
    have hk4 := byteShiftNat_lt c0 f
    have hcases : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
        ∨ byteShiftNat c0 f = 3 := by omega
    rcases hcases with hbs | hbs | hbs | hbs <;>
      · simp only [populateA, sllwMsb, shiftU16, hf0, hf1z, hbs]
        norm_num

omit [Fact (Nat.Prime p)] in
/-- Each `limb_result` ℕ entry is `< 2^16` (the split parts recombine within a u16). -/
theorem limbResultNat_lt (b : Word (ZMod p)) (c0 : ZMod p) (hb : Word.isU64 b)
    (i : ℕ) (hi : i < 4) : (limbResultNat b c0)[i] < 2 ^ 16 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  have hs : c0.val % 16 ≤ 15 := by omega
  have key : ∀ (x y : ℕ), x < 2 ^ 16 → y < 2 ^ 16 →
      x % 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) + y / 2 ^ (16 - c0.val % 16) < 2 ^ 16 := by
    intro x y _ hy
    set s := c0.val % 16
    have hpow : 2 ^ (16 - s) * 2 ^ s = 65536 := by
      rw [← pow_add, show 16 - s + s = 16 by omega]; norm_num
    exact ShiftBounds.hi_lo_lt hpow (Nat.mod_lt _ (pow_pos (by norm_num) _))
      (div_pow_lt (by omega) hy)
  interval_cases i <;>
    simp only [limbResultNat, bitShiftNat, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact lt_of_le_of_lt (Nat.le_add_right _ _) (key _ _ hb0 hb0)
  · exact key _ _ hb1 hb0
  · exact key _ _ hb2 hb1
  · exact key _ _ hb3 hb2

/-- Each `limb_result` field entry has `.val < 2^16`. -/
theorem limbResult_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (hb : Word.isU64 b)
    (i : ℕ) (hi : i < 4) : (limbResult b c0)[i].val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have h := limbResultNat_lt b c0 hb i hi
  simp only [limbResult, Vector.getElem_map]
  rw [ZMod.val_natCast_of_lt (by omega)]
  exact h

/-- Each placed result limb has `.val < 2^16` (`limb_result` entry, `msb·65535`, or `0`). -/
theorem populateA_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 2)
    (hb : Word.isU64 b) (i : ℕ) (hi : i < 4) : (populateA b c0 f)[i].val < 2 ^ 16 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hlr := fun j hj => limbResult_val_lt b c0 hb j hj
  have hzero : (0 : ZMod p).val < 2 ^ 16 := by rw [ZMod.val_zero]; norm_num
  have hmsb : ∀ x : ZMod p, x.val < 2 ^ 16 →
      (U16MSBOperation.populate_msb x * 65535).val < 2 ^ 16 := by
    intro x hx
    rcases U16MSBOperation.populate_msb_bool hx with h | h <;> rw [h]
    · rw [zero_mul, ZMod.val_zero]; norm_num
    · rw [one_mul, val_65535_zmod_p]; norm_num
  by_cases h0 : f[0] = 1
  · have hk4 := byteShiftNat_lt c0 f
    have hcases : byteShiftNat c0 f = 0 ∨ byteShiftNat c0 f = 1 ∨ byteShiftNat c0 f = 2
        ∨ byteShiftNat c0 f = 3 := by omega
    rcases hcases with hbs | hbs | hbs | hbs <;>
      · simp only [populateA, h0, hbs, if_true]
        interval_cases i <;>
          first | exact hlr _ (by norm_num) | exact hzero
  · by_cases h1 : f[1] = 1
    · by_cases hbs : byteShiftNat c0 f = 0 <;>
        · simp only [populateA, h0, h1, hbs, if_true, if_false]
          interval_cases i <;>
            first
              | exact hlr _ (by norm_num)
              | exact hzero
              | exact hmsb _ (hlr _ (by norm_num))
    · simp only [populateA, h0, h1, if_false]
      interval_cases i <;> exact hzero

/-- The witnessed SLLW sign bit is boolean. -/
theorem sllwMsb_bool (b : Word (ZMod p)) (c0 : ZMod p) (f : Vector (ZMod p) 2)
    (hb : Word.isU64 b) : sllwMsb b c0 f = 0 ∨ sllwMsb b c0 f = 1 := by
  unfold sllwMsb
  split
  · exact U16MSBOperation.populate_msb_bool (populateA_val_lt b c0 f hb 1 (by norm_num))
  · exact Or.inl rfl

omit [Fact (2 ^ 17 < p)] in
/-- The low-four `c_bits` weighted sum is the cast bit shift (`c0.val mod 16`). -/
theorem cBits_bitShift_sum (c0 : ZMod p) :
    (cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p) + (cBits c0)[2] * (4 : ZMod p)
        + (cBits c0)[3] * (8 : ZMod p)
      = ((c0.val % 16 : ℕ) : ZMod p) := by
  simp only [cBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.shiftRight_eq_div_pow]
  have h : c0.val % 16
      = c0.val / 2 ^ 0 % 2 + (c0.val / 2 ^ 1 % 2) * 2 + (c0.val / 2 ^ 2 % 2) * 4
        + (c0.val / 2 ^ 3 % 2) * 8 := by
    simp only [pow_zero, pow_one, Nat.div_one]
    omega
  rw [h]
  push_cast
  ring

omit [Fact (2 ^ 17 < p)] in
/-- The six-bit `c_bits` weighted sum (the committed `shamt`) is the cast `c0.val mod 64`. -/
theorem cBits_shamt_sum (c0 : ZMod p) :
    (cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p) + (cBits c0)[2] * (4 : ZMod p)
        + (cBits c0)[3] * (8 : ZMod p) + (cBits c0)[4] * (16 : ZMod p)
        + (cBits c0)[5] * (32 : ZMod p)
      = ((c0.val % 64 : ℕ) : ZMod p) := by
  simp only [cBits, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.shiftRight_eq_div_pow]
  have h : c0.val % 64
      = c0.val / 2 ^ 0 % 2 + (c0.val / 2 ^ 1 % 2) * 2 + (c0.val / 2 ^ 2 % 2) * 4
        + (c0.val / 2 ^ 3 % 2) * 8 + (c0.val / 2 ^ 4 % 2) * 16 + (c0.val / 2 ^ 5 % 2) * 32 := by
    simp only [pow_zero, pow_one, Nat.div_one]
    omega
  rw [h]
  push_cast
  ring

/-- The shift-amount high-bits value: `(c0 - (c0.val mod 64)) · 64⁻¹ = c0.val / 64` (cast). -/
theorem e32_eq (c0 : ZMod p) :
    (c0 - ((c0.val % 64 : ℕ) : ZMod p)) * ((64 : ZMod p))⁻¹ = ((c0.val / 64 : ℕ) : ZMod p) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have h64ne : (64 : ZMod p) ≠ 0 := by simp [← ZMod.val_eq_zero, val_64_zmod_p]
  obtain ⟨q, r, hqr, hrlt⟩ : ∃ q r, c0.val = 64 * q + r ∧ r < 64 :=
    ⟨c0.val / 64, c0.val % 64, (Nat.div_add_mod _ _).symm, Nat.mod_lt _ (by norm_num)⟩
  have hq : c0.val / 64 = q := by omega
  have hr : c0.val % 64 = r := by omega
  rw [hq, hr, show c0 = ((64 * q + r : ℕ) : ZMod p) by rw [← hqr, ZMod.natCast_zmod_val]]
  push_cast
  rw [add_sub_cancel_right, mul_comm ((64 : ZMod p)) ((q : ZMod p)), mul_assoc,
    mul_inv_cancel₀ h64ne, mul_one]

/-- `c0.val / 64` is a 10-bit value (cast `.val` form), for the high-bits byte-range pull. -/
theorem e32_val_lt (c0 : ZMod p) (hc : c0.val < 2 ^ 16) :
    (((c0.val / 64 : ℕ) : ZMod p)).val < 2 ^ 10 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  rw [ZMod.val_natCast_of_lt (by omega)]
  omega

/-- Each `lower_limb` entry's `.val` is below `2^(16 - bitShift)`. -/
theorem lowerLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (i : ℕ) (hi : i < 4) :
    (lowerLimb b c0)[i].val < 2 ^ (16 - bitShiftNat c0) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hpos : 0 < 2 ^ (16 - bitShiftNat c0) := pow_pos (by norm_num) _
  have hle : 2 ^ (16 - bitShiftNat c0) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  interval_cases i <;>
    · simp only [lowerLimb, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hpos) (by omega))]
      exact Nat.mod_lt _ hpos

/-- Each `higher_limb` entry's `.val` is below `2^bitShift` (for u16 operand limbs). -/
theorem higherLimb_val_lt (b : Word (ZMod p)) (c0 : ZMod p) (hb : Word.isU64 b)
    (i : ℕ) (hi : i < 4) : (higherLimb b c0)[i].val < 2 ^ bitShiftNat c0 := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hbs : bitShiftNat c0 ≤ 16 := by unfold bitShiftNat; omega
  have hsmall : ∀ x : ℕ, x < 2 ^ 16 → x / 2 ^ (16 - bitShiftNat c0) < p := by
    intro x hx
    have h1 := div_pow_lt hbs hx
    have h2 : 2 ^ bitShiftNat c0 ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) hbs
    omega
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  interval_cases i <;>
    simp only [higherLimb, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb0)]; exact div_pow_lt hbs hb0
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb1)]; exact div_pow_lt hbs hb1
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb2)]; exact div_pow_lt hbs hb2
  · rw [ZMod.val_natCast_of_lt (hsmall _ hb3)]; exact div_pow_lt hbs hb3

/-- Provide a `Range` byte-table row (the producer direction of `byteRowSpec_range`, for
variable widths). -/
theorem byteRowSpec_range_intro {x w : ZMod p} (h : x.val < 2 ^ w.val) :
    ByteRowSpec (⟨6, x, w, 0⟩ : ByteRow (ZMod p)) :=
  ⟨ByteOpcode.Range, by norm_cast, h⟩

/-- The shift-amount high-bits pull row (`e32 < 2^10`) is in the byte table (field-numeral
normal form; the completeness use-site `convert`s the circuit's ℕ-cast numerals onto it). -/
theorem byteRow_e32 (c0 : ZMod p) (hc : c0.val < 2 ^ 16) :
    ByteRowSpec (⟨6, (c0 + -((cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p)
      + (cBits c0)[2] * (4 : ZMod p) + (cBits c0)[3] * (8 : ZMod p)
      + (cBits c0)[4] * (16 : ZMod p) + (cBits c0)[5] * (32 : ZMod p))) * (64 : ZMod p)⁻¹,
      (10 : ZMod p), 0⟩ : ByteRow (ZMod p)) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  rw [cBits_shamt_sum, ← sub_eq_add_neg, e32_eq]
  refine byteRowSpec_range_intro ?_
  rw [show ((10 : ZMod p)) = ((10 : ℕ) : ZMod p) by push_cast; rfl,
    ZMod.val_natCast_of_lt (show (10 : ℕ) < p by omega)]
  exact e32_val_lt c0 hc

/-- The `lower_limb` byte-range pull rows (`< 2^(16 - bitShift)`) are in the table
(field-numeral normal form). -/
theorem byteRow_lower (b : Word (ZMod p)) (c0 : ZMod p) (i : ℕ) (hi : i < 4) :
    ByteRowSpec (⟨6, (lowerLimb b c0)[i],
      (16 : ZMod p) + -((cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p)
        + (cBits c0)[2] * (4 : ZMod p) + (cBits c0)[3] * (8 : ZMod p)),
      0⟩ : ByteRow (ZMod p)) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have hw : (16 : ZMod p) + -((cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p)
      + (cBits c0)[2] * (4 : ZMod p) + (cBits c0)[3] * (8 : ZMod p))
      = ((16 - c0.val % 16 : ℕ) : ZMod p) := by
    rw [cBits_bitShift_sum, ← sub_eq_add_neg,
      show ((16 : ZMod p)) = ((16 : ℕ) : ZMod p) by push_cast; rfl,
      ← Nat.cast_sub (by omega)]
  rw [hw]
  refine byteRowSpec_range_intro ?_
  rw [ZMod.val_natCast_of_lt (show 16 - c0.val % 16 < p by omega)]
  have h := lowerLimb_val_lt b c0 i hi
  unfold bitShiftNat at h
  exact h

/-- The `higher_limb` byte-range pull rows (`< 2^bitShift`) are in the table (field-numeral
normal form). -/
theorem byteRow_higher (b : Word (ZMod p)) (c0 : ZMod p) (hb : Word.isU64 b)
    (i : ℕ) (hi : i < 4) :
    ByteRowSpec (⟨6, (higherLimb b c0)[i],
      (cBits c0)[0] * (1 : ZMod p) + (cBits c0)[1] * (2 : ZMod p) + (cBits c0)[2] * (4 : ZMod p)
        + (cBits c0)[3] * (8 : ZMod p),
      0⟩ : ByteRow (ZMod p)) := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  rw [cBits_bitShift_sum]
  refine byteRowSpec_range_intro ?_
  rw [ZMod.val_natCast_of_lt (show c0.val % 16 < p by omega)]
  have h := higherLimb_val_lt b c0 hb i hi
  unfold bitShiftNat at h
  exact h

end ValueLemmas

end SP1Clean.ShiftLeftChip
