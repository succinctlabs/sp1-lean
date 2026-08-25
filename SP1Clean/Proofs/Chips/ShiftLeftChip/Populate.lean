import SP1Clean.Math.Word
import ToMathlib.General
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

/-! ## Witness IR

The exportable twins of the nine witness payloads (`docs/agents/porting-recipe.md` § the
witness-IR port). The variable-exponent arithmetic stays in the u64 sort: `2^(c&m)` is
`1 <<< (c.val % (m+1))`, and the split modulus `2^(16 − bitShift)` is `65536 >>> bitShift`
(`Nat.two_pow_shiftRight` closes the ℕ side). The variant dispatch mirrors `populateA`'s
flag/byte-shift branching — the SLL placement is one `.listGet` per cell over the byte-shift
index (in range: `byteShiftNat_lt`). Deliberately **not** `@[circuit_norm]`; only the eval/congr
lemmas cross the boundary. -/

section WitnessIR

/-- The two hint-flag reads (`is_sll`, `is_sllw`), as exportable IR leaves. -/
def hintF (k : Fin 2) : Witgen.FExpr (ZMod p) := .hintGet "shift_left_flags" 2 0 k

/-- The six shift-amount bits, as IR. -/
def cBitsIR (c0e : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 6 :=
  .ofFExprs #v[((c0e.val >>> 0) % 2).toField, ((c0e.val >>> 1) % 2).toField,
               ((c0e.val >>> 2) % 2).toField, ((c0e.val >>> 3) % 2).toField,
               ((c0e.val >>> 4) % 2).toField, ((c0e.val >>> 5) % 2).toField]

/-- The three power encodings (`2^(c&3), 2^(c&7), 2^(c&15)`), as IR. -/
def vPowersIR (c0e : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 3 :=
  .ofFExprs #v[((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 4)).toField,
               ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 8)).toField,
               ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16)).toField]

/-- The byte-level shift amount, u64-sorted (bit 5 gated by the `is_sll` hint flag). -/
def byteShiftU (c0e : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (c0e.val >>> 4) % 2
    + 2 * ((c0e.val >>> 5) % 2) * (.ite ((hintF 0 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p)) 1 0)

/-- The flag-gated one-hot byte-shift selector, as IR. -/
def shiftU16IR (c0e : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[.ite (byteShiftU c0e =? (0 : ℕ)) (hintF 0 + hintF 1) 0,
               .ite (byteShiftU c0e =? (1 : ℕ)) (hintF 0 + hintF 1) 0,
               .ite (byteShiftU c0e =? (2 : ℕ)) (hintF 0 + hintF 1) 0,
               .ite (byteShiftU c0e =? (3 : ℕ)) (hintF 0 + hintF 1) 0]

/-- The bit-split modulus `2^(16 − bitShift)`, u64-sorted (`65536 >>> (c & 0xF)`). -/
def lowModU (c0e : Expression (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (65536 : Witgen.U64Expr (ZMod p)) >>> (c0e.val % 16)

/-- The per-limb low bit-split, as IR. -/
def lowerLimbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[(b[0].val % lowModU c0e).toField, (b[1].val % lowModU c0e).toField,
               (b[2].val % lowModU c0e).toField, (b[3].val % lowModU c0e).toField]

/-- The per-limb high bit-split, as IR. -/
def higherLimbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[(b[0].val / lowModU c0e).toField, (b[1].val / lowModU c0e).toField,
               (b[2].val / lowModU c0e).toField, (b[3].val / lowModU c0e).toField]

/-- The `limb_result` cell `i` as a bare `FExpr` (shared by `limbResultIR` and the `a` placement). -/
def lrF (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) (i : ℕ) :
    Witgen.FExpr (ZMod p) :=
  [((b[0].val % lowModU c0e) * ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16))).toField,
   ((b[1].val % lowModU c0e) * ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16))
     + b[0].val / lowModU c0e).toField,
   ((b[2].val % lowModU c0e) * ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16))
     + b[1].val / lowModU c0e).toField,
   ((b[3].val % lowModU c0e) * ((1 : Witgen.U64Expr (ZMod p)) <<< (c0e.val % 16))
     + b[2].val / lowModU c0e).toField].getD i 0

/-- The `limb_result` reassembly, as IR. -/
def limbResultIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[lrF b c0e 0, lrF b c0e 1, lrF b c0e 2, lrF b c0e 3]

/-- The placed `a[1]` limb of the SLLW branch (`lo[1]`): `limb_result` cell `1` on byte-shift `0`,
cell `0` otherwise. -/
def loF1 (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) : Witgen.FExpr (ZMod p) :=
  .ite (byteShiftU c0e =? (0 : ℕ)) (lrF b c0e 1) (lrF b c0e 0)

/-- Result-word cell `j`, mirroring `populateA`'s variant dispatch: the SLL branch places
`limb_result` by the byte shift (a `.listGet`); the SLLW branch places the low two limbs and
sign-fills the upper two with `msb · 65535`. -/
def aF (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) : ℕ → Witgen.FExpr (ZMod p)
  | 0 => .ite ((hintF 0 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
      (.listGet [lrF b c0e 0, 0, 0, 0] (byteShiftU c0e))
      (.ite ((hintF 1 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p)) (.ite (byteShiftU c0e =? (0 : ℕ)) (lrF b c0e 0) 0) 0)
  | 1 => .ite ((hintF 0 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
      (.listGet [lrF b c0e 1, lrF b c0e 0, 0, 0] (byteShiftU c0e))
      (.ite ((hintF 1 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p)) (loF1 b c0e) 0)
  | 2 => .ite ((hintF 0 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
      (.listGet [lrF b c0e 2, lrF b c0e 1, lrF b c0e 0, 0] (byteShiftU c0e))
      (.ite ((hintF 1 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
        (U16MSBOperation.populate_msbF (loF1 b c0e) * (65535 : ZMod p)) 0)
  | 3 => .ite ((hintF 0 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
      (.listGet [lrF b c0e 3, lrF b c0e 2, lrF b c0e 1, lrF b c0e 0] (byteShiftU c0e))
      (.ite ((hintF 1 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
        (U16MSBOperation.populate_msbF (loF1 b c0e) * (65535 : ZMod p)) 0)
  | _ => 0

/-- The result word `a`, as IR. -/
def populateAIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 4 :=
  .ofFExprs #v[aF b c0e 0, aF b c0e 1, aF b c0e 2, aF b c0e 3]

/-- The SLLW sign bit, as IR. -/
def sllwMsbIR (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p)) :
    Witgen.WitgenIR (ZMod p) 1 :=
  .ofFExprs #v[.ite ((hintF 1 : Witgen.FExpr (ZMod p)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (aF b c0e 1)) 0]

/-- The three committed flag cells (`is_sll`, `is_sllw`, `is_sllw · imm_c`), as IR. -/
def flagsIR (imm_c : Expression (ZMod p)) : Witgen.WitgenIR (ZMod p) 3 :=
  .ofFExprs #v[hintF 0, hintF 1, hintF 1 * .expr imm_c]

/-! ### Eval lemmas (the boundary: IR evaluation = the value-level witness functions) -/

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating a hint-flag leaf is the `hintFlags` accessor cell. -/
theorem hintF_eval (env : ProverEnvironment (ZMod p)) (k : Fin 2) :
    Witgen.FExpr.eval { env := env } (hintF k) = (hintFlags env.hint)[k] := by
  have hdefault : (default : Vector (ZMod p) 2) = #v[0, 0] := rfl
  rw [hintFlags, ← hdefault]
  fin_cases k <;> simp only [hintF, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the shift-amount bits is `cBits` (the limb bound keeps the u64 sort from
wrapping). -/
theorem cBitsIR_eval (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p)) (c0 : ZMod p)
    (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    (cBitsIR c0e).eval env = cBits c0 := by
  apply Vector.ext
  intro i hi
  simp only [cBitsIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [cBits, circuit_norm, hc0]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the power encodings is `vPowers` (`1 <<< k = 2^k`, in range for `k < 16`). -/
theorem vPowersIR_eval (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p)) (c0 : ZMod p)
    (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    (vPowersIR c0e).eval env = vPowers c0 := by
  have h4 : 2 ^ (c0.val % 4) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h8 : 2 ^ (c0.val % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : 2 ^ (c0.val % 16) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
  apply Vector.ext
  intro i hi
  simp only [vPowersIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    (simp only [vPowers, circuit_norm, hc0]
     rw [Nat.shiftLeft_eq, one_mul])

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the u64 byte-shift amount is `byteShiftNat` (of the evaluated limb and the hint
flags). -/
theorem byteShiftU_toNat (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p)) (c0 : ZMod p)
    (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    ((byteShiftU c0e).eval { env := env }).toNat = byteShiftNat c0 (hintFlags env.hint) := by
  simp only [byteShiftU, byteShiftNat, circuit_norm, hc0, hintF_eval, apply_ite UInt64.toNat]
  split_ifs <;> omega

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the byte-shift selector is `shiftU16`. -/
theorem shiftU16IR_eval (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p)) (c0 : ZMod p)
    (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    (shiftU16IR c0e).eval env = shiftU16 c0 (hintFlags env.hint) := by
  have hbs := byteShiftU_toNat env c0e c0 hc0 hb
  apply Vector.ext
  intro i hi
  simp only [shiftU16IR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [shiftU16, circuit_norm, hintF_eval, hbs]

omit [Fact (2 ^ 17 < p)] in
/-- The u64 split modulus evaluates to `2^(16 − bitShift)` (`Nat.two_pow_shiftRight`). -/
theorem lowModU_toNat (env : ProverEnvironment (ZMod p)) (c0e : Expression (ZMod p)) (c0 : ZMod p)
    (hc0 : Expression.eval env.toEnvironment c0e = c0) (hb : c0.val < 2 ^ 16) :
    ((lowModU c0e).eval { env := env }).toNat = 2 ^ (16 - c0.val % 16) := by
  simp only [lowModU, circuit_norm, hc0]
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Nat.two_pow_shiftRight (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the low bit-split is `lowerLimb`. -/
theorem lowerLimbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (lowerLimbIR b c0e).eval env = lowerLimb vb c0 := by
  have hmod := lowModU_toNat env c0e c0 hc0 hb
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  apply Vector.ext
  intro i hi
  simp only [lowerLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [lowerLimb, bitShiftNat, circuit_norm, h0, h1, h2, h3, hmod]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the high bit-split is `higherLimb`. -/
theorem higherLimbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (higherLimbIR b c0e).eval env = higherLimb vb c0 := by
  have hmod := lowModU_toNat env c0e c0 hc0 hb
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  apply Vector.ext
  intro i hi
  simp only [higherLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [higherLimb, bitShiftNat, circuit_norm, h0, h1, h2, h3, hmod]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating a `limb_result` cell is `limbResult`'s cell (the split product stays below `2^16`:
`(x % 2^(16−s)) · 2^s < 2^16`). -/
theorem lrF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) (i : ℕ) (hi : i < 4) :
    Witgen.FExpr.eval { env := env } (lrF b c0e i) = (limbResult vb c0)[i] := by
  have hmod := lowModU_toNat env c0e c0 hc0 hb
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hbU
  have hs16 : c0.val % 16 ≤ 16 := le_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
  have hpow : 2 ^ (16 - c0.val % 16) * 2 ^ (c0.val % 16) = 2 ^ 16 := by
    rw [← pow_add]
    congr 1
    omega
  have hApos : 0 < 2 ^ (16 - c0.val % 16) := Nat.pow_pos (by omega)
  have hBpos : 0 < 2 ^ (c0.val % 16) := Nat.pow_pos (by omega)
  have hprod : ∀ x : ℕ, x < 2 ^ 16 →
      (x % 2 ^ (16 - c0.val % 16)) * 2 ^ (c0.val % 16) < 2 ^ 16 := fun x hx =>
    lt_of_lt_of_le (mul_lt_mul_of_pos_right (Nat.mod_lt x hApos) hBpos) (le_of_eq hpow)
  have hp0 := hprod vb[0].val u0
  have hp1 := hprod vb[1].val u1
  have hp2 := hprod vb[2].val u2
  have hp3 := hprod vb[3].val u3
  have hd0 : vb[0].val / 2 ^ (16 - c0.val % 16) ≤ vb[0].val := Nat.div_le_self _ _
  have hd1 : vb[1].val / 2 ^ (16 - c0.val % 16) ≤ vb[1].val := Nat.div_le_self _ _
  have hd2 : vb[2].val / 2 ^ (16 - c0.val % 16) ≤ vb[2].val := Nat.div_le_self _ _
  have hd3 : vb[3].val / 2 ^ (16 - c0.val % 16) ≤ vb[3].val := Nat.div_le_self _ _
  have hsl : (1 : ℕ) <<< (c0.val % 16) = 2 ^ (c0.val % 16) := by
    rw [Nat.shiftLeft_eq, one_mul]
  have hs64 : 2 ^ (c0.val % 16) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) (by norm_num)
  interval_cases i
  · simp only [lrF, limbResult, limbResultNat, bitShiftNat, List.getD, List.getElem?_cons_zero,
      Option.getD_some, circuit_norm, h0, hmod]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      Nat.mod_eq_of_lt (lt_trans hp0 (by norm_num))]
  · simp only [lrF, limbResult, limbResultNat, bitShiftNat, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, circuit_norm, h0, h1, hmod]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      Nat.mod_eq_of_lt (lt_trans hp1 (by norm_num)), Nat.mod_eq_of_lt (by omega)]
  · simp only [lrF, limbResult, limbResultNat, bitShiftNat, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, circuit_norm, h1, h2, hmod]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      Nat.mod_eq_of_lt (lt_trans hp2 (by norm_num)), Nat.mod_eq_of_lt (by omega)]
  · simp only [lrF, limbResult, limbResultNat, bitShiftNat, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, circuit_norm, h2, h3, hmod]
    rw [hc0, Nat.mod_eq_of_lt (show c0.val < 2 ^ 64 by omega), hsl, Nat.mod_eq_of_lt hs64,
      Nat.mod_eq_of_lt (lt_trans hp3 (by norm_num)), Nat.mod_eq_of_lt (by omega)]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the `limb_result` reassembly is `limbResult`. -/
theorem limbResultIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (limbResultIR b c0e).eval env = limbResult vb c0 := by
  apply Vector.ext
  intro i hi
  simp only [limbResultIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simpa using lrF_eval env b c0e vb c0 hW hc0 hbU hb _ (by omega)

/-- Evaluating a result-word cell is `populateA`'s cell (the variant dispatch resolves branch by
branch; the SLL placement's `.listGet` lands in range by `byteShiftNat_lt`). -/
theorem aF_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) (j : ℕ) (hj : j < 4) :
    Witgen.FExpr.eval { env := env } (aF b c0e j)
      = (populateA vb c0 (hintFlags env.hint))[j] := by
  have hp17 : (2 : ℕ) ^ 17 < p := Fact.out
  have hbs := byteShiftU_toNat env c0e c0 hc0 hb
  have hlr := lrF_eval env b c0e vb c0 hW hc0 hbU hb
  have hlrv : ∀ (i : ℕ) (hi : i < 4), ((limbResult vb c0)[i]).val < 2 ^ 16 := fun i hi => by
    simp only [limbResult, Vector.getElem_map]
    rw [ZMod.val_natCast_of_lt (lt_trans (limbResultNat_lt vb c0 hbU i hi) (by omega))]
    exact limbResultNat_lt vb c0 hbU i hi
  have hk4 : byteShiftNat c0 (hintFlags env.hint) < 4 := byteShiftNat_lt c0 _
  set k := byteShiftNat c0 (hintFlags env.hint) with hkeq
  clear_value k
  have hlo1 : Witgen.FExpr.eval { env := env } (loF1 b c0e)
      = if k = 0 then (limbResult vb c0)[1] else (limbResult vb c0)[0] := by
    simp only [loF1, circuit_norm, hbs, hlr 0 (by omega), hlr 1 (by omega)]
  have hlo1v : (if k = 0 then (limbResult vb c0)[1] else (limbResult vb c0)[0]).val < 2 ^ 16 := by
    split_ifs
    · exact hlrv 1 (by omega)
    · exact hlrv 0 (by omega)
  have hmsb : Witgen.FExpr.eval { env := env } (U16MSBOperation.populate_msbF (loF1 b c0e))
      = U16MSBOperation.populate_msb
          (if k = 0 then (limbResult vb c0)[1] else (limbResult vb c0)[0]) := by
    rw [U16MSBOperation.populate_msbF_eval _ _ (by rw [hlo1]; exact hlo1v), hlo1]
  interval_cases j <;> by_cases hf0 : (hintFlags env.hint)[0] = 1
  · interval_cases k <;>
      simp only [aF, populateA, circuit_norm, hintF_eval, hf0, if_true, hbs,
        Witgen.FExpr.evalList, hlr 0 (by omega)] <;>
      norm_num [← hkeq]
  · by_cases hf1 : (hintFlags env.hint)[1] = 1
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_true, if_false, hbs]
      split_ifs <;> first | omega | norm_num [hlr 0 (by omega), hlr 1 (by omega)]
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_false]
  · interval_cases k <;>
      simp only [aF, populateA, circuit_norm, hintF_eval, hf0, if_true, hbs,
        Witgen.FExpr.evalList, hlr 0 (by omega), hlr 1 (by omega)] <;>
      norm_num [← hkeq]
  · by_cases hf1 : (hintFlags env.hint)[1] = 1
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_true, if_false, hbs]
      rw [hlo1]
      split_ifs <;> first | omega | norm_num [hlr 0 (by omega), hlr 1 (by omega)]
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_false]
  · interval_cases k <;>
      simp only [aF, populateA, circuit_norm, hintF_eval, hf0, if_true, hbs,
        Witgen.FExpr.evalList, hlr 0 (by omega), hlr 1 (by omega), hlr 2 (by omega)] <;>
      norm_num [← hkeq]
  · by_cases hf1 : (hintFlags env.hint)[1] = 1
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_true, if_false, hmsb]
      split_ifs <;> first | omega | norm_num
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_false]
  · interval_cases k <;>
      simp only [aF, populateA, circuit_norm, hintF_eval, hf0, if_true, hbs,
        Witgen.FExpr.evalList, hlr 0 (by omega), hlr 1 (by omega), hlr 2 (by omega),
        hlr 3 (by omega)] <;>
      norm_num [← hkeq]
  · by_cases hf1 : (hintFlags env.hint)[1] = 1
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_true, if_false, hmsb]
      split_ifs <;> first | omega | norm_num
    · simp only [aF, populateA, circuit_norm, hintF_eval, hf0, hf1, if_false]

/-- Evaluating the result word is `populateA`. -/
theorem populateAIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (populateAIR b c0e).eval env = populateA vb c0 (hintFlags env.hint) := by
  apply Vector.ext
  intro i hi
  simp only [populateAIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simpa using aF_eval env b c0e vb c0 hW hc0 hbU hb _ (by omega)

/-- Evaluating the SLLW sign bit is `sllwMsb`. -/
theorem sllwMsbIR_eval (env : ProverEnvironment (ZMod p))
    (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (vb : Word (ZMod p)) (c0 : ZMod p)
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vb[i])
    (hc0 : Expression.eval env.toEnvironment c0e = c0)
    (hbU : vb.isU64) (hb : c0.val < 2 ^ 16) :
    (sllwMsbIR b c0e).eval env = #v[sllwMsb vb c0 (hintFlags env.hint)] := by
  have ha1 := aF_eval env b c0e vb c0 hW hc0 hbU hb 1 (by omega)
  have ha1v := populateA_val_lt vb c0 (hintFlags env.hint) hbU 1 (by omega)
  have hmsbA : Witgen.FExpr.eval { env := env }
      (U16MSBOperation.populate_msbF (aF b c0e 1))
      = U16MSBOperation.populate_msb (populateA vb c0 (hintFlags env.hint))[1] := by
    rw [U16MSBOperation.populate_msbF_eval _ _ (by rw [ha1]; exact ha1v), ha1]
  apply Vector.ext
  intro i hi
  simp only [sllwMsbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  simp only [sllwMsb, circuit_norm, hintF_eval, hmsbA]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the committed flag cells is the flag/`is_sllw_imm` triple. -/
theorem flagsIR_eval (env : ProverEnvironment (ZMod p)) (imm_c : Expression (ZMod p)) :
    (flagsIR imm_c).eval env
      = #v[(hintFlags env.hint)[0], (hintFlags env.hint)[1],
           (hintFlags env.hint)[1] * Expression.eval env.toEnvironment imm_c] := by
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

/-- Congruence for the shift-amount bits. -/
theorem cBitsIR_congr (c0e : Expression (ZMod p))
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (cBitsIR c0e).eval env = (cBitsIR c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [cBitsIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [circuit_norm, -Witgen.u64Wrap, hc]

/-- Congruence for the power encodings. -/
theorem vPowersIR_congr (c0e : Expression (ZMod p))
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (vPowersIR c0e).eval env = (vPowersIR c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [vPowersIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;> simp only [circuit_norm, -Witgen.u64Wrap, hc]

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

/-- Congruence for the low bit-split. -/
theorem lowerLimbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (lowerLimbIR b c0e).eval env = (lowerLimbIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [lowerLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [lowModU, circuit_norm, -Witgen.u64Wrap, hB 0 (by omega), hB 1 (by omega),
      hB 2 (by omega), hB 3 (by omega), hc]

/-- Congruence for the high bit-split. -/
theorem higherLimbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (higherLimbIR b c0e).eval env = (higherLimbIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [higherLimbIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
    simp only [lowModU, circuit_norm, -Witgen.u64Wrap, hB 0 (by omega), hB 1 (by omega),
      hB 2 (by omega), hB 3 (by omega), hc]

/-- Congruence for a `limb_result` cell. -/
theorem lrF_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (i : ℕ) :
    Witgen.FExpr.eval { env := env } (lrF b c0e i)
      = Witgen.FExpr.eval { env := env' } (lrF b c0e i) := by
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · interval_cases i <;>
      simp only [lrF, lowModU, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, circuit_norm, -Witgen.u64Wrap, hB 0 (by omega), hB 1 (by omega),
        hB 2 (by omega), hB 3 (by omega), hc]
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
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e) :
    (limbResultIR b c0e).eval env = (limbResultIR b c0e).eval env' := by
  apply Vector.ext
  intro i hi
  simp only [limbResultIR]
  rw [Witgen.WitgenIR.getElem_eval_ofFExprs, Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i
  · exact lrF_congr env env' b c0e hB hc 0
  · exact lrF_congr env env' b c0e hB hc 1
  · exact lrF_congr env env' b c0e hB hc 2
  · exact lrF_congr env env' b c0e hB hc 3

/-- Congruence for a result-word cell. -/
theorem aF_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) (j : ℕ) :
    Witgen.FExpr.eval { env := env } (aF b c0e j)
      = Witgen.FExpr.eval { env := env' } (aF b c0e j) := by
  have hlr0 := lrF_congr env env' b c0e hB hc 0
  have hlr1 := lrF_congr env env' b c0e hB hc 1
  have hlr2 := lrF_congr env env' b c0e hB hc 2
  have hlr3 := lrF_congr env env' b c0e hB hc 3
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
  have hloC : Witgen.FExpr.eval { env := env } (loF1 b c0e)
      = Witgen.FExpr.eval { env := env' } (loF1 b c0e) := by
    simp only [loF1, byteShiftU, hintF, circuit_norm, -Witgen.u64Wrap, hc, hh, hlr0, hlr1]
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (loF1 b c0e) hloC
  rcases Nat.lt_or_ge j 4 with hlt | hge
  · interval_cases j <;>
      (simp only [aF, byteShiftU, hintF, circuit_norm, -Witgen.u64Wrap, hc, hh, hmsbC, hloC,
        hlr0]
       rw [hEL _ _ (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          first | rfl | exact hlr0 | exact hlr1 | exact hlr2 | exact hlr3)])
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

/-- Congruence for the SLLW sign bit. -/
theorem sllwMsbIR_congr (b : Word (Expression (ZMod p))) (c0e : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hc : Expression.eval env.toEnvironment c0e = Expression.eval env'.toEnvironment c0e)
    (hh : env.hint = env'.hint) :
    (sllwMsbIR b c0e).eval env = (sllwMsbIR b c0e).eval env' := by
  have ha1 := aF_congr env env' b c0e hB hc hh 1
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' }
    (aF b c0e 1) ha1
  apply Vector.ext
  intro i hi
  simp only [sllwMsbIR]
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

end SP1Clean.ShiftLeftChip
