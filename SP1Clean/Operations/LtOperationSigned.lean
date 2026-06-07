import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Channels
import SP1Clean.Operations.LtOperationUnsigned.Formal
import SP1Clean.Operations.LtOperationUnsigned.Populate
import SP1Clean.Operations.U16MSBOperation.Formal
import SP1Clean.Extracted.LtOperationSigned
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `LtOperationSigned` as a Clean-native witnessed `FormalCircuit`

Signed/unsigned word less-than. A selector `is_signed` chooses the mode: when set, the top limbs are
sign-adjusted by flipping the high bit (`b[3] + is_signed·2^15 - 2^16·b_msb`, via two
`U16MSBOperation`s that witness the sign bits `b_msb`, `c_msb`), and the adjusted words are fed to
`LtOperationUnsigned`. When `is_signed = 0` the adjustment is the identity and the sign-bit ranges
are not enforced.

`RawSpec` transcribes the literal meaning at `is_real = 1` with **`is_signed` free**; `ltSigned_of_raw`
derives the semantic `Spec` from it. The keystone is the **sign-bias** identity (`adj_bias`): biasing the
top limb by `2^15` is `+2^63 mod 2^64`, so an unsigned `<` of the biased words is the signed `<` (`toInt`)
of the originals (`toInt_compare_of_bias`). Soundness/completeness of the witnessed `FormalCircuit` are
**fully proven and axiom-clean**; `Faithful/LtOperationSigned.lean` anchors `RawSpec`. -/

namespace SP1Clean.LtOperationSigned

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-! ## Sign-bias arithmetic (the signed-compare keystone)

The signed compare is realised by flipping bit 15 of the top limb (bit 63 of the word): the adjusted
limb `e13 = x + 32768 - 65536·msb` (with `msb` the high bit of `x`) biases the value by `2^63 mod 2^64`,
so an **unsigned** compare of the adjusted words is the **signed** compare of the originals. -/

/-- The biased top limb `x + 32768 - 65536·msb` (with `msb = [x ≥ 2^15]`) is itself a 16-bit value,
and its `ℕ`-value lifts to the integer bias `x.val + 2^15 - 2^16·msb`. -/
private lemma adj_limb {x : ZMod p} (hx : x.val < 2 ^ 16) :
    ((x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val : ℤ)
        = (x.val : ℤ) + 32768 - 65536 * (if 32768 ≤ x.val then 1 else 0)
      ∧ (x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val < 2 ^ 16 := by
  have hp : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  by_cases hsign : 32768 ≤ x.val
  · simp only [if_pos hsign, mul_one]
    have hval : (x + 32768 - 65536 : ZMod p).val = x.val - 32768 := by
      have e : ((x.val - 32768 : ℕ) : ZMod p) = x + 32768 - 65536 := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; push_cast; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val - 32768 < p by omega)
    rw [hval]; refine ⟨by omega, by omega⟩
  · simp only [if_neg hsign, mul_zero, sub_zero]
    have hval : (x + 32768 : ZMod p).val = x.val + 32768 := by
      have e : ((x.val + 32768 : ℕ) : ZMod p) = x + 32768 := by
        push_cast [ZMod.natCast_zmod_val]; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val + 32768 < p by omega)
    rw [hval]; refine ⟨by push_cast; omega, by omega⟩

/-- **Sign-bias keystone.** For a 64-bit word `b`, the `toNat` of the word with its top limb biased
(bit 15 flipped: `e13 = b[3] + 2^15 - 2^16·[b[3] ≥ 2^15]`) equals `(toBitVec64 b).toInt + 2^63`. Hence
an unsigned `<` of two biased words is a signed `<` of the originals. -/
private lemma adj_bias {b : Word (ZMod p)} (hb : b.isU64) :
    ((Word.toNat (#v[b[0], b[1], b[2],
        b[3] + 32768 - 65536 * (if 32768 ≤ b[3].val then (1 : ZMod p) else 0)] : Word (ZMod p))) : ℤ)
      = (Word.toBitVec64 b).toInt + 2 ^ 63 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hval, _⟩ := adj_limb h3
  rw [Word.toNat_def, BitVec.toInt_eq_toNat_cond, Word.toBitVec64_toNat hb, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hval ⊢
  by_cases hsign : 32768 ≤ b[3].val
  · rw [if_neg (by omega : ¬ 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_pos hsign] at hval ⊢; push_cast at hval ⊢; omega
  · rw [if_pos (by omega : 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_neg hsign] at hval ⊢; push_cast at hval ⊢; omega

/-- Transfer: with the two top limbs biased by their sign bits, the **unsigned** `<` of the biased
words is the **signed** `<` (`toInt`) of the originals. -/
private lemma toInt_compare_of_bias {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64)
    {bm cm : ZMod p}
    (hbm : bm = if 32768 ≤ b[3].val then 1 else 0)
    (hcm : cm = if 32768 ≤ cc[3].val then 1 else 0) :
    (Word.toNat (#v[b[0], b[1], b[2], b[3] + 32768 - 65536 * bm] : Word (ZMod p))
        < Word.toNat (#v[cc[0], cc[1], cc[2], cc[3] + 32768 - 65536 * cm] : Word (ZMod p)))
      ↔ (Word.toBitVec64 b).toInt < (Word.toBitVec64 cc).toInt := by
  subst hbm hcm
  have hb' := adj_bias hb
  have hcc' := adj_bias hcc
  omega

omit [Fact (2 ^ 17 < p)] in
/-- For 64-bit words, `toBitVec64` equality is `toNat` equality (it round-trips through `toNat`). Used
to carry the unsigned core's `toNat`-equality up to the signed `Spec`'s `toBitVec64` equality. -/
private lemma toBitVec64_eq_iff {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64) :
    (Word.toBitVec64 b = Word.toBitVec64 cc) ↔ (Word.toNat b = Word.toNat cc) := by
  constructor
  · intro h; rw [← Word.toBitVec64_toNat hb, ← Word.toBitVec64_toNat hcc, h]
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [Word.toBitVec64_toNat hb, Word.toBitVec64_toNat hcc, h]

/-- Literal meaning of SP1's `LtOperationSigned` constraint list at `is_real = 1`, with `is_signed`
free: the two `is_signed`-gated MSB sub-lists and the composed unsigned compare on the adjusted
words. -/
def RawSpec (b cc : Word (ZMod p)) (cols : Extracted.LtOperationSigned (ZMod p))
    (is_signed : ZMod p) : Prop :=
  let bm := cols.b_msb.msb; let cm := cols.c_msb.msb
  let e13 := b[3] + is_signed * 32768 - 65536 * bm
  let e17 := cc[3] + is_signed * 32768 - 65536 * cm
  (is_signed = 0 ∨ is_signed = 1) ∧ (bm = 0 ∨ bm = 1) ∧
    (is_signed ≠ 0 → (2 * b[3] - bm * 65536).val < 2 ^ 16) ∧
  (is_signed = 0 ∨ is_signed = 1) ∧ (cm = 0 ∨ cm = 1) ∧
    (is_signed ≠ 0 → (2 * cc[3] - cm * 65536).val < 2 ^ 16) ∧
  LtOperationUnsigned.RawSpec #v[b[0], b[1], b[2], e13] #v[cc[0], cc[1], cc[2], e17] cols.result ∧
  (is_signed = 0 ∨ is_signed = 1) ∧
  ((is_signed - 1) * bm = 0) ∧ ((is_signed - 1) * cm = 0)

/-- The operands are genuine 64-bit values; the mode selector is boolean. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧ (input.is_signed = 0 ∨ input.is_signed = 1)

set_option maxHeartbeats 800000 in
theorem ltSigned_of_raw {input : Inputs (ZMod p)} {cols : Extracted.LtOperationSigned (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc)
    (h_raw : RawSpec input.b input.cc cols input.is_signed) : Spec input cols := by
  simp only [RawSpec] at h_raw
  obtain ⟨hs1, hbm_b, hrange_b, -, hcm_b, hrange_c, h_uns, -, h_pb, h_pc⟩ := h_raw
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have h01 : (0 : ZMod p) ≠ 1 := by
    intro h; haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    have := congrArg ZMod.val h; rw [ZMod.val_zero, ZMod.val_one] at this; exact absurd this (by norm_num)
  simp only [Spec]
  rcases hs1 with hs | hs
  · -- `is_signed = 0`: `bm = cm = 0`, the unsigned compare of the unbiased words.
    have hbm0 : cols.b_msb.msb = 0 := by have h := h_pb; rw [hs] at h; linear_combination -h
    have hcm0 : cols.c_msb.msb = 0 := by have h := h_pc; rw [hs] at h; linear_combination -h
    rw [hs, hbm0, hcm0] at h_uns
    simp only [zero_mul, mul_zero, sub_zero, add_zero] at h_uns
    have hbit := LtOperationUnsigned.ltUnsigned_semantic
      #v[input.b[0], input.b[1], input.b[2], input.b[3]]
      #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]]
      (Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hb3))
      (Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hc3)) h_uns
    refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · rw [hbit.1]
      simp only [hs, if_neg h01, Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
    · rw [toBitVec64_eq_iff hb hcc]
      have key := hbit.2
      simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at key ⊢
      exact key
    · -- the unsigned `RawSpec`'s flag-sum-binary conjunct (6th), on the unbiased words.
      exact h_uns.2.2.2.2.2.1
  · -- `is_signed = 1`: `bm`/`cm` are the sign bits, the unsigned compare of the bias-flipped words.
    have hbm : cols.b_msb.msb = if 32768 ≤ input.b[3].val then 1 else 0 :=
      U16MSBOperation.msb_of_raw hb3
        ⟨hbm_b, by
          have h := hrange_b (by rw [hs]; norm_num)
          simpa using h⟩
    have hcm : cols.c_msb.msb = if 32768 ≤ input.cc[3].val then 1 else 0 :=
      U16MSBOperation.msb_of_raw hc3
        ⟨hcm_b, by
          have h := hrange_c (by rw [hs]; norm_num)
          simpa using h⟩
    rw [hs] at h_uns
    simp only [one_mul] at h_uns
    have hbU : (input.b[3] + 32768 - 65536 * cols.b_msb.msb).val < 2 ^ 16 := by
      rw [hbm]; exact (adj_limb hb3).2
    have hcU : (input.cc[3] + 32768 - 65536 * cols.c_msb.msb).val < 2 ^ 16 := by
      rw [hcm]; exact (adj_limb hc3).2
    have hbit := LtOperationUnsigned.ltUnsigned_semantic
      #v[input.b[0], input.b[1], input.b[2], input.b[3] + 32768 - 65536 * cols.b_msb.msb]
      #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3] + 32768 - 65536 * cols.c_msb.msb]
      (Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbU))
      (Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hcU)) h_uns
    refine ⟨?_, fun h => absurd (h ▸ hs) h01, fun h => absurd (h ▸ hs) h01⟩
    rw [hbit.1]
    simp only [hs, ↓reduceIte, toInt_compare_of_bias hb hcc hbm hcm]

/-! ## The witnessed `FormalCircuit`

Composes the two `U16MSBOperation` sub-gadgets and the `LtOperationUnsigned` sub-gadget on the
sign-adjusted words. The sign-bit witnesses are **`is_signed`-gated** (`is_signed · populate_msb`), so
on `is_signed = 0` rows `b_msb = c_msb = 0` and the `(is_signed-1)·msb` gates are satisfiable. -/

/-- Witness the two MSB sub-gadgets on the high limbs; feed the sign-adjusted words to the unsigned
compare sub-gadget; assert the selector boolean and the two `(is_signed-1)·msb` constraints.
Returns `⟨result, b_msb, c_msb⟩`. -/
def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var Extracted.LtOperationSigned (ZMod p)) := do
  -- witness the two sign bits via `populate_msb`; compose the demoted `U16MSBOperation` as `assertion`s
  -- (gated by `is_signed` — the sign-bit ranges are only enforced in signed mode).
  let b_msb ← witnessVector 1 (fun env =>
    #v[env input.is_signed * U16MSBOperation.populate_msb (env input.b[3])])
  let c_msb ← witnessVector 1 (fun env =>
    #v[env input.is_signed * U16MSBOperation.populate_msb (env input.cc[3])])
  let bm : Expression (ZMod p) := b_msb[0]
  let cm : Expression (ZMod p) := c_msb[0]
  assertion U16MSBOperation.circuit ⟨input.b[3], ⟨bm⟩, input.is_signed⟩
  assertion U16MSBOperation.circuit ⟨input.cc[3], ⟨cm⟩, input.is_signed⟩
  let e13 := input.b[3] + input.is_signed * (32768 : ZMod p) - (65536 : ZMod p) * bm
  let e17 := input.cc[3] + input.is_signed * (32768 : ZMod p) - (65536 : ZMod p) * cm
  -- `LtOperationUnsigned` is now a `FormalAssertion`: witness its comparison columns here (the
  -- sign-adjusted words via `populate_unsigned`), then compose it as a Clean `assertion` (`is_real := 1`).
  let cl ← witnessVector 2 (fun env =>
    LtOperationUnsigned.comparisonLimbsWitness
      #v[env input.b[0], env input.b[1], env input.b[2],
         env input.b[3] + env input.is_signed * 32768 - 65536 * env b_msb[0]]
      #v[env input.cc[0], env input.cc[1], env input.cc[2],
         env input.cc[3] + env input.is_signed * 32768 - 65536 * env c_msb[0]])
  let f ← witnessVector 4 (fun env =>
    LtOperationUnsigned.flagsWitness
      #v[env input.b[0], env input.b[1], env input.b[2],
         env input.b[3] + env input.is_signed * 32768 - 65536 * env b_msb[0]]
      #v[env input.cc[0], env input.cc[1], env input.cc[2],
         env input.cc[3] + env input.is_signed * 32768 - 65536 * env c_msb[0]])
  let not_eq_inv ← witnessVector 1 (fun env =>
    LtOperationUnsigned.notEqInvWitness
      #v[env input.b[0], env input.b[1], env input.b[2],
         env input.b[3] + env input.is_signed * 32768 - 65536 * env b_msb[0]]
      #v[env input.cc[0], env input.cc[1], env input.cc[2],
         env input.cc[3] + env input.is_signed * 32768 - 65536 * env c_msb[0]])
  let bit ← witnessVector 1 (fun env => #v[U16CompareOperation.populate_bit (env cl[0]) (env cl[1])])
  assertion LtOperationUnsigned.circuit
    ⟨#v[input.b[0], input.b[1], input.b[2], e13], #v[input.cc[0], input.cc[1], input.cc[2], e17],
      ⟨⟨bit[0]⟩, f, not_eq_inv[0], cl⟩, 1⟩
  input.is_signed * (input.is_signed - 1) === 0
  (input.is_signed - 1) * bm === 0
  (input.is_signed - 1) * cm === 0
  return ⟨⟨⟨bit[0]⟩, f, not_eq_inv[0], cl⟩, ⟨bm⟩, ⟨cm⟩⟩

set_option maxHeartbeats 1000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Extracted.LtOperationSigned main where
  -- witnesses the two sign bits (1 each) + the `LtOperationUnsigned` block (8); the two
  -- `U16MSBOperation`s are now `FormalAssertion`s (`localLength 0`).
  localLength _ := 1 + 1 + (2 + 4 + 1 + 1)
  localLength_eq := by simp +arith [circuit_norm, main, LtOperationUnsigned.circuit, U16MSBOperation.circuit]
  subcircuitsConsistent := by simp only [circuit_norm, main]; try omega
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements := [byteChannel.toRawGated]
  channelsLawful := by simp [circuit_norm, main, LtOperationUnsigned.circuit, U16MSBOperation.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees :
      List (RawChannel (ZMod p))) = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements :
      List (RawChannel (ZMod p))) = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 1 + 1 + (2 + 4 + 1 + 1) := rfl

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem soundness : Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  set bm := env.get i₀ with hbmdef
  set cm := env.get (i₀ + 1) with hcmdef
  obtain ⟨hb, hcc, h_sbin⟩ := h_assumptions
  obtain ⟨hib, hicc, his⟩ := h_input
  obtain ⟨h_msb_b, h_msb_c, h_lt, h_gate, h_pb, h_pc⟩ := h_holds
  have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
  have ec0 : Expression.eval env input_var_cc[0] = input_cc[0] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec1 : Expression.eval env input_var_cc[1] = input_cc[1] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec2 : Expression.eval env input_var_cc[2] = input_cc[2] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec3 : Expression.eval env input_var_cc[3] = input_cc[3] := by rw [← hicc]; simp only [Vector.getElem_map]
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3] at h_msb_b h_msb_c h_lt ⊢
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have hAb : U16MSBOperation.circuit.Assumptions ⟨input_b[3], ⟨bm⟩, input_is_signed⟩ :=
    ⟨fun _ => hb3, h_sbin⟩
  have hAc : U16MSBOperation.circuit.Assumptions ⟨input_cc[3], ⟨cm⟩, input_is_signed⟩ :=
    ⟨fun _ => hc3, h_sbin⟩
  have Sb := h_msb_b hAb
  have Sc := h_msb_c hAc
  simp only [← hbmdef, ← hcmdef] at h_lt h_pb h_pc Sb Sc ⊢
  clear_value bm cm
  rcases h_sbin with hs | hs
  · -- `is_signed = 0`: the two `(is_signed-1)·msb` gates force `bm = cm = 0`, so the adjusted top limbs
    -- are the originals and the unsigned compare *is* the spec's unsigned branch.
    subst hs
    have hbm : bm = 0 := by linear_combination -h_pb
    have hcm : cm = 0 := by linear_combination -h_pc
    have hbU : (input_b[3] + 0 * 32768 + -(65536 * bm)).val < 2 ^ 16 := by
      rw [hbm]; simpa using hb3
    have hcU : (input_cc[3] + 0 * 32768 + -(65536 * cm)).val < 2 ^ 16 := by
      rw [hcm]; simpa using hc3
    have hbU64 : Word.isU64
        #v[input_b[0], input_b[1], input_b[2], input_b[3] + 0 * 32768 + -(65536 * bm)] :=
      Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbU)
    have hcU64 : Word.isU64
        #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + 0 * 32768 + -(65536 * cm)] :=
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hcU)
    have hbit := LtOperationUnsigned.result_semantic hbU64 hcU64 rfl
      (h_lt ⟨fun _ => ⟨hbU64, hcU64⟩, Or.inr rfl⟩)
    have h01 : (0 : ZMod p) ≠ 1 := by
      intro h
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      have := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_one] at this
      exact absurd this (by norm_num)
    have hadjb : (#v[input_b[0], input_b[1], input_b[2], input_b[3] + 0 * 32768 + -(65536 * bm)]
        : Word (ZMod p)) = input_b := by
      rw [hbm]; apply Vector.ext; intro i hi; interval_cases i <;>
        simp [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    have hadjc : (#v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + 0 * 32768 + -(65536 * cm)]
        : Word (ZMod p)) = input_cc := by
      rw [hcm]; apply Vector.ext; intro i hi; interval_cases i <;>
        simp [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    obtain ⟨hbit1, hbit2⟩ := hbit
    simp only [hadjb, hadjc] at hbit1
    simp only [hadjb, hadjc, Vector.getElem_map] at hbit2
    -- the unsigned `Spec`'s flag-sum-binary conjunct (5th), on the (here unbiased) adjusted words.
    have h_uns_spec := h_lt ⟨fun _ => ⟨hbU64, hcU64⟩, Or.inr rfl⟩
    refine ⟨⟨?_, fun _ => ?_, fun _ => ?_⟩, Or.inr hAb, Or.inr hAc, Or.inr ⟨fun _ => ⟨hbU64, hcU64⟩, Or.inr rfl⟩⟩
    · rw [hbit1]; simp only [if_neg h01]
    · rw [toBitVec64_eq_iff hb hcc]; exact hbit2
    · simpa only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        using h_uns_spec.2.2.2.2.1
  · -- `is_signed = 1`: the two `U16MSBOperation` specs pin `bm`/`cm` to the sign bits, so the unsigned
    -- compare of the bit-15-flipped words is the signed compare (`toInt`) of the originals.
    subst hs
    have hbm : bm = if 32768 ≤ input_b[3].val then 1 else 0 := Sb.2 rfl
    have hcm : cm = if 32768 ≤ input_cc[3].val then 1 else 0 := Sc.2 rfl
    have hbU : (input_b[3] + 1 * 32768 + -(65536 * bm)).val < 2 ^ 16 := by
      rw [hbm]; have := (adj_limb hb3).2; rw [sub_eq_add_neg] at this; simpa using this
    have hcU : (input_cc[3] + 1 * 32768 + -(65536 * cm)).val < 2 ^ 16 := by
      rw [hcm]; have := (adj_limb hc3).2; rw [sub_eq_add_neg] at this; simpa using this
    have hbU64 : Word.isU64
        #v[input_b[0], input_b[1], input_b[2], input_b[3] + 1 * 32768 + -(65536 * bm)] :=
      Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbU)
    have hcU64 : Word.isU64
        #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + 1 * 32768 + -(65536 * cm)] :=
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hcU)
    obtain ⟨hbit1, _hbit2⟩ := LtOperationUnsigned.result_semantic hbU64 hcU64 rfl
      (h_lt ⟨fun _ => ⟨hbU64, hcU64⟩, Or.inr rfl⟩)
    simp only [Vector.getElem_map] at hbit1
    refine ⟨⟨?_, fun h => absurd h one_ne_zero, fun h => absurd h one_ne_zero⟩, Or.inr hAb, Or.inr hAc,
      Or.inr ⟨fun _ => ⟨hbU64, hcU64⟩, Or.inr rfl⟩⟩
    rw [hbit1]
    simp only [one_mul, ↓reduceIte, ← sub_eq_add_neg, toInt_compare_of_bias hb hcc hbm hcm]

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (ZMod p) main Assumptions := by
  circuit_proof_start
  obtain ⟨hb, hcc, h_sbin⟩ := h_assumptions
  obtain ⟨hib, hicc, his⟩ := h_input
  obtain ⟨henvb, henvc, henvcl, henvf, henvni, henvbit⟩ := h_env
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb2 : Expression.eval env.toEnvironment input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb3 : Expression.eval env.toEnvironment input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
  have ec0 : Expression.eval env.toEnvironment input_var_cc[0] = input_cc[0] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec1 : Expression.eval env.toEnvironment input_var_cc[1] = input_cc[1] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec2 : Expression.eval env.toEnvironment input_var_cc[2] = input_cc[2] := by rw [← hicc]; simp only [Vector.getElem_map]
  have ec3 : Expression.eval env.toEnvironment input_var_cc[3] = input_cc[3] := by rw [← hicc]; simp only [Vector.getElem_map]
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3] at henvb henvc ⊢
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have hpmb : U16MSBOperation.populate_msb input_b[3] = if 32768 ≤ input_b[3].val then 1 else 0 :=
    (U16MSBOperation.spec_populate hb3 1).2 rfl
  have hpmc : U16MSBOperation.populate_msb input_cc[3] = if 32768 ≤ input_cc[3].val then 1 else 0 :=
    (U16MSBOperation.spec_populate hc3 1).2 rfl
  have hadjb : (input_b[3] + input_is_signed * 32768 + -(65536 * env.get i₀)).val < 2 ^ 16 := by
    rw [henvb, hpmb]
    rcases h_sbin with h | h <;> rw [h]
    · simp only [zero_mul, mul_zero, neg_zero, add_zero]; exact hb3
    · have := (adj_limb hb3).2; rw [sub_eq_add_neg] at this; simpa using this
  have hadjc : (input_cc[3] + input_is_signed * 32768 + -(65536 * env.get (i₀ + 1))).val < 2 ^ 16 := by
    rw [henvc, hpmc]
    rcases h_sbin with h | h <;> rw [h]
    · simp only [zero_mul, mul_zero, neg_zero, add_zero]; exact hc3
    · have := (adj_limb hc3).2; rw [sub_eq_add_neg] at this; simpa using this
  refine ⟨⟨⟨fun _ => hb3, h_sbin⟩,
      ⟨by simp only [henvb]; rcases h_sbin with h | h <;> rw [h]
          · left; ring
          · rw [one_mul, hpmb]; split <;> simp,
       fun h1 => by dsimp only at h1 ⊢; rw [henvb, h1, one_mul, hpmb]⟩⟩,
    ⟨⟨fun _ => hc3, h_sbin⟩,
      ⟨by simp only [henvc]; rcases h_sbin with h | h <;> rw [h]
          · left; ring
          · rw [one_mul, hpmc]; split <;> simp,
       fun h1 => by dsimp only at h1 ⊢; rw [henvc, h1, one_mul, hpmc]⟩⟩,
    ⟨⟨fun _ => ⟨Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
          (by simpa using hadjb),
        Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
          (by simpa using hadjc)⟩, Or.inr rfl⟩, ?_⟩,
    by rcases h_sbin with h | h <;> rw [h] <;> simp,
    by rw [henvb]; rcases h_sbin with h | h <;> rw [h] <;> simp,
    by rw [henvc]; rcases h_sbin with h | h <;> rw [h] <;> simp⟩
  -- The composed `LtOperationUnsigned` assertion's `Spec`: the witnessed comparison columns are
  -- `populate`'s output on the sign-adjusted words, so `spec_populate` discharges it.
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3, sub_eq_add_neg, circuit_norm] at henvcl henvf henvni henvbit
  have hclv : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 2 fun i => var { index := i₀ + 1 + 1 + i }))
      = LtOperationUnsigned.comparisonLimbsWitness
          #v[input_b[0], input_b[1], input_b[2], input_b[3] + input_is_signed * 32768 + -(65536 * env.get i₀)]
          #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + input_is_signed * 32768 + -(65536 * env.get (i₀ + 1))] := by
    apply Vector.ext; intro i hi; simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [henvcl ⟨i, hi⟩]
  have hfv : (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 4 fun i => var { index := i₀ + 1 + 1 + 2 + i }))
      = LtOperationUnsigned.flagsWitness
          #v[input_b[0], input_b[1], input_b[2], input_b[3] + input_is_signed * 32768 + -(65536 * env.get i₀)]
          #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + input_is_signed * 32768 + -(65536 * env.get (i₀ + 1))] := by
    apply Vector.ext; intro i hi; simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [henvf ⟨i, hi⟩]
  have hcolseq :
      (⟨⟨env.get (i₀ + 1 + 1 + 2 + 4 + 1)⟩,
        Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var { index := i₀ + 1 + 1 + 2 + i }),
        env.get (i₀ + 1 + 1 + 2 + 4),
        Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 2 fun i => var { index := i₀ + 1 + 1 + i })⟩
        : Extracted.LtOperationUnsigned (ZMod p))
      = LtOperationUnsigned.populate
          #v[input_b[0], input_b[1], input_b[2], input_b[3] + input_is_signed * 32768 + -(65536 * env.get i₀)]
          #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + input_is_signed * 32768 + -(65536 * env.get (i₀ + 1))] := by
    have hcl0 := henvcl ⟨0, by norm_num⟩
    have hcl1 := henvcl ⟨1, by norm_num⟩
    have hni0 := henvni ⟨0, by norm_num⟩
    simp only [add_zero] at hcl0 hcl1
    simp only [LtOperationUnsigned.populate, hclv, hfv, hni0, henvbit, hcl0, hcl1]
  rw [hcolseq]
  exact LtOperationUnsigned.spec_populate

/-- The witnessed `FormalCircuit` for signed/unsigned word less-than; output is SP1's
`LtOperationSigned` column struct. -/
def circuit : FormalCircuit (ZMod p) Inputs Extracted.LtOperationSigned :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 1 + 1 + (2 + 4 + 1 + 1) := rfl

end SP1Clean.LtOperationSigned
