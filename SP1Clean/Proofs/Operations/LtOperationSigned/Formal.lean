import SP1Clean.Native.Operations.LtOperationSigned.RawSpec
import SP1Clean.Native.Operations.LtOperationSigned.Populate
import SP1Clean.Extracted.Circuit.LtOperationSigned
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal

/-! # `LtOperationSigned` — the `FormalAssertion` (Spec / soundness / completeness / contract)

SP1's `LtOperationSigned::eval` as a Clean `FormalAssertion` that **composes** two `U16MSBOperation`
(`assertion`, gated by `is_signed`) on the high limbs and one `LtOperationUnsigned` (`assertion`, on
the sign-adjusted words, threaded `is_real`) — witnessing nothing (the column block is an input `cols`,
threaded in by the composing chip via `populate`). The semantic `Spec` is **structural** (equivalent
to the constraint list: the selector booleans, the two `(is_signed-1)·msb` and `(is_real-1)·is_signed`
gates, the `is_signed`-gated high-bit equations, and the composed `LtOperationUnsigned.Spec` on the
adjusted words). The semantic readout (`bit = signed/unsigned-less-than`) is exposed by
`result_semantic`, routing through `LtOperationUnsigned.result_semantic` and the sign-bias keystones in
`RawSpec.lean`.

`Spec`/`spec_populate` live here (not in `Specs.Operation`) to avoid an import cycle: the `Extracted`
`main` imports `U16MSBOperation.Formal`/`LtOperationUnsigned.Formal` for `.circuit`. -/

namespace SP1Clean.LtOperationSigned

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The operands are genuine 64-bit values (true on real and zero-padded rows, supplied by the
register reads); `is_real` and `is_signed` are binary. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_signed = 0 ∨ input.is_signed = 1)

/-- Structural contract, **equivalent to the constraint list** (so completeness `Assumptions ∧ Spec →
constraints` holds): `is_signed`/`is_real`/`b_msb`/`c_msb` are boolean; the `(is_real-1)·is_signed` and
two `(is_signed-1)·msb` gates vanish; the two sign bits are the high bits on a signed row; and the
composed `LtOperationUnsigned.Spec` holds on the sign-adjusted words. The semantic whole-word signed/
unsigned order is derived from this by `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let bm := input.cols.b_msb.msb
  let cm := input.cols.c_msb.msb
  let e13 := input.b[3] + input.is_signed * 32768 - 65536 * bm
  let e17 := input.cc[3] + input.is_signed * 32768 - 65536 * cm
  (input.is_signed = 0 ∨ input.is_signed = 1) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (bm = 0 ∨ bm = 1) ∧ (cm = 0 ∨ cm = 1) ∧
  ((input.is_real - 1) * input.is_signed = 0) ∧
  ((input.is_signed - 1) * bm = 0) ∧ ((input.is_signed - 1) * cm = 0) ∧
  (input.is_signed = 1 → bm = if input.b[3].val ≥ 32768 then 1 else 0) ∧
  (input.is_signed = 1 → cm = if input.cc[3].val ≥ 32768 then 1 else 0) ∧
  LtOperationUnsigned.Spec
    ⟨#v[input.b[0], input.b[1], input.b[2], e13],
     #v[input.cc[0], input.cc[1], input.cc[2], e17], input.cols.result, input.is_real⟩

/-- The composed `LtOperationUnsigned` sub-assertion's `main` reconstructs the result column vectors
element-wise (`#v[r.u16_flags[0], …]`); these eta lemmas fold them back to the whole vector so the
sub `Spec` matches the clean `input.cols.result`. -/
private lemma vec4_eta {α : Type} (v : Vector α 4) : #v[v[0], v[1], v[2], v[3]] = v := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl
private lemma vec2_eta {α : Type} (v : Vector α 2) : #v[v[0], v[1]] = v := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl

/-- `(0 : ZMod p) ≠ 1`. -/
private lemma zero_ne_one' : (0 : ZMod p) ≠ 1 := by
  intro h; haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have := congrArg ZMod.val h; rw [ZMod.val_zero, ZMod.val_one] at this; exact absurd this (by norm_num)

set_option maxHeartbeats 800000 in
/-- Semantic readout (consumed by `LtChip`/`BranchChip` soundness): on a real row the compare `bit`
is the signed (`is_signed = 1`, via `toInt`) / unsigned (`is_signed = 0`, via `toNat`) less-than
indicator, and on the unsigned branch the flags sum to `0` exactly when the words are equal. -/
theorem result_semantic {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc) (hir : input.is_real = 1)
    (hs : Spec input) :
    (input.cols.result.u16_compare_operation.bit =
      if (if input.is_signed = 1
          then (Word.toBitVec64 input.b).toInt < (Word.toBitVec64 input.cc).toInt
          else Word.toNat input.b < Word.toNat input.cc)
        then 1 else 0) ∧
    (input.is_signed = 0 →
      ((input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
          + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 0)
        ↔ Word.toBitVec64 input.b = Word.toBitVec64 input.cc)) ∧
    (input.is_signed = 0 →
      (input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
          + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 0 ∨
       input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
          + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 1)) := by
  obtain ⟨his, _hirb, _hbmb, _hcmb, _hg5, hg7, hg9, hbm_eq, hcm_eq, h_uns⟩ := hs
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one'
  rcases his with hs0 | hs1
  · -- `is_signed = 0`: `bm = cm = 0`, the unsigned compare on the unbiased words.
    have hbm0 : input.cols.b_msb.msb = 0 := by rw [hs0] at hg7; linear_combination -hg7
    have hcm0 : input.cols.c_msb.msb = 0 := by rw [hs0] at hg9; linear_combination -hg9
    rw [hs0, hbm0, hcm0] at h_uns
    simp only [zero_mul, mul_zero, sub_zero, add_zero] at h_uns
    have hbU64 : Word.isU64 #v[input.b[0], input.b[1], input.b[2], input.b[3]] :=
      Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hb3)
    have hcU64 : Word.isU64 #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]] :=
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hc3)
    have hbit := LtOperationUnsigned.result_semantic hbU64 hcU64 hir h_uns
    refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · rw [hbit.1]
      simp only [hs0, if_neg h01, Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      rfl
    · rw [toBitVec64_eq_iff hb hcc]
      have key := hbit.2
      simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at key ⊢
      exact key
    · exact h_uns.2.2.2.2.1
  · -- `is_signed = 1`: `bm`/`cm` are the sign bits; the unsigned compare of the bias-flipped words.
    have hbm : input.cols.b_msb.msb = if input.b[3].val ≥ 32768 then 1 else 0 := hbm_eq hs1
    have hcm : input.cols.c_msb.msb = if input.cc[3].val ≥ 32768 then 1 else 0 := hcm_eq hs1
    rw [hs1] at h_uns
    simp only [one_mul] at h_uns
    have hbU : (input.b[3] + 32768 - 65536 * input.cols.b_msb.msb).val < 2 ^ 16 := by
      rw [hbm]; exact (adj_limb hb3).2
    have hcU : (input.cc[3] + 32768 - 65536 * input.cols.c_msb.msb).val < 2 ^ 16 := by
      rw [hcm]; exact (adj_limb hc3).2
    have hbU64 : Word.isU64
        #v[input.b[0], input.b[1], input.b[2], input.b[3] + 32768 - 65536 * input.cols.b_msb.msb] :=
      Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbU)
    have hcU64 : Word.isU64
        #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3] + 32768 - 65536 * input.cols.c_msb.msb] :=
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hcU)
    have hbit := LtOperationUnsigned.result_semantic hbU64 hcU64 hir h_uns
    refine ⟨?_, fun h => absurd (h ▸ hs1) h01, fun h => absurd (h ▸ hs1) h01⟩
    rw [hbit.1]
    simp only [hs1, ↓reduceIte, toInt_compare_of_bias hb hcc hbm hcm]

set_option maxHeartbeats 1000000 in
/-- The witnessed columns `populate b cc is_signed is_real` satisfy the gadget `Spec`. The composing
chip uses this to discharge the `assertion LtOperationSigned.circuit` obligation. -/
theorem spec_populate {b cc : Word (ZMod p)} {is_signed is_real : ZMod p}
    (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (hs_bin : is_signed = 0 ∨ is_signed = 1) (hr_bin : is_real = 0 ∨ is_real = 1)
    (h_gate : (is_real - 1) * is_signed = 0) :
    Spec (⟨b, cc, populate b cc is_signed is_real, is_signed, is_real⟩ : Inputs (ZMod p)) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one'
  have hpmb : U16MSBOperation.populate_msb b[3] = if b[3].val ≥ 32768 then 1 else 0 :=
    (U16MSBOperation.spec_populate (by simpa using hb3) 1).2 rfl
  have hpmc : U16MSBOperation.populate_msb cc[3] = if cc[3].val ≥ 32768 then 1 else 0 :=
    (U16MSBOperation.spec_populate (by simpa using hc3) 1).2 rfl
  have hbmb : U16MSBOperation.populate_msb b[3] = 0 ∨ U16MSBOperation.populate_msb b[3] = 1 :=
    U16MSBOperation.populate_msb_bool (by simpa using hb3)
  have hcmb : U16MSBOperation.populate_msb cc[3] = 0 ∨ U16MSBOperation.populate_msb cc[3] = 1 :=
    U16MSBOperation.populate_msb_bool (by simpa using hc3)
  simp only [Spec, populate]
  refine ⟨hs_bin, hr_bin, ?_, ?_, h_gate, ?_, ?_, ?_, ?_, ?_⟩
  · -- `b_msb = is_signed * populate_msb` is boolean
    rcases hs_bin with h | h <;> rw [h]
    · left; ring
    · rw [one_mul]; exact hbmb
  · rcases hs_bin with h | h <;> rw [h]
    · left; ring
    · rw [one_mul]; exact hcmb
  · -- `(is_signed - 1) * (is_signed * populate_msb) = 0`
    rcases hs_bin with h | h <;> rw [h] <;> ring
  · rcases hs_bin with h | h <;> rw [h] <;> ring
  · -- `is_signed = 1 → b_msb = high bit`
    intro h1; rw [h1, one_mul, hpmb]
  · intro h1; rw [h1, one_mul, hpmc]
  · -- the composed `LtOperationUnsigned.Spec` on the sign-adjusted words
    by_cases hr1 : is_real = 1
    · subst hr1
      rw [if_pos rfl]
      exact LtOperationUnsigned.spec_populate
    · rw [if_neg hr1]
      have hr0 : is_real = 0 := Or.resolve_right hr_bin hr1
      subst hr0
      -- all-zero unsigned columns satisfy `LtOperationUnsigned.Spec` at `is_real = 0`
      simp [LtOperationUnsigned.Spec]

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hb_u64, hcc_u64, hir_bin, his_bin⟩ := h_assumptions
  obtain ⟨hib, hicc, ⟨⟨_, hflags, _, hcl⟩, _, _⟩, _, _⟩ := h_input
  have eb : ∀ i (hi : i < 4), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_result_u16_flags[i] = input_cols_result_u16_flags[i] := by
    intro i hi; rw [← hflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2), Expression.eval env input_var_cols_result_comparison_limbs[i]
      = input_cols_result_comparison_limbs[i] := by
    intro i hi; rw [← hcl]; simp only [Vector.getElem_map]
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb_u64
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc_u64
  obtain ⟨h_msb_b, h_msb_c, h_lt, _, _, hE5, hE7, hE9⟩ := h_holds
  simp only [eb, ec, ef, ecl, vec4_eta, vec2_eta]
    at h_msb_b h_msb_c h_lt hE5 hE7 hE9 ⊢
  -- the two `U16MSBOperation` sub-assertion `Assumptions` (16-bit operands, `is_signed` binary).
  have hAb : U16MSBOperation.circuit.Assumptions
      ⟨input_b[3], ⟨input_cols_b_msb_msb⟩, input_is_signed⟩ := ⟨fun _ => hb3, his_bin⟩
  have hAc : U16MSBOperation.circuit.Assumptions
      ⟨input_cc[3], ⟨input_cols_c_msb_msb⟩, input_is_signed⟩ := ⟨fun _ => hc3, his_bin⟩
  obtain ⟨hbm_bool, hbm_eq⟩ := h_msb_b hAb
  obtain ⟨hcm_bool, hcm_eq⟩ := h_msb_c hAc
  -- defeq-reduced forms (the sub `Spec`'s `{…}.cols.msb` / `{…}.a.val` projections reduce).
  have hbm_bool' : input_cols_b_msb_msb = 0 ∨ input_cols_b_msb_msb = 1 := hbm_bool
  have hcm_bool' : input_cols_c_msb_msb = 0 ∨ input_cols_c_msb_msb = 1 := hcm_bool
  have hbm_eq' : input_is_signed = 1 → input_cols_b_msb_msb = if input_b[3].val ≥ 32768 then 1 else 0 := hbm_eq
  have hcm_eq' : input_is_signed = 1 → input_cols_c_msb_msb = if input_cc[3].val ≥ 32768 then 1 else 0 := hcm_eq
  -- the `LtOperationUnsigned` sub-assertion `Assumptions` (the sign-adjusted words are 16-bit).
  have hbtop : (input_b[3] + input_is_signed * 32768 - 65536 * input_cols_b_msb_msb).val < 2 ^ 16 := by
    rcases his_bin with h | h
    · have h7 := hE7; rw [h] at h7
      have hbm0 : input_cols_b_msb_msb = 0 := by simpa using h7
      rw [h, hbm0]; simpa using hb3
    · rw [h, one_mul, hbm_eq' h]; simpa using (adj_limb hb3).2
  have hctop : (input_cc[3] + input_is_signed * 32768 - 65536 * input_cols_c_msb_msb).val < 2 ^ 16 := by
    rcases his_bin with h | h
    · have h9 := hE9; rw [h] at h9
      have hcm0 : input_cols_c_msb_msb = 0 := by simpa using h9
      rw [h, hcm0]; simpa using hc3
    · rw [h, one_mul, hcm_eq' h]; simpa using (adj_limb hc3).2
  have hAlt : LtOperationUnsigned.circuit.Assumptions
      ⟨#v[input_b[0], input_b[1], input_b[2], input_b[3] + input_is_signed * 32768 - 65536 * input_cols_b_msb_msb],
       #v[input_cc[0], input_cc[1], input_cc[2], input_cc[3] + input_is_signed * 32768 - 65536 * input_cols_c_msb_msb],
       ⟨⟨input_cols_result_u16_compare_operation_bit⟩, input_cols_result_u16_flags,
         input_cols_result_not_eq_inv, input_cols_result_comparison_limbs⟩, input_is_real⟩ :=
    ⟨fun _ => ⟨Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbtop),
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hctop)⟩, hir_bin⟩
  exact ⟨⟨his_bin, hir_bin, hbm_bool', hcm_bool', hE5, hE7, hE9, hbm_eq', hcm_eq', h_lt hAlt⟩,
    Or.inr hAb, Or.inr hAc, Or.inr hAlt⟩

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hb_u64, hcc_u64, hir_bin, his_bin⟩ := h_assumptions
  obtain ⟨_, _, hbm_bool, hcm_bool, hg5, hg7, hg9, hbm_eq, hcm_eq, h_uns_spec⟩ := h_spec
  obtain ⟨hib, hicc, ⟨⟨_, hflags, _, hcl⟩, _, _⟩, _, _⟩ := h_input
  have eb : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cols_result_u16_flags[i]
      = input_cols_result_u16_flags[i] := by
    intro i hi; rw [← hflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env.toEnvironment input_var_cols_result_comparison_limbs[i]
        = input_cols_result_comparison_limbs[i] := by
    intro i hi; rw [← hcl]; simp only [Vector.getElem_map]
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb_u64
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc_u64
  have hbtop : (input_b[3] + input_is_signed * 32768 - 65536 * input_cols_b_msb_msb).val < 2 ^ 16 := by
    rcases his_bin with h | h
    · have h7 := hg7; rw [h] at h7
      have hbm0 : input_cols_b_msb_msb = 0 := by simpa using h7
      rw [h, hbm0]; simpa using hb3
    · rw [h, one_mul, hbm_eq h]; simpa using (adj_limb hb3).2
  have hctop : (input_cc[3] + input_is_signed * 32768 - 65536 * input_cols_c_msb_msb).val < 2 ^ 16 := by
    rcases his_bin with h | h
    · have h9 := hg9; rw [h] at h9
      have hcm0 : input_cols_c_msb_msb = 0 := by simpa using h9
      rw [h, hcm0]; simpa using hc3
    · rw [h, one_mul, hcm_eq h]; simpa using (adj_limb hc3).2
  simp only [eb, ec, ef, ecl, vec4_eta, vec2_eta]
  refine ⟨⟨⟨fun _ => hb3, his_bin⟩, hbm_bool, hbm_eq⟩,
    ⟨⟨fun _ => hc3, his_bin⟩, hcm_bool, hcm_eq⟩,
    ⟨⟨fun _ => ⟨Word.isU64_of_cases (by simpa using hb0) (by simpa using hb1) (by simpa using hb2)
        (by simpa using hbtop),
      Word.isU64_of_cases (by simpa using hc0) (by simpa using hc1) (by simpa using hc2)
        (by simpa using hctop)⟩, hir_bin⟩, h_uns_spec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rcases his_bin with h | h <;> rw [h] <;> simp
  · rcases hir_bin with h | h <;> rw [h] <;> simp
  · exact hg5
  · exact hg7
  · exact hg9

/-- SP1's `LtOperationSigned::eval` as a Clean-native `FormalAssertion`: composes two
`U16MSBOperation` and one `LtOperationUnsigned` as sub-assertions, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.LtOperationSigned
