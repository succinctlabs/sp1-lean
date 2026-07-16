import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Native.Operations.MulOperation
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal
import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels

/-! # `DivRemChip` — constraint-extraction helpers

The *plumbing* layer of the `DivRem` chip soundness: variant-independent lemmas that turn the raw,
in-context circuit hypotheses (the byte-bus `Guarantees`, the two `MulOperation` `Assumptions → Spec`
implications) into the clean structured facts (`.val < 2^16`, `Word.isU64`, the Mul result word's
`toBitVec64` product form) that the `Soundness`/`Math` consumers expect. Stated over **loose**
variables (a Word `qc`/`c`, an opaque result-column `cols`, a bare `ByteRowSpec`), never over the
chip's `cols`/`env.get` terms — so `Formal.lean` does the offset bookkeeping once and applies these.

Kept out of `Formal.lean` so each extraction step is an independently-checkable named lemma that
compiles fast (no heavy `circuit_norm` reduction). -/

namespace SP1Clean.DivRemChip

open SP1Clean
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## `IsZeroWordOperation` result-field projection

`IsZeroWordOperation.result_semantic` exposes the divide-by-zero result on `h_isc0`'s destructured
witness form; the chip's `ownAsserts` gates carry the folded `(fromElements w_is_c_0).result`. The two
are defeq but their `whnf` is heartbeat-prohibitive inside the soundness theorem. This pays the
`fromElements`/`componentsFromElements` reduction ONCE here (the `result` field is flat element 10 — four
`IsZeroOperation` limbs × 2 + two halves + result), so `Formal` rewrites both forms to a cheap
element-level comparison. -/

/-- The base `field` `ProvableType.fromElements` is the single element (generic over the carrier `F`,
so it matches both the `Var` (`Expression`) and the evaluated (`ZMod p`) struct forms). -/
lemma field_fromElements_one {F : Type} (v : Vector F 1) :
    (fromElements v : field F) = v[0] := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [_], _ => rfl

set_option maxHeartbeats 4000000 in
lemma iszeroword_result_proj {F : Type} (W : Vector F 11) :
    (fromElements W : Extracted.IsZeroWordOperation F).result = W[10] := by
  -- 4.30: `ProvableType.fromStruct` is an *instance* that `simp` no longer unfolds; unfold the
  -- `fromElements` projection + the instance explicitly to expose the `field`-`fromElements` slice.
  unfold ProvableType.fromElements ProvableType.fromStruct
  simp only [ProvableStruct.componentsFromElements, circuit_norm]
  rw [field_fromElements_one]
  simp only [Vector.getElem_cast, Vector.getElem_take, Vector.getElem_drop, Nat.reduceAdd]

set_option maxHeartbeats 4000000 in
/-- `IsEqualWordOperation` wraps a single `is_diff_zero : IsZeroWordOperation` (11 elements), so the
overflow flags `is_overflow_b`/`is_overflow_c` (witnessed `fromElements` over 11 scalars) expose their
`.is_diff_zero.result` at the same flat element 10. The single-field `fromElements`'s `.is_diff_zero`
is **defeq** to the inner `IsZeroWord` `fromElements` (cast/take only — does NOT force the expensive
`.result` field), so a cheap `rfl` bridges to `iszeroword_result_proj`. -/
lemma iseqword_result_proj {F : Type} (W : Vector F 11) :
    (fromElements W : Extracted.IsEqualWordOperation F).is_diff_zero.result = W[10] := by
  have hd : toComponents (fromElements W : Extracted.IsEqualWordOperation F)
      = ProvableStruct.ProvableTypeList.cons
          (fromElements W : Extracted.IsEqualWordOperation F).is_diff_zero
          ProvableStruct.ProvableTypeList.nil := rfl
  have ht : toComponents (fromElements W : Extracted.IsEqualWordOperation F)
      = ProvableStruct.ProvableTypeList.cons (fromElements W : Extracted.IsZeroWordOperation F)
          ProvableStruct.ProvableTypeList.nil := by
    rw [show (fromElements W : Extracted.IsEqualWordOperation F)
          = fromComponents (ProvableStruct.componentsFromElements
              (components Extracted.IsEqualWordOperation)
              ((W).cast ProvableStruct.combinedSize_eq)) from rfl,
        ProvableStruct.toComponents_fromComponents]
    -- Lean 4.31 no longer unfolds this implicit-reducible instance at `simp`'s default transparency.
    -- Reduce it once, coherently with the dependent vector casts, before peeling the one-field list.
    dsimp +instances only [components, Extracted.instProvableStructIsEqualWordOperation]
    rw [← ProvableStruct.fromElements_toElements
      [{ type := Extracted.IsZeroWordOperation, provableType := inferInstance }]
      (ProvableStruct.ProvableTypeList.cons
        (fromElements W : Extracted.IsZeroWordOperation F)
        ProvableStruct.ProvableTypeList.nil)]
    apply congrArg (ProvableStruct.componentsFromElements
      [{ type := Extracted.IsZeroWordOperation, provableType := inferInstance }])
    simp only [ProvableStruct.componentsToElements, ProvableType.toElements_fromElements,
      Vector.cast_rfl]
    apply Vector.ext
    intro i hi
    rfl
  have h1 : (fromElements W : Extracted.IsEqualWordOperation F).is_diff_zero
      = (fromElements W : Extracted.IsZeroWordOperation F) := by
    have h := hd.symm.trans ht
    injection h
  exact (congrArg Extracted.IsZeroWordOperation.result h1).trans (iszeroword_result_proj W)

/-! ## Byte-bus range extraction -/

/-- Extract the `Range` bound `x.val < 2 ^ w.val` from a byte-table membership `⟨6, x, w, 0⟩` with a
**symbolic** width column `w`. The `opcode = 6` column pins the `ByteOpcode` to `Range`
(`cast_le6_inj`), whose `constrain` is exactly the bound. (Public sibling of the `private`
`ShiftRightChip.byteRowSpec_range_val`; co-located here as the single shared home.) -/
lemma byteRowSpec_range_val {x w : ZMod p}
    (h : ByteRowSpec (⟨6, x, w, 0⟩ : ByteRow (ZMod p))) : x.val < 2 ^ w.val := by
  obtain ⟨op, hop, hc⟩ := h
  have hk : op.idx = 6 := cast_le6_inj (by cases op <;> decide) (by norm_num) (by rw [hop]; norm_cast)
  cases op <;> simp only [ByteOpcode.idx] at hk <;>
    first
      | omega
      | (simp only [ByteOpcode.constrain] at hc; exact hc)

/-- `(16 : ZMod p).val = 16` (the byte-bus 16-bit range width column). -/
@[simp] lemma val_16_zmod_p : (16 : ZMod p).val = 16 := by
  have : (2 ^ 17 : ℕ) < p := Fact.out
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

/-- A 16-bit byte-bus pull `⟨6, v, 16, 0⟩` gives `v.val < 2^16`. The byte channel's `Guarantees` is
definitionally `ByteRowSpec`, so `Formal` applies this directly to `hb_* hr` (the real-row guarantee).
-/
lemma isU16_of_byteRowSpec {v : ZMod p}
    (h : ByteRowSpec (⟨6, v, 16, 0⟩ : ByteRow (ZMod p))) : v.val < 2 ^ 16 := by
  have := byteRowSpec_range_val h
  rwa [val_16_zmod_p] at this

/-! ## `MulOperation` sub-circuit `Spec` projection

The chip composes two `MulOperation`s of `quotient_comp × op_c_val`: `mul_lower` (`is_mul = is_real`)
for the low 64 bits and `mul_upper` (`is_mulh = is_div+is_rem` signed / `is_mulhu = is_divu+is_remu`
unsigned) for the high 64 bits. Each is exposed to soundness as an `Assumptions → Spec cols`
implication. The three lemmas below discharge the `Assumptions` (the only nontrivial input is
`isU64 quotient_comp`) and project the active conjunct, returning the result word's `toBitVec64`
product form. -/

/-- `mul_lower`: with `is_mul = ir = 1` (the row is real), the result word is the **low 64 bits** of
`qc · c`. -/
lemma mul_lo_spec {qc c : Word (ZMod p)} {ir : ZMod p} {cols : Extracted.MulOperation (ZMod p)}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1) :
    Word.toBitVec64 (MulOperation.resultWord ⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩ cols)
      = qc.toBitVec64 * c.toBitVec64 := by
  have hAs : MulOperation.circuit.Assumptions
      (⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩ : MulOperation.Inputs (ZMod p)) :=
    ⟨fun _ => ⟨hqcU, hcU⟩, Or.inr hir, fun _ => hir, Or.inr hir, Or.inl rfl, Or.inl rfl, Or.inl rfl,
     Or.inl rfl, Or.inr (by rw [hir]; ring)⟩
  obtain ⟨_, hmul, _, _, _, _⟩ := MulOperation.result_semantic hAs (h hAs) hir
  exact hmul hir

/-- `mul_upper`, unsigned branch: with `is_mulhu = ihmu = 1` and `is_mulh = ihm = 0`, the result word
is the **unsigned high 64 bits** of `qc · c`. -/
lemma mul_hi_spec_unsigned {qc c : Word (ZMod p)} {ir ihm ihmu : ZMod p}
    {cols : Extracted.MulOperation (ZMod p)}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1) (hihm : ihm = 0) (hihmu : ihmu = 1) :
    Word.toBitVec64 (MulOperation.resultWord ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ cols)
      = (((qc.toBitVec64).setWidth 128 * (c.toBitVec64).setWidth 128) >>> 64).setWidth 64 := by
  have hAs : MulOperation.circuit.Assumptions
      (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) :=
    ⟨fun _ => ⟨hqcU, hcU⟩, Or.inr hir, fun _ => hir, Or.inl rfl, Or.inl hihm, Or.inr hihmu, Or.inl rfl,
     Or.inl rfl, Or.inr (by rw [hihm, hihmu]; ring)⟩
  obtain ⟨_, _, hmulhu, _, _, _⟩ := MulOperation.result_semantic hAs (h hAs) hir
  exact hmulhu hihmu

/-- `mul_upper`, signed branch: with `is_mulh = ihm = 1` and `is_mulhu = ihmu = 0`, the result word is
the **signed high 64 bits** of `qc · c`. -/
lemma mul_hi_spec_signed {qc c : Word (ZMod p)} {ir ihm ihmu : ZMod p}
    {cols : Extracted.MulOperation (ZMod p)}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1) (hihm : ihm = 1) (hihmu : ihmu = 0) :
    Word.toBitVec64 (MulOperation.resultWord ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ cols)
      = (((qc.toBitVec64).signExtend 128 * (c.toBitVec64).signExtend 128) >>> 64).setWidth 64 := by
  have hAs : MulOperation.circuit.Assumptions
      (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) :=
    ⟨fun _ => ⟨hqcU, hcU⟩, Or.inr hir, fun _ => hir, Or.inl rfl, Or.inr hihm, Or.inl hihmu, Or.inl rfl,
     Or.inl rfl, Or.inr (by rw [hihm, hihmu]; ring)⟩
  obtain ⟨_, _, _, hmulh, _, _⟩ := MulOperation.result_semantic hAs (h hAs) hir
  exact hmulh hihm

/-! ## `c_times_quotient` gluing — the Mul result word as the `ctq` limbs

The chip's `c_times_quotient[i] === mul_*.product[2i] + mul_*.product[2i+1]·256` asserts glue the two
`MulOperation` result words to the `c_times_quotient` byte vector (`Defs.lean:175-182`). The three
lemmas below combine that gluing with the `Spec` projection: given the four glue equalities (the chip's
`h_ctq*`, phrased on `productVal`) and the `MulOperation` `Assumptions → Spec` implication, the `ctq`
low/high Word's `toBitVec64` *is* the corresponding slice of the product `qc · c`. This is the `hlo`/
`hhi` that `Soundness.hid_of_carry_chain` / `euclid_identity_signed` consume. -/

/-- Low `ctq` limbs (`mul_lower`): `#v[r0,r1,r2,r3].toBitVec64 = qc.toBitVec64 * c.toBitVec64`. The
`hi` hypotheses are the chip's `h_ctq0..3` verbatim (`c_times_quotient[i] = product[2i] +
product[2i+1]·256`). -/
lemma rwlo_product {qc c : Word (ZMod p)} {ir : ZMod p} {cols : Extracted.MulOperation (ZMod p)}
    {r0 r1 r2 r3 : ZMod p}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1)
    (h0 : r0 = cols.product[0] + cols.product[1] * 256)
    (h1 : r1 = cols.product[2] + cols.product[3] * 256)
    (h2 : r2 = cols.product[4] + cols.product[5] * 256)
    (h3 : r3 = cols.product[6] + cols.product[7] * 256) :
    Word.toBitVec64 (#v[r0, r1, r2, r3] : Word (ZMod p)) = qc.toBitVec64 * c.toBitVec64 := by
  have hrw : (#v[r0, r1, r2, r3] : Word (ZMod p))
      = MulOperation.resultWord ⟨qc, c, cols, ir, ir, 0, 0, 0, 0⟩ cols := by
    rw [h0, h1, h2, h3]; simp only [MulOperation.resultWord, MulOperation.productVal]; norm_num
  rw [hrw]; exact mul_lo_spec h hqcU hcU hir

/-- High `ctq` limbs (`mul_upper`, unsigned): the unsigned high 64 of `qc · c`. -/
lemma rwhi_product_unsigned {qc c : Word (ZMod p)} {ir ihm ihmu : ZMod p}
    {cols : Extracted.MulOperation (ZMod p)} {r4 r5 r6 r7 : ZMod p}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1) (hihm : ihm = 0) (hihmu : ihmu = 1)
    (h4 : r4 = cols.product[8] + cols.product[9] * 256)
    (h5 : r5 = cols.product[10] + cols.product[11] * 256)
    (h6 : r6 = cols.product[12] + cols.product[13] * 256)
    (h7 : r7 = cols.product[14] + cols.product[15] * 256) :
    Word.toBitVec64 (#v[r4, r5, r6, r7] : Word (ZMod p))
      = (((qc.toBitVec64).setWidth 128 * (c.toBitVec64).setWidth 128) >>> 64).setWidth 64 := by
  have hrw : (#v[r4, r5, r6, r7] : Word (ZMod p))
      = MulOperation.resultWord ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ cols := by
    rw [h4, h5, h6, h7]; simp only [MulOperation.resultWord, MulOperation.productVal]
    rw [if_neg (by norm_num), if_pos (Or.inr (Or.inl hihmu))]; norm_num
  rw [hrw]; exact mul_hi_spec_unsigned h hqcU hcU hir hihm hihmu

/-- High `ctq` limbs (`mul_upper`, signed): the signed high 64 of `qc · c`. -/
lemma rwhi_product_signed {qc c : Word (ZMod p)} {ir ihm ihmu : ZMod p}
    {cols : Extracted.MulOperation (ZMod p)} {r4 r5 r6 r7 : ZMod p}
    (h : MulOperation.circuit.Assumptions (⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ : MulOperation.Inputs (ZMod p)) →
         MulOperation.circuit.Spec ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩)
    (hqcU : qc.isU64) (hcU : c.isU64) (hir : ir = 1) (hihm : ihm = 1) (hihmu : ihmu = 0)
    (h4 : r4 = cols.product[8] + cols.product[9] * 256)
    (h5 : r5 = cols.product[10] + cols.product[11] * 256)
    (h6 : r6 = cols.product[12] + cols.product[13] * 256)
    (h7 : r7 = cols.product[14] + cols.product[15] * 256) :
    Word.toBitVec64 (#v[r4, r5, r6, r7] : Word (ZMod p))
      = (((qc.toBitVec64).signExtend 128 * (c.toBitVec64).signExtend 128) >>> 64).setWidth 64 := by
  have hrw : (#v[r4, r5, r6, r7] : Word (ZMod p))
      = MulOperation.resultWord ⟨qc, c, cols, ir, 0, ihm, ihmu, 0, 0⟩ cols := by
    rw [h4, h5, h6, h7]; simp only [MulOperation.resultWord, MulOperation.productVal]
    rw [if_neg (by norm_num), if_pos (Or.inl hihm)]; norm_num
  rw [hrw]; exact mul_hi_spec_signed h hqcU hcU hir hihm hihmu

/-! ## Signed overflow detection (`is_overflow = 1` ⟹ `b = i64::MIN`, `c = -1`) -/

/-- From the two `IsEqualWordOperation` `Spec`s (`b` vs `#v[0,0,0,32768]` = `i64::MIN`'s limbs, `c` vs
`#v[65535,65535,65535,65535]` = `-1`'s limbs) on a real gate, plus the product of their result bits being
`1` (the chip's `is_overflow = is_overflow_b·is_overflow_c·E10` pinned to `1`), the operands are exactly
`i64::MIN` and `-1`. The `result_semantic` if-conditions are the limb matches; both products being `1`
forces both conditions. Loose over the structs, so `Formal` supplies the evaluated `Spec`s + the product
fact (no cast-fold on the spec side). -/
lemma overflow_of_iseqword {b c : Word (ZMod p)}
    {ovb ovc : Extracted.IsEqualWordOperation (ZMod p)} {ir : ZMod p}
    (hbU : b.isU64) (hcU : c.isU64) (hir : ir = 1)
    (hb_spec : IsEqualWordOperation.Spec ⟨b, #v[0, 0, 0, 32768], ovb, ir⟩)
    (hc_spec : IsEqualWordOperation.Spec ⟨c, #v[65535, 65535, 65535, 65535], ovc, ir⟩)
    (hprod : ovb.is_diff_zero.result * ovc.is_diff_zero.result = 1) :
    b.toBitVec64 = BitVec.intMin 64 ∧ c.toBitVec64 = -1#64 := by
  have hrb := IsEqualWordOperation.result_semantic hb_spec hir
  have hrc := IsEqualWordOperation.result_semantic hc_spec hir
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hrb hrc
  rw [hrb, hrc] at hprod
  have h32768 : (32768 : ZMod p).val = 32768 :=
    ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
  split_ifs at hprod with hbc hcc
  · obtain ⟨hb0, hb1, hb2, hb3⟩ := hbc
    obtain ⟨hc0, hc1, hc2, hc3⟩ := hcc
    refine ⟨intMin_of_toNat hbU ?_, neg_one_of_toNat hcU ?_⟩
    · rw [Word.toNat_def, hb0, hb1, hb2, hb3]
      simp only [ZMod.val_zero, h32768]; norm_num
    · rw [Word.toNat_def, hc0, hc1, hc2, hc3]
      simp only [val_65535_zmod_p]; norm_num
  all_goals simp_all

/-- **Half-word overflow.** The `*W` overflow branch uses the *low-half* `IsEqualWord` pair (the operand
columns' bottom two limbs, top two zeroed, against `i32::MIN`/`-1` low halves). Both products being `1`
pins the low-32 operands `extractLsb 31 0 b = i32::MIN`, `extractLsb 31 0 c = -1`, feeding
`Math.divw_remw_overflow`. The 32-bit analogue of `overflow_of_iseqword`. -/
lemma overflow_of_iseqword_word {b c : Word (ZMod p)}
    {ovb ovc : Extracted.IsEqualWordOperation (ZMod p)} {ir : ZMod p}
    (hbU : b.isU64) (hcU : c.isU64) (hir : ir = 1)
    (hb_spec : IsEqualWordOperation.Spec ⟨#v[b[0], b[1], 0, 0], #v[0, 32768, 0, 0], ovb, ir⟩)
    (hc_spec : IsEqualWordOperation.Spec ⟨#v[c[0], c[1], 0, 0], #v[65535, 65535, 0, 0], ovc, ir⟩)
    (hprod : ovb.is_diff_zero.result * ovc.is_diff_zero.result = 1) :
    BitVec.extractLsb 31 0 b.toBitVec64 = BitVec.intMin 32 ∧
    BitVec.extractLsb 31 0 c.toBitVec64 = -1#32 := by
  have hrb := IsEqualWordOperation.result_semantic hb_spec hir
  have hrc := IsEqualWordOperation.result_semantic hc_spec hir
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hrb hrc
  rw [hrb, hrc] at hprod
  have h32768 : (32768 : ZMod p).val = 32768 :=
    ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by have := Fact.out (p := 2 ^ 17 < p); omega)
  split_ifs at hprod with hbc hcc
  · obtain ⟨hb0, hb1, _, _⟩ := hbc
    obtain ⟨hc0, hc1, _, _⟩ := hcc
    refine ⟨?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [extractLsb_lo_toNat hbU, hb0, hb1, BitVec.toNat_intMin]
      simp only [ZMod.val_zero, h32768]; norm_num
    · apply BitVec.eq_of_toNat_eq
      rw [extractLsb_lo_toNat hcU, hc0, hc1, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      simp only [val_65535_zmod_p]; norm_num
  all_goals simp_all

local instance : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- A 4-flag group sum is binary when the flags are binary and their `.val`s sum to `≤ 1` (the one-hot
budget). Used to lift the per-flag one-hot to the variant selectors `E5`/`E6`/`E7`. -/
lemma group_binary4 {a b c d : ZMod p} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (hv : a.val + b.val + c.val + d.val ≤ 1) :
    a + b + c + d = 0 ∨ a + b + c + d = 1 := by
  have v0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have v1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  rcases ha with h | h <;> rcases hb with h' | h' <;> rcases hc with h'' | h'' <;>
    rcases hd with h''' | h''' <;> subst_vars <;>
    first
      | (left; ring1)
      | (right; ring1)
      | (exfalso; omega)

/-- A 2-flag group sum is binary (the word selectors `E6 = is_divw + is_remw`, `E7 = is_divuw + is_remuw`). -/
lemma group_binary2 {a b : ZMod p} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hv : a.val + b.val ≤ 1) : a + b = 0 ∨ a + b = 1 := by
  have v0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have v1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  rcases ha with h | h <;> rcases hb with h' | h' <;> subst_vars <;>
    first
      | (left; ring1)
      | (right; ring1)
      | (exfalso; omega)

/-- One-hot limb bound (the `?_tail` `quotient_comp`/`remainder_comp` `isU64` lever): a high comp-limb `qc`
is pinned by exactly one variant selector — `s5` (64-bit) ⇒ `qc = q` (the byte-checked output limb), `s6`
(signed word) ⇒ `qc = msb·65535` (sign fill, `msb` binary), `s7` (unsigned word) ⇒ `qc = 0`. With the
selectors summing to one and each binary, `qc.val < 2^16` in every case. The `(s5 = s6 = 1)` corner is
excluded by the sum (with `s7` binary). -/
lemma comp_limb_isU16 {s5 s6 s7 qc q msb : ZMod p}
    (hb5 : s5 = 0 ∨ s5 = 1) (hb6 : s6 = 0 ∨ s6 = 1) (hb7 : s7 = 0 ∨ s7 = 1)
    (hsum : s5 + s6 + s7 = 1)
    (h59 : s5 * (qc + -q) = 0) (h54 : s6 * (qc + -(msb * 65535)) = 0) (h51 : s7 * qc = 0)
    (hmsb : msb = 0 ∨ msb = 1) (hq : q.val < 2 ^ 16) : qc.val < 2 ^ 16 := by
  have hqc : qc = s5 * q + s6 * (msb * 65535) := by
    linear_combination h59 + h54 + h51 - qc * hsum
  have hpbig : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rcases hb5 with h5 | h5 <;> rcases hb6 with h6 | h6
  · rw [hqc, h5, h6]; simp
  · rw [hqc, h5, h6]; simp only [zero_mul, one_mul, zero_add]
    rcases hmsb with hm | hm <;> rw [hm] <;> simp [val_65535_zmod_p]
  · rw [hqc, h5, h6]; simp only [one_mul, zero_mul, add_zero]; exact hq
  · exfalso
    rcases hb7 with h7 | h7 <;> rw [h5, h6, h7] at hsum
    · -- 1 + 1 + 0 = 1 ⇒ (1 : ZMod p) = 0
      have h1 : ((1 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hsum
      have := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp h1
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    · -- 1 + 1 + 1 = 1 ⇒ (2 : ZMod p) = 0
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hsum
      have := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)

/-- Operand-column `isU64` for the word-truncated/sign-extended operands `b`/`c`: the low two limbs equal the
raw register read (so `isU64` of the read bounds them), and the high two limbs are `read·(1-e2) + sign·e2·65535`
— the read on 64-bit rows (`e2 = 0`), the sign/zero fill `∈ {0, 65535}` on word rows (`e2 = 1`, `sign` binary).
Every limb is `< 2^16`. -/
lemma operand_isU64 {w : Word (ZMod p)} {r0 r1 r2 r3 e2 s : ZMod p}
    (h0 : w[0] = r0) (h1 : w[1] = r1)
    (h2 : w[2] = r2 * (1 - e2) + s * e2 * 65535) (h3 : w[3] = r3 * (1 - e2) + s * e2 * 65535)
    (hr0 : r0.val < 2 ^ 16) (hr1 : r1.val < 2 ^ 16) (hr2 : r2.val < 2 ^ 16) (hr3 : r3.val < 2 ^ 16)
    (he2 : e2 = 0 ∨ e2 = 1) (hs : s = 0 ∨ s = 1) : Word.isU64 w := by
  apply Word.isU64_of_cases
  · rw [h0]; exact hr0
  · rw [h1]; exact hr1
  · rw [h2]; rcases he2 with he | he <;> rw [he]
    · simpa using hr2
    · rcases hs with hs' | hs' <;> rw [hs'] <;>
        simp only [sub_self, mul_zero, zero_mul, one_mul, mul_one, zero_add, add_zero,
          ZMod.val_zero, val_65535_zmod_p] <;> norm_num
  · rw [h3]; rcases he2 with he | he <;> rw [he]
    · simpa using hr3
    · rcases hs with hs' | hs' <;> rw [hs'] <;>
        simp only [sub_self, mul_zero, zero_mul, one_mul, mul_one, zero_add, add_zero,
          ZMod.val_zero, val_65535_zmod_p] <;> norm_num

set_option linter.unusedSectionVars false in
/-- The low 32 bits of `toBitVec64 w` depend only on limbs 0,1 — the lever for the `*w` read-lift: the
operand and the raw read agree on limbs 0,1 (E20/E22/E21/E23), and `RV64.*w` use only `extractLsb 31 0`. -/
lemma toBitVec64_extractLsb [NeZero p] {w w' : Word (ZMod p)} (hw : w.isU64) (hw' : w'.isU64)
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) :
    BitVec.extractLsb 31 0 (Word.toBitVec64 w) = BitVec.extractLsb 31 0 (Word.toBitVec64 w') := by
  simp only [BitVec.extractLsb, BitVec.extractLsb']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reduceSub, Nat.reduceAdd,
    Word.toBitVec64_toNat hw, Word.toBitVec64_toNat hw', Word.toNat_def, h0, h1]
  have key : ∀ a b c : ℕ, (a + b * 2 ^ 32 + c * 2 ^ 48) % 2 ^ 32 = a % 2 ^ 32 := fun a b c => by
    rw [show a + b * 2 ^ 32 + c * 2 ^ 48 = a + (b + c * 2 ^ 16) * 2 ^ 32 by ring,
        Nat.add_mul_mod_self_right]
  simp only [key]

end SP1Clean.DivRemChip
