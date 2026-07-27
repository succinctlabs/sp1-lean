import SP1Clean.Native.Operations.MulOperation.RawSpec
import SP1Clean.Native.Operations.MulOperation.Populate
import SP1Clean.Native.Operations.MulOperation.Defs
import SP1Clean.Model.ByteTable

/-! # `MulOperation` contract — `Assumptions` / soundness / completeness / `circuit`. -/

namespace SP1Clean.MulOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The five variant selectors are boolean and **at most one** is set (the `{0,1}` sum-bound — the
chip discharges this unconditionally from the in-circuit sum gate, including on padding rows where
the sum is `0`). Operand bounds are conclusions of the two safe byte decompositions, not
composer-supplied preconditions. On an active row exactly one flag is set; `mulSemantics_of_raw`
recovers `sum = 1` per active variant via `sum_eq_one`. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_mulw = 1 → input.is_real = 1) ∧
  (input.is_mul = 0 ∨ input.is_mul = 1) ∧ (input.is_mulh = 0 ∨ input.is_mulh = 1) ∧
  (input.is_mulhu = 0 ∨ input.is_mulhu = 1) ∧ (input.is_mulhsu = 0 ∨ input.is_mulhsu = 1) ∧
  (input.is_mulw = 0 ∨ input.is_mulw = 1) ∧
  (input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 0 ∨
    input.is_mul + input.is_mulh + input.is_mulhu + input.is_mulhsu + input.is_mulw = 1)

/-- The **structural** `FormalAssertion` contract (`is_real`-gated): on a real row the columns are exactly
the schoolbook form — the raw carry-chain (`RawSpec`), the two operand `U16toU8` byte decompositions, and
the three MSB facts (`b_msb`/`c_msb` unconditional, `product_msb` gated on `is_mulw`). This pins **every**
column (so completeness `Assumptions ∧ Spec → constraints` holds — the semantic `resultWord = b·c` slice
alone would *not* pin the high product bytes). The semantic readout is recovered by `result_semantic`,
which consumers use. A padding row owes nothing. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  -- **Ungated** facts (SP1's `eval` asserts these regardless of `is_real`, so they must hold on padding
  -- too): the two sign-extend column definitions (`mul.rs:224-225`) and the three MSB booleanities (the
  -- `U16MSBOperation` sub-`Spec`s carry the bool unconditionally). Completeness needs them on `is_real = 0`.
  (input.cols.b_sign_extend = (input.is_mulh + input.is_mulhsu) * input.cols.b_msb) ∧
  (input.cols.c_sign_extend = input.is_mulh * input.cols.c_msb) ∧
  (input.cols.b_msb = 0 ∨ input.cols.b_msb = 1) ∧
  (input.cols.c_msb = 0 ∨ input.cols.c_msb = 1) ∧
  (input.cols.product_msb.msb = 0 ∨ input.cols.product_msb.msb = 1) ∧
  -- **`is_real`-gated** body: the schoolbook carry-chain + ranges (`RawSpec`), the byte decompositions,
  -- and the MSB high-bit equations. Pins the product/carry columns on a real row.
  (input.is_real = 1 →
    RawSpec input input.cols ∧
    U16toU8OperationSafe.DecompSpec input.b input.cols.b_lower_byte ∧
    U16toU8OperationSafe.DecompSpec input.c input.cols.c_lower_byte ∧
    (input.cols.b_msb = if input.b[3].val ≥ 32768 then 1 else 0) ∧
    (input.cols.c_msb = if input.c[3].val ≥ 32768 then 1 else 0) ∧
    (input.cols.product_msb.msb = 0 ∨ input.cols.product_msb.msb = 1) ∧
    (input.is_mulw = 1 → input.cols.product_msb.msb =
      if (input.cols.product[2] + input.cols.product[3] * 256).val ≥ 32768 then 1 else 0))

/-- **Semantic readout** (the consumer-facing lemma, mirroring `LtOperationUnsigned.result_semantic`): the
structural `Spec` + `Assumptions` give the BitVec-product slice for the active variant on a real row. This
is what `MulChip`/`DivRemChip` consume to reach the RV64 semantics. -/
theorem result_semantic {input : Inputs (ZMod p)} (h_assum : Assumptions input)
    (h_spec : Spec input) (hr : input.is_real = 1) : SemanticSpec input input.cols := by
  obtain ⟨_, _, _, _, _, hgated⟩ := h_spec
  obtain ⟨h_raw, hb_low, hc_low, hb_msb, hc_msb, hmsb_bool, hmsb⟩ := hgated hr
  obtain ⟨_, _, hmul_b, hmh_b, hmhu_b, hmhsu_b, hmw_b, hsum⟩ := h_assum
  have hbU := U16toU8OperationSafe.isU64_of_decomp hb_low
  have hcU := U16toU8OperationSafe.isU64_of_decomp hc_low
  exact mulSemantics_of_raw hbU hcU hmul_b hmh_b hmhu_b hmhsu_b hmw_b hsum hb_low hc_low
    hmsb_bool hmsb hb_msb hc_msb h_raw

/-- Bridge from the op5 `MSB` byte guarantee (`msb` is the byte-MSB of `hi = (x-lo)/256`) plus the
`U16toU8` decomposition (`x = lo + hi·256`) to the limb-MSB form `msb = if x.val ≥ 32768 then 1 else 0`. -/
private lemma msb_eq_of_op5 {x lo msb : ZMod p}
    (hlo : lo.val < 256) (hhi : ((x - lo) * 256⁻¹).val < 256)
    (hreass : x = lo + (x - lo) * 256⁻¹ * 256)
    (hbool : msb = 0 ∨ msb = 1) (hiff : msb = 1 ↔ 128 ≤ ((x - lo) * 256⁻¹).val) :
    msb = if x.val ≥ 32768 then 1 else 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hxval : x.val = lo.val + ((x - lo) * 256⁻¹).val * 256 := byte_compose_val hlo hhi hreass
  have key : (32768 ≤ x.val) ↔ (128 ≤ ((x - lo) * 256⁻¹).val) := by omega
  rcases hbool with h0 | h1
  · subst h0; rw [if_neg (fun hx => zero_ne_one (hiff.mpr (key.mp hx)))]
  · subst h1; rw [if_pos (key.mpr (hiff.mp rfl))]

/-- Reverse of `msb_eq_of_op5` (for completeness): recover the op5 `MSB` byte-row content. -/
private lemma op5_iff_of_msb_eq {x lo msb : ZMod p}
    (hlo : lo.val < 256) (hhi : ((x - lo) * 256⁻¹).val < 256)
    (hreass : x = lo + (x - lo) * 256⁻¹ * 256)
    (hmsb : msb = if x.val ≥ 32768 then 1 else 0) :
    (msb = 0 ∨ msb = 1) ∧ (msb = 1 ↔ 128 ≤ ((x - lo) * 256⁻¹).val) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hxval : x.val = lo.val + ((x - lo) * 256⁻¹).val * 256 := byte_compose_val hlo hhi hreass
  have key : (32768 ≤ x.val) ↔ (128 ≤ ((x - lo) * 256⁻¹).val) := by omega
  rw [hmsb]; split
  · rename_i h; exact ⟨Or.inr rfl, iff_of_true rfl (key.mp h)⟩
  · rename_i h; exact ⟨Or.inl rfl, iff_of_false zero_ne_one (fun hc => h (key.mpr hc))⟩

-- 40M: the gadget composes the 8×8 limb product's carry chain plus four sub-gadget boundaries;
-- soundness normalizes all 45 witnessed columns' constraints in one `circuit_proof_start` pass.
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hir_bin, hmw_real, hmul_b, hmh_b, hmhu_b, hmhsu_b, hmw_b, hsum⟩ := h_assumptions
  obtain ⟨hib, hic, _hicols, hir, _him_mul, _him_mulh, _him_mulhu, _him_mulhsu, _him_mulw⟩ := h_input
  obtain ⟨_gate, hA, hB, hpm, hb_bool, hc_bool, hb5, hc5, hcF0, hcF1, hcF2, hcF3, hcF4, hcF5, hcF6, hcF7, hcF8, hcF9, hcF10,
    hcF11, hcF12, hcF13, hcF14, hcF15, hpG0, hpG1, hpG2, hpG3, hpG4, hpG5, hpG6, hpG7,
    hsdb, hsdc, himpb, himpc, hch0, hch1, hch2, hch3, hch4, hch5, hch6, hch7, hch8, hch9, hch10,
    hch11, hch12, hch13, hch14, hch15⟩ := h_holds
  refine ⟨?_spec, ?_tail⟩
  · -- structural `Spec`: 5 ungated facts (sign-extend defs + 3 MSB booleans) then the gated body.
    -- `b_msb`/`c_msb` booleanity from the ungated `b_msb*(b_msb-1)=0` asserts (SP1 `assert_bool`).
    refine ⟨hsdb, hsdc,
      bool_of_mul_pred (by simpa only [sub_eq_add_neg] using hb_bool),
      bool_of_mul_pred (by simpa only [sub_eq_add_neg] using hc_bool),
      (hpm ⟨fun hmw => by
        obtain ⟨_, eprod_eq, _, _, _, _, _, _, _⟩ := _hicols
        have hr1 : input_is_real = 1 := hmw_real hmw
        have ep2 : Expression.eval env input_var_cols_product[2] = input_cols_product[2] := by
          rw [← eprod_eq, Vector.getElem_map]
        have ep3 : Expression.eval env input_var_cols_product[3] = input_cols_product[3] := by
          rw [← eprod_eq, Vector.getElem_map]
        have pb2 : input_cols_product[2].val < 2 ^ 8 := by
          rw [← ep2]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG1 (by rw [hr1]))).1
        have pb3 : input_cols_product[3].val < 2 ^ 8 := by
          rw [← ep3]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG1 (by rw [hr1]))).2
        rw [ep2, ep3, byte_compose_val pb2 pb3 rfl]; omega, hmw_b⟩).1,
      ?_⟩
    intro hr
    have hb_low := (hA hir_bin) hr
    have hc_low := (hB hir_bin) hr
    have hbU := U16toU8OperationSafe.isU64_of_decomp hb_low
    have hcU := U16toU8OperationSafe.isU64_of_decomp hc_low
    obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hbU
    obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hcU
    have hneg : - input_is_real = -1 := by rw [hr]
    have h16p : (16 : ℕ) < p := by
      have h := Fact.out (p := 2 ^ 24 < p); have e : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      omega
    obtain ⟨ecar_eq, eprod_eq, ebl_eq, ecl_eq, ebm_eq, ecm_eq, _, _, _⟩ := _hicols
    have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib, Vector.getElem_map]
    have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib, Vector.getElem_map]
    have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib, Vector.getElem_map]
    have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib, Vector.getElem_map]
    have ec0 : Expression.eval env input_var_c[0] = input_c[0] := by rw [← hic, Vector.getElem_map]
    have ec1 : Expression.eval env input_var_c[1] = input_c[1] := by rw [← hic, Vector.getElem_map]
    have ec2 : Expression.eval env input_var_c[2] = input_c[2] := by rw [← hic, Vector.getElem_map]
    have ec3 : Expression.eval env input_var_c[3] = input_c[3] := by rw [← hic, Vector.getElem_map]
    have ep0 : Expression.eval env input_var_cols_product[0] = input_cols_product[0] := by rw [← eprod_eq, Vector.getElem_map]
    have ep1 : Expression.eval env input_var_cols_product[1] = input_cols_product[1] := by rw [← eprod_eq, Vector.getElem_map]
    have ep2 : Expression.eval env input_var_cols_product[2] = input_cols_product[2] := by rw [← eprod_eq, Vector.getElem_map]
    have ep3 : Expression.eval env input_var_cols_product[3] = input_cols_product[3] := by rw [← eprod_eq, Vector.getElem_map]
    have ep4 : Expression.eval env input_var_cols_product[4] = input_cols_product[4] := by rw [← eprod_eq, Vector.getElem_map]
    have ep5 : Expression.eval env input_var_cols_product[5] = input_cols_product[5] := by rw [← eprod_eq, Vector.getElem_map]
    have ep6 : Expression.eval env input_var_cols_product[6] = input_cols_product[6] := by rw [← eprod_eq, Vector.getElem_map]
    have ep7 : Expression.eval env input_var_cols_product[7] = input_cols_product[7] := by rw [← eprod_eq, Vector.getElem_map]
    have ep8 : Expression.eval env input_var_cols_product[8] = input_cols_product[8] := by rw [← eprod_eq, Vector.getElem_map]
    have ep9 : Expression.eval env input_var_cols_product[9] = input_cols_product[9] := by rw [← eprod_eq, Vector.getElem_map]
    have ep10 : Expression.eval env input_var_cols_product[10] = input_cols_product[10] := by rw [← eprod_eq, Vector.getElem_map]
    have ep11 : Expression.eval env input_var_cols_product[11] = input_cols_product[11] := by rw [← eprod_eq, Vector.getElem_map]
    have ep12 : Expression.eval env input_var_cols_product[12] = input_cols_product[12] := by rw [← eprod_eq, Vector.getElem_map]
    have ep13 : Expression.eval env input_var_cols_product[13] = input_cols_product[13] := by rw [← eprod_eq, Vector.getElem_map]
    have ep14 : Expression.eval env input_var_cols_product[14] = input_cols_product[14] := by rw [← eprod_eq, Vector.getElem_map]
    have ep15 : Expression.eval env input_var_cols_product[15] = input_cols_product[15] := by rw [← eprod_eq, Vector.getElem_map]
    have ecar0 : Expression.eval env input_var_cols_carry[0] = input_cols_carry[0] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar1 : Expression.eval env input_var_cols_carry[1] = input_cols_carry[1] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar2 : Expression.eval env input_var_cols_carry[2] = input_cols_carry[2] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar3 : Expression.eval env input_var_cols_carry[3] = input_cols_carry[3] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar4 : Expression.eval env input_var_cols_carry[4] = input_cols_carry[4] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar5 : Expression.eval env input_var_cols_carry[5] = input_cols_carry[5] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar6 : Expression.eval env input_var_cols_carry[6] = input_cols_carry[6] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar7 : Expression.eval env input_var_cols_carry[7] = input_cols_carry[7] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar8 : Expression.eval env input_var_cols_carry[8] = input_cols_carry[8] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar9 : Expression.eval env input_var_cols_carry[9] = input_cols_carry[9] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar10 : Expression.eval env input_var_cols_carry[10] = input_cols_carry[10] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar11 : Expression.eval env input_var_cols_carry[11] = input_cols_carry[11] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar12 : Expression.eval env input_var_cols_carry[12] = input_cols_carry[12] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar13 : Expression.eval env input_var_cols_carry[13] = input_cols_carry[13] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar14 : Expression.eval env input_var_cols_carry[14] = input_cols_carry[14] := by rw [← ecar_eq, Vector.getElem_map]
    have ecar15 : Expression.eval env input_var_cols_carry[15] = input_cols_carry[15] := by rw [← ecar_eq, Vector.getElem_map]
    have ebl0 : Expression.eval env input_var_cols_b_lower_byte_low_bytes[0] = input_cols_b_lower_byte_low_bytes[0] := by rw [← ebl_eq, Vector.getElem_map]
    have ebl1 : Expression.eval env input_var_cols_b_lower_byte_low_bytes[1] = input_cols_b_lower_byte_low_bytes[1] := by rw [← ebl_eq, Vector.getElem_map]
    have ebl2 : Expression.eval env input_var_cols_b_lower_byte_low_bytes[2] = input_cols_b_lower_byte_low_bytes[2] := by rw [← ebl_eq, Vector.getElem_map]
    have ebl3 : Expression.eval env input_var_cols_b_lower_byte_low_bytes[3] = input_cols_b_lower_byte_low_bytes[3] := by rw [← ebl_eq, Vector.getElem_map]
    have ecl0 : Expression.eval env input_var_cols_c_lower_byte_low_bytes[0] = input_cols_c_lower_byte_low_bytes[0] := by rw [← ecl_eq, Vector.getElem_map]
    have ecl1 : Expression.eval env input_var_cols_c_lower_byte_low_bytes[1] = input_cols_c_lower_byte_low_bytes[1] := by rw [← ecl_eq, Vector.getElem_map]
    have ecl2 : Expression.eval env input_var_cols_c_lower_byte_low_bytes[2] = input_cols_c_lower_byte_low_bytes[2] := by rw [← ecl_eq, Vector.getElem_map]
    have ecl3 : Expression.eval env input_var_cols_c_lower_byte_low_bytes[3] = input_cols_c_lower_byte_low_bytes[3] := by rw [← ecl_eq, Vector.getElem_map]
    have cb0 : input_cols_carry[0].val < 2 ^ 16 := by rw [← ecar0]; exact (byteRowSpec_range _ h16p).mp (hcF0 hneg)
    have cb1 : input_cols_carry[1].val < 2 ^ 16 := by rw [← ecar1]; exact (byteRowSpec_range _ h16p).mp (hcF1 hneg)
    have cb2 : input_cols_carry[2].val < 2 ^ 16 := by rw [← ecar2]; exact (byteRowSpec_range _ h16p).mp (hcF2 hneg)
    have cb3 : input_cols_carry[3].val < 2 ^ 16 := by rw [← ecar3]; exact (byteRowSpec_range _ h16p).mp (hcF3 hneg)
    have cb4 : input_cols_carry[4].val < 2 ^ 16 := by rw [← ecar4]; exact (byteRowSpec_range _ h16p).mp (hcF4 hneg)
    have cb5 : input_cols_carry[5].val < 2 ^ 16 := by rw [← ecar5]; exact (byteRowSpec_range _ h16p).mp (hcF5 hneg)
    have cb6 : input_cols_carry[6].val < 2 ^ 16 := by rw [← ecar6]; exact (byteRowSpec_range _ h16p).mp (hcF6 hneg)
    have cb7 : input_cols_carry[7].val < 2 ^ 16 := by rw [← ecar7]; exact (byteRowSpec_range _ h16p).mp (hcF7 hneg)
    have cb8 : input_cols_carry[8].val < 2 ^ 16 := by rw [← ecar8]; exact (byteRowSpec_range _ h16p).mp (hcF8 hneg)
    have cb9 : input_cols_carry[9].val < 2 ^ 16 := by rw [← ecar9]; exact (byteRowSpec_range _ h16p).mp (hcF9 hneg)
    have cb10 : input_cols_carry[10].val < 2 ^ 16 := by rw [← ecar10]; exact (byteRowSpec_range _ h16p).mp (hcF10 hneg)
    have cb11 : input_cols_carry[11].val < 2 ^ 16 := by rw [← ecar11]; exact (byteRowSpec_range _ h16p).mp (hcF11 hneg)
    have cb12 : input_cols_carry[12].val < 2 ^ 16 := by rw [← ecar12]; exact (byteRowSpec_range _ h16p).mp (hcF12 hneg)
    have cb13 : input_cols_carry[13].val < 2 ^ 16 := by rw [← ecar13]; exact (byteRowSpec_range _ h16p).mp (hcF13 hneg)
    have cb14 : input_cols_carry[14].val < 2 ^ 16 := by rw [← ecar14]; exact (byteRowSpec_range _ h16p).mp (hcF14 hneg)
    have cb15 : input_cols_carry[15].val < 2 ^ 16 := by rw [← ecar15]; exact (byteRowSpec_range _ h16p).mp (hcF15 hneg)
    have pb0 : input_cols_product[0].val < 2 ^ 8 := by rw [← ep0]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG0 hneg)).1
    have pb1 : input_cols_product[1].val < 2 ^ 8 := by rw [← ep1]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG0 hneg)).2
    have pb2 : input_cols_product[2].val < 2 ^ 8 := by rw [← ep2]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG1 hneg)).1
    have pb3 : input_cols_product[3].val < 2 ^ 8 := by rw [← ep3]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG1 hneg)).2
    have pb4 : input_cols_product[4].val < 2 ^ 8 := by rw [← ep4]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG2 hneg)).1
    have pb5 : input_cols_product[5].val < 2 ^ 8 := by rw [← ep5]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG2 hneg)).2
    have pb6 : input_cols_product[6].val < 2 ^ 8 := by rw [← ep6]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG3 hneg)).1
    have pb7 : input_cols_product[7].val < 2 ^ 8 := by rw [← ep7]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG3 hneg)).2
    have pb8 : input_cols_product[8].val < 2 ^ 8 := by rw [← ep8]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG4 hneg)).1
    have pb9 : input_cols_product[9].val < 2 ^ 8 := by rw [← ep9]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG4 hneg)).2
    have pb10 : input_cols_product[10].val < 2 ^ 8 := by rw [← ep10]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG5 hneg)).1
    have pb11 : input_cols_product[11].val < 2 ^ 8 := by rw [← ep11]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG5 hneg)).2
    have pb12 : input_cols_product[12].val < 2 ^ 8 := by rw [← ep12]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG6 hneg)).1
    have pb13 : input_cols_product[13].val < 2 ^ 8 := by rw [← ep13]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG6 hneg)).2
    have pb14 : input_cols_product[14].val < 2 ^ 8 := by rw [← ep14]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG7 hneg)).1
    have pb15 : input_cols_product[15].val < 2 ^ 8 := by rw [← ep15]; exact ((byteRowSpec_u8range_pair _ _).mp (hpG7 hneg)).2
    simp only [hr, one_mul, id_eq, ep0, ep1, ep2, ep3, ep4, ep5, ep6, ep7, ep8, ep9, ep10, ep11, ep12, ep13, ep14, ep15, ecar0, ecar1, ecar2, ecar3, ecar4, ecar5, ecar6, ecar7, ecar8, ecar9, ecar10, ecar11, ecar12, ecar13, ecar14, ecar15, ebl0, ebl1, ebl2, ebl3, ecl0, ecl1, ecl2, ecl3, eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3] at hch0 hch1 hch2 hch3 hch4 hch5 hch6 hch7 hch8 hch9 hch10 hch11 hch12 hch13 hch14 hch15
    have hpmspec := hpm ⟨fun _ => by rw [ep2, ep3, byte_compose_val pb2 pb3 rfl]; omega, hmw_b⟩
    have hmsb_bool : input_cols_product_msb_msb = 0 ∨ input_cols_product_msb_msb = 1 := hpmspec.1
    have hmsb : input_is_mulw = 1 → input_cols_product_msb_msb =
        if (input_cols_product[2] + input_cols_product[3] * 256).val ≥ 32768 then 1 else 0 := by
      intro h; have := hpmspec.2 h; rwa [ep2, ep3] at this
    have hb_msb : input_cols_b_msb = if input_b[3].val ≥ 32768 then 1 else 0 := by
      obtain ⟨hlo3, hhi3, hreass3⟩ := hb_low 3
      dsimp only at hlo3 hhi3 hreass3
      have hg := (byteRowSpec_msb _ _).mp (hb5 hneg)
      simp only [circuit_norm, eb3, ebl3, ebm_eq, ← sub_eq_add_neg] at hg
      exact msb_eq_of_op5 hlo3 hhi3 hreass3 hg.2.1 hg.2.2
    have hc_msb : input_cols_c_msb = if input_c[3].val ≥ 32768 then 1 else 0 := by
      obtain ⟨hlo3, hhi3, hreass3⟩ := hc_low 3
      dsimp only at hlo3 hhi3 hreass3
      have hg := (byteRowSpec_msb _ _).mp (hc5 hneg)
      simp only [circuit_norm, ec3, ecl3, ecm_eq, ← sub_eq_add_neg] at hg
      exact msb_eq_of_op5 hlo3 hhi3 hreass3 hg.2.1 hg.2.2
    refine ⟨?_, hb_low, hc_low, hb_msb, hc_msb, hmsb_bool, hmsb⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      interval_cases k
      · rw [colSum_0]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch0
      · rw [colSum_1]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch1
      · rw [colSum_2]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch2
      · rw [colSum_3]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch3
      · rw [colSum_4]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch4
      · rw [colSum_5]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch5
      · rw [colSum_6]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch6
      · rw [colSum_7]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch7
      · rw [colSum_8]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch8
      · rw [colSum_9]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch9
      · rw [colSum_10]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch10
      · rw [colSum_11]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch11
      · rw [colSum_12]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch12
      · rw [colSum_13]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch13
      · rw [colSum_14]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch14
      · rw [colSum_15]
        simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map,
          Vector.getElem_mapRange]
        linear_combination hch15
    · intro k hk
      interval_cases k <;>
        simp only [productVal, Nat.reduceLT, dif_pos] <;>
        first | exact pb0 | exact pb1 | exact pb2 | exact pb3 | exact pb4 | exact pb5 | exact pb6 | exact pb7 | exact pb8 | exact pb9 | exact pb10 | exact pb11 | exact pb12 | exact pb13 | exact pb14 | exact pb15
    · intro k hk
      interval_cases k <;>
        simp only [carryVal, Nat.reduceLT, dif_pos] <;>
        first | exact cb0 | exact cb1 | exact cb2 | exact cb3 | exact cb4 | exact cb5 | exact cb6 | exact cb7 | exact cb8 | exact cb9 | exact cb10 | exact cb11 | exact cb12 | exact cb13 | exact cb14 | exact cb15
    · exact hsdb
    · exact hsdc
    · exact bool_of_mul_pred (by simpa only [sub_eq_add_neg] using hb_bool)
    · exact bool_of_mul_pred (by simpa only [sub_eq_add_neg] using hc_bool)
    · show input_cols_b_sign_extend = 0 ∨ input_cols_b_sign_extend = 1
      have hims : input_is_mulh + input_is_mulhsu = 0 ∨ input_is_mulh + input_is_mulhsu = 1 := by
        rcases hmh_b with h | h
        · rcases hmhsu_b with h2 | h2 <;> rw [h, h2] <;> simp
        · have hs1 := sum_eq_one hmul_b (Or.inr h) hmhu_b hmhsu_b hmw_b hsum (Or.inr (Or.inl h))
          have hs' : input_is_mulh + input_is_mul + input_is_mulhu + input_is_mulhsu + input_is_mulw = 1 := by
            linear_combination hs1
          obtain ⟨_, _, h2, _⟩ := rest_zero hmul_b hmhu_b hmhsu_b hmw_b h hs'
          rw [h, h2]; simp
      rw [hsdb]; rcases hims with h | h <;> rw [h]
      · left; ring
      · rw [one_mul, hb_msb]; split <;> simp
    · show input_cols_c_sign_extend = 0 ∨ input_cols_c_sign_extend = 1
      rw [hsdc]; rcases hmh_b with h | h <;> rw [h]
      · left; ring
      · rw [one_mul, hc_msb]; split <;> simp
  · -- The 26 direct byte pulls' off-gate requirements (2 op5 MSB + 16 carry + 8 product range)
    -- are all vacuous under the binary `is_real` gate.  The three composed gadgets now expose their
    -- byte channel through canonical Clean metadata, so their interactions do not reappear here.
    exact ⟨fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0,
        fun h1 h0 => off_gate_vacuous hir_bin h1 h0, fun h1 h0 => off_gate_vacuous hir_bin h1 h0⟩

/-- Byte-value bridge: the `k`-th byte of the `ZMod`-level sign/zero-extended operand equals the `ℕ`
byte stream `extStream` at `k` (used by the witnessed `schoolProduct`/`schoolCarry`). Bytes `0..7` are
the `U16toU8` decomposition (low byte / high byte of each limb); bytes `8..15` are the sign fill
`s * 255` (a genuine byte since `s ∈ {0,1}`). -/
lemma byteAt_extendedBytes_val (w : Word (ZMod p)) (lower : Extracted.U16toU8Operation (ZMod p))
    (s : ZMod p) (hspec : U16toU8OperationSafe.DecompSpec w lower) (hs : s.val ≤ 1) (i : ℕ) :
    (byteAt (extendedBytes w lower s) i).val
      = extStream w[0].val w[1].val w[2].val w[3].val s.val i := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp : 2 ^ 24 < p := Fact.out
  have hsign : (s * 255).val = s.val * 255 := by
    have h255 : (s * 255 : ZMod p) = ((s.val * 255 : ℕ) : ZMod p) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    rw [h255, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hlo0, hhi0, hre0⟩ := hspec 0
  obtain ⟨hlo1, hhi1, hre1⟩ := hspec 1
  obtain ⟨hlo2, hhi2, hre2⟩ := hspec 2
  obtain ⟨hlo3, hhi3, hre3⟩ := hspec 3
  have c0 : w[0].val = (lower.low_bytes[0]).val + ((w[0] - lower.low_bytes[0]) * 256⁻¹).val * 256 :=
    byte_compose_val hlo0 hhi0 hre0
  have c1 : w[1].val = (lower.low_bytes[1]).val + ((w[1] - lower.low_bytes[1]) * 256⁻¹).val * 256 :=
    byte_compose_val hlo1 hhi1 hre1
  have c2 : w[2].val = (lower.low_bytes[2]).val + ((w[2] - lower.low_bytes[2]) * 256⁻¹).val * 256 :=
    byte_compose_val hlo2 hhi2 hre2
  have c3 : w[3].val = (lower.low_bytes[3]).val + ((w[3] - lower.low_bytes[3]) * 256⁻¹).val * 256 :=
    byte_compose_val hlo3 hhi3 hre3
  have hlo0' : (lower.low_bytes[0]).val < 256 := hlo0
  have hlo1' : (lower.low_bytes[1]).val < 256 := hlo1
  have hlo2' : (lower.low_bytes[2]).val < 256 := hlo2
  have hlo3' : (lower.low_bytes[3]).val < 256 := hlo3
  have hhi0' : ((w[0] - lower.low_bytes[0]) * 256⁻¹).val < 256 := hhi0
  have hhi1' : ((w[1] - lower.low_bytes[1]) * 256⁻¹).val < 256 := hhi1
  have hhi2' : ((w[2] - lower.low_bytes[2]) * 256⁻¹).val < 256 := hhi2
  have hhi3' : ((w[3] - lower.low_bytes[3]) * 256⁻¹).val < 256 := hhi3
  by_cases hi16 : i < 16
  · interval_cases i
    · show (lower.low_bytes[0]).val = w[0].val % 256; omega
    · show ((w[0] - lower.low_bytes[0]) * 256⁻¹).val = w[0].val / 256; omega
    · show (lower.low_bytes[1]).val = w[1].val % 256; omega
    · show ((w[1] - lower.low_bytes[1]) * 256⁻¹).val = w[1].val / 256; omega
    · show (lower.low_bytes[2]).val = w[2].val % 256; omega
    · show ((w[2] - lower.low_bytes[2]) * 256⁻¹).val = w[2].val / 256; omega
    · show (lower.low_bytes[3]).val = w[3].val % 256; omega
    · show ((w[3] - lower.low_bytes[3]) * 256⁻¹).val = w[3].val / 256; omega
    all_goals exact hsign
  · rw [byteAt, dif_neg hi16, ZMod.val_zero, extStream,
      List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]

/-- The `ZMod`-level schoolbook column `colSum` over the sign/zero-extended bytes equals the cast of the
`ℕ`-level byte convolution `cpNat` over the matching `extStream`s (for `k < 16`). This is the bridge
from the in-circuit gate (phrased via `colSum`) to the witnessed `schoolProduct`/`schoolCarry` (built
from `cpNat`). -/
lemma colSum_eq_cpNat (w w' : Word (ZMod p)) (lower lower' : Extracted.U16toU8Operation (ZMod p))
    (s s' : ZMod p) (hspec : U16toU8OperationSafe.DecompSpec w lower)
    (hspec' : U16toU8OperationSafe.DecompSpec w' lower') (hs : s = 0 ∨ s = 1) (hs' : s' = 0 ∨ s' = 1)
    (k : ℕ) (hk : k < 16) :
    colSum (extendedBytes w lower s) (extendedBytes w' lower' s') k
      = ((MulCarryChain.cpNat (extStream w[0].val w[1].val w[2].val w[3].val s.val)
            (extStream w'[0].val w'[1].val w'[2].val w'[3].val s'.val) k : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hsv : s.val ≤ 1 := by rcases hs with h | h <;> simp [h, ZMod.val_one, ZMod.val_zero]
  have hsv' : s'.val ≤ 1 := by rcases hs' with h | h <;> simp [h, ZMod.val_one, ZMod.val_zero]
  have hbb_lt := extendedBytes_byte_lt w lower s (fun i => (hspec i).1) (fun i => (hspec i).2.1) hs
  have hcc_lt := extendedBytes_byte_lt w' lower' s' (fun i => (hspec' i).1) (fun i => (hspec' i).2.1) hs'
  have key := byteAt_extendedBytes_val w lower s hspec hsv
  have key' := byteAt_extendedBytes_val w' lower' s' hspec' hsv'
  have hval : (colSum (extendedBytes w lower s) (extendedBytes w' lower' s') k).val
      = MulCarryChain.cpNat (extStream w[0].val w[1].val w[2].val w[3].val s.val)
          (extStream w'[0].val w'[1].val w'[2].val w'[3].val s'.val) k := by
    rw [colSum_val _ _ hbb_lt hcc_lt k]
    simp only [key, key']
    rw [MulCarryChain.cpNat, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [← ZMod.natCast_zmod_val (colSum (extendedBytes w lower s) (extendedBytes w' lower' s') k), hval]

/-- Each `extStream` byte is `≤ 255` (low/high bytes of `< 2^16` limbs; sign fill `sgn * 255` with
`sgn ≤ 1`). -/
lemma extStream_le (l0 l1 l2 l3 sgn : ℕ) (hl0 : l0 < 2 ^ 16) (hl1 : l1 < 2 ^ 16) (hl2 : l2 < 2 ^ 16)
    (hl3 : l3 < 2 ^ 16) (hsgn : sgn ≤ 1) (i : ℕ) : extStream l0 l1 l2 l3 sgn i ≤ 255 := by
  unfold extStream
  rcases Nat.lt_or_ge i 16 with h | h
  · interval_cases i <;> simp <;> omega
  · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

/-- `extStream` vanishes past index `15` (its backing list has length `16`). -/
lemma extStream_eq_zero (l0 l1 l2 l3 sgn i : ℕ) (h : 16 ≤ i) :
    extStream l0 l1 l2 l3 sgn i = 0 := by
  unfold extStream; rw [List.getD_eq_default _ _ (by simp; omega)]

set_option maxHeartbeats 4000000 in
/-- `populate b c is_mulh is_mulhsu is_mulw` satisfies the structural `Spec` for any `is_real` and any
boolean variant flags with a `{0,1}`-bounded sum (mirroring `Assumptions`). The composing chip uses
this to discharge its `MulOperation` assertion obligation in completeness. -/
theorem spec_populate {b c : Word (ZMod p)} (hb : b.isU64) (hc : c.isU64)
    (is_mul is_mulh is_mulhu is_mulhsu is_mulw is_real : ZMod p)
    (hmul : is_mul = 0 ∨ is_mul = 1) (hmh : is_mulh = 0 ∨ is_mulh = 1)
    (hmhu : is_mulhu = 0 ∨ is_mulhu = 1) (hmhsu : is_mulhsu = 0 ∨ is_mulhsu = 1)
    (hmw : is_mulw = 0 ∨ is_mulw = 1)
    (hsum : is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 0 ∨
            is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1) :
    Spec (⟨b, c, populate b c is_mulh is_mulhsu is_mulw,
      is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  have hp : 2 ^ 24 < p := Fact.out
  have hp_lit : 16777216 < p := by
    have e : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    omega
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hc
  -- `is_mulh + is_mulhsu` is boolean (`hsum` excludes both signed flags set at once).
  have hims : is_mulh + is_mulhsu = 0 ∨ is_mulh + is_mulhsu = 1 := by
    rcases hmh with h | h
    · rcases hmhsu with h2 | h2 <;> rw [h, h2] <;> simp
    · have hs1 := sum_eq_one hmul (Or.inr h) hmhu hmhsu hmw hsum (Or.inr (Or.inl h))
      have hs' : is_mulh + is_mul + is_mulhu + is_mulhsu + is_mulw = 1 := by
        linear_combination hs1
      obtain ⟨_, _, h2, _⟩ := rest_zero hmul hmhu hmhsu hmw h hs'
      rw [h, h2]; simp
  -- the two MSB witnesses are boolean
  have hmsb_b := U16MSBOperation.populate_msb_bool (p := p) hbU3
  have hmsb_c := U16MSBOperation.populate_msb_bool (p := p) hcU3
  -- the two sign-extend selectors are boolean
  have hbs_bool : (is_mulh + is_mulhsu) * U16MSBOperation.populate_msb b[3] = 0 ∨
      (is_mulh + is_mulhsu) * U16MSBOperation.populate_msb b[3] = 1 := by
    rcases hims with h | h
    · rw [h, zero_mul]; exact Or.inl rfl
    · rw [h, one_mul]; exact hmsb_b
  have hcs_bool : is_mulh * U16MSBOperation.populate_msb c[3] = 0 ∨
      is_mulh * U16MSBOperation.populate_msb c[3] = 1 := by
    rcases hmh with h | h
    · rw [h, zero_mul]; exact Or.inl rfl
    · rw [h, one_mul]; exact hmsb_c
  -- field↔ℕ sign-fill correspondence: the `ZMod` sign-extend selector's value is the `ℕ`-level
  -- `bsgn`/`csgn` that the witnessed `schoolProduct`/`schoolCarry` consume.
  have hbsv : ((is_mulh + is_mulhsu) * U16MSBOperation.populate_msb b[3]).val
      = (is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2) := by
    rcases hmh with h1 | h1 <;> rcases hmhsu with h2 | h2
    · rw [h1, h2]; simp
    · rw [h1, h2, zero_add, one_mul, ZMod.val_zero, ZMod.val_one,
        U16MSBOperation.populate_msb, ZMod.val_natCast_of_lt (by omega)]
      omega
    · rw [h1, h2, add_zero, one_mul, ZMod.val_one, ZMod.val_zero,
        U16MSBOperation.populate_msb, ZMod.val_natCast_of_lt (by omega)]
      omega
    · exfalso
      rw [h1, h2] at hims
      have h2cast : (1 : ZMod p) + 1 = ((2 : ℕ) : ZMod p) := by norm_num
      rw [h2cast] at hims
      have hv2 : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
      rcases hims with h | h
      · have := congrArg ZMod.val h; rw [hv2, ZMod.val_zero] at this; omega
      · have := congrArg ZMod.val h; rw [hv2, ZMod.val_one] at this; omega
  have hcsv : (is_mulh * U16MSBOperation.populate_msb c[3]).val
      = is_mulh.val * (c[3].val / 32768 % 2) := by
    rcases hmh with h1 | h1
    · rw [h1]; simp
    · rw [h1, one_mul, ZMod.val_one, one_mul,
        U16MSBOperation.populate_msb, ZMod.val_natCast_of_lt (by omega)]
      omega
  -- the witnessed `U16toU8` decompositions
  have hbdec : U16toU8OperationSafe.DecompSpec b (U16toU8OperationSafe.populate b) :=
    U16toU8OperationSafe.spec_populate hbU0 hbU1 hbU2 hbU3 1 rfl
  have hcdec : U16toU8OperationSafe.DecompSpec c (U16toU8OperationSafe.populate c) :=
    U16toU8OperationSafe.spec_populate hcU0 hcU1 hcU2 hcU3 1 rfl
  -- byte-stream bounds: each `extStream` entry is a byte and vanishes past index 15, so the
  -- convolution meets `cpBound` at every limb.
  have hbsgn_le : (is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2) ≤ 1 := by
    rw [← hbsv]
    rcases hbs_bool with h | h <;> rw [h]
    · simp
    · rw [ZMod.val_one]
  have hcsgn_le : is_mulh.val * (c[3].val / 32768 % 2) ≤ 1 := by
    rw [← hcsv]
    rcases hcs_bool with h | h <;> rw [h]
    · simp
    · rw [ZMod.val_one]
  have hbS_le : ∀ i, extStream b[0].val b[1].val b[2].val b[3].val
      ((is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)) i ≤ 255 :=
    extStream_le _ _ _ _ _ hbU0 hbU1 hbU2 hbU3 hbsgn_le
  have hcS_le : ∀ i, extStream c[0].val c[1].val c[2].val c[3].val
      (is_mulh.val * (c[3].val / 32768 % 2)) i ≤ 255 :=
    extStream_le _ _ _ _ _ hcU0 hcU1 hcU2 hcU3 hcsgn_le
  have hcp_le : ∀ k, MulCarryChain.cpNat
      (extStream b[0].val b[1].val b[2].val b[3].val
        ((is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)))
      (extStream c[0].val c[1].val c[2].val c[3].val
        (is_mulh.val * (c[3].val / 32768 % 2))) k ≤ MulCarryChain.cpBound :=
    MulCarryChain.cpNat_le_cpBound_total _ _ hbS_le hcS_le
      (fun i hi => extStream_eq_zero _ _ _ _ _ i hi)
  -- pin the witnessed product/carry columns to the abstract carry chain
  have hprodv : ∀ (k : ℕ), k < 16 → productVal (populate b c is_mulh is_mulhsu is_mulw) k
      = ((MulCarryChain.product (MulCarryChain.cpNat
            (extStream b[0].val b[1].val b[2].val b[3].val
              ((is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)))
            (extStream c[0].val c[1].val c[2].val c[3].val
              (is_mulh.val * (c[3].val / 32768 % 2)))) k : ℕ) : ZMod p) := by
    intro k hk
    simp only [productVal, dif_pos hk, populate, Vector.getElem_ofFn, schoolProduct]
  have hcarryv : ∀ (k : ℕ), k < 16 → carryVal (populate b c is_mulh is_mulhsu is_mulw) k
      = ((MulCarryChain.carry (MulCarryChain.cpNat
            (extStream b[0].val b[1].val b[2].val b[3].val
              ((is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)))
            (extStream c[0].val c[1].val c[2].val c[3].val
              (is_mulh.val * (c[3].val / 32768 % 2)))) k : ℕ) : ZMod p) := by
    intro k hk
    simp only [carryVal, dif_pos hk, populate, Vector.getElem_ofFn, schoolCarry]
  -- ranges
  have hprod_lt : ∀ k : ℕ, k < 16 →
      (productVal (populate b c is_mulh is_mulhsu is_mulw) k).val < 256 := by
    intro k hk
    rw [hprodv k hk, MulCarryChain.product_val _ (by omega) k]
    exact MulCarryChain.product_lt _ k
  have hcarry_lt : ∀ k : ℕ, k < 16 →
      (carryVal (populate b c is_mulh is_mulhsu is_mulw) k).val < 2 ^ 16 := by
    intro k hk
    rw [hcarryv k hk, MulCarryChain.carry_val _ hcp_le (by omega) k]
    have := MulCarryChain.carry_lt _ hcp_le k
    omega
  -- the schoolbook column over the witnessed byte decomposition is the cast `ℕ` convolution
  have hcolsum : ∀ (k : ℕ), k < 16 →
      colSum (extendedBytes b (U16toU8OperationSafe.populate b)
            ((is_mulh + is_mulhsu) * U16MSBOperation.populate_msb b[3]))
          (extendedBytes c (U16toU8OperationSafe.populate c)
            (is_mulh * U16MSBOperation.populate_msb c[3])) k
        = ((MulCarryChain.cpNat
            (extStream b[0].val b[1].val b[2].val b[3].val
              ((is_mulh.val + is_mulhsu.val) * (b[3].val / 32768 % 2)))
            (extStream c[0].val c[1].val c[2].val c[3].val
              (is_mulh.val * (c[3].val / 32768 % 2))) k : ℕ) : ZMod p) := by
    intro k hk
    rw [colSum_eq_cpNat b c _ _ _ _ hbdec hcdec hbs_bool hcs_bool k hk, hbsv, hcsv]
  -- the carry-chain gate equations
  have hchain : ∀ (k : ℕ), k < 16 →
      productVal (populate b c is_mulh is_mulhsu is_mulw) k
        = colSum (extendedBytes b (U16toU8OperationSafe.populate b)
              ((is_mulh + is_mulhsu) * U16MSBOperation.populate_msb b[3]))
            (extendedBytes c (U16toU8OperationSafe.populate c)
              (is_mulh * U16MSBOperation.populate_msb c[3])) k
          + (if k = 0 then 0 else carryVal (populate b c is_mulh is_mulhsu is_mulw) (k - 1))
          - carryVal (populate b c is_mulh is_mulhsu is_mulw) k * 256 := by
    intro k hk
    rw [hprodv k hk, hcolsum k hk]
    rcases k with _ | k'
    · rw [hcarryv 0 hk, if_pos rfl, add_zero]
      exact MulCarryChain.gate_zero _
    · have hk' : k' < 16 := by omega
      rw [hcarryv (k' + 1) hk, if_neg (Nat.succ_ne_zero k'), Nat.add_sub_cancel, hcarryv k' hk']
      exact MulCarryChain.gate_succ _ k'
  -- `product_msb`: boolean unconditionally, and the limb-MSB form under `is_mulw = 1`
  have hpm_msb_eq : (populate b c is_mulh is_mulhsu is_mulw).product_msb.msb
      = if is_mulw = 1 then U16MSBOperation.populate_msb
          ((populate b c is_mulh is_mulhsu is_mulw).product[2]
            + (populate b c is_mulh is_mulhsu is_mulw).product[3] * 256)
        else 0 := rfl
  have hpm_arg_lt : ((populate b c is_mulh is_mulhsu is_mulw).product[2]
      + (populate b c is_mulh is_mulhsu is_mulw).product[3] * 256).val < 2 ^ 16 := by
    have h2 := hprod_lt 2 (by norm_num)
    have h3 := hprod_lt 3 (by norm_num)
    have e2 : productVal (populate b c is_mulh is_mulhsu is_mulw) 2
        = (populate b c is_mulh is_mulhsu is_mulw).product[2] := dif_pos (by norm_num)
    have e3 : productVal (populate b c is_mulh is_mulhsu is_mulw) 3
        = (populate b c is_mulh is_mulhsu is_mulw).product[3] := dif_pos (by norm_num)
    rw [e2] at h2; rw [e3] at h3
    rw [byte_compose_val h2 h3 rfl]
    omega
  have hpm_bool : (populate b c is_mulh is_mulhsu is_mulw).product_msb.msb = 0 ∨
      (populate b c is_mulh is_mulhsu is_mulw).product_msb.msb = 1 := by
    rw [hpm_msb_eq]
    split_ifs with hw
    · exact U16MSBOperation.populate_msb_bool hpm_arg_lt
    · exact Or.inl rfl
  -- assemble the `Spec`
  refine ⟨rfl, rfl, hmsb_b, hmsb_c, hpm_bool, fun _ =>
    ⟨⟨hchain, hprod_lt, hcarry_lt, rfl, rfl, hmsb_b, hmsb_c, hbs_bool, hcs_bool⟩,
     hbdec, hcdec,
     (U16MSBOperation.spec_populate hbU3 1).2 rfl,
     (U16MSBOperation.spec_populate hcU3 1).2 rfl,
     hpm_bool, fun hw => ?_⟩⟩
  show (if is_mulw = 1 then U16MSBOperation.populate_msb
          ((populate b c is_mulh is_mulhsu is_mulw).product[2]
            + (populate b c is_mulh is_mulhsu is_mulw).product[3] * 256)
        else 0)
      = if ((populate b c is_mulh is_mulhsu is_mulw).product[2]
            + (populate b c is_mulh is_mulhsu is_mulw).product[3] * 256).val ≥ 32768 then 1 else 0
  rw [if_pos hw]
  exact (U16MSBOperation.spec_populate hpm_arg_lt 1).2 rfl

-- 40M: completeness re-runs the same 45-column carry-chain normalization as soundness above,
-- with the `populate` witness closure substituted cell-by-cell.
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hir_bin, hmw_real, hmul_b, hmh_b, hmhu_b, hmhsu_b, hmw_b, hsum⟩ := h_assumptions
  obtain ⟨hib, hic, hicols, _hir, _him_mul, _him_mulh, _him_mulhu, _him_mulhsu, _him_mulw⟩ := h_input
  obtain ⟨h_bsd, h_csd, h_bmb, h_cmb, h_pmb, h_gated⟩ := h_spec
  obtain ⟨ecar_eq, eprod_eq, ebl_eq, ecl_eq, _ebm, _ecm, _epm, _ebse, _ecse⟩ := hicols
  have h16p : (16 : ℕ) < p := by
    have h := Fact.out (p := 2 ^ 24 < p); have e : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    omega
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by rw [← hib, Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by rw [← hib, Vector.getElem_map]
  have eb2 : Expression.eval env.toEnvironment input_var_b[2] = input_b[2] := by rw [← hib, Vector.getElem_map]
  have eb3 : Expression.eval env.toEnvironment input_var_b[3] = input_b[3] := by rw [← hib, Vector.getElem_map]
  have ec0 : Expression.eval env.toEnvironment input_var_c[0] = input_c[0] := by rw [← hic, Vector.getElem_map]
  have ec1 : Expression.eval env.toEnvironment input_var_c[1] = input_c[1] := by rw [← hic, Vector.getElem_map]
  have ec2 : Expression.eval env.toEnvironment input_var_c[2] = input_c[2] := by rw [← hic, Vector.getElem_map]
  have ec3 : Expression.eval env.toEnvironment input_var_c[3] = input_c[3] := by rw [← hic, Vector.getElem_map]
  have ep0 : Expression.eval env.toEnvironment input_var_cols_product[0] = input_cols_product[0] := by rw [← eprod_eq, Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_cols_product[1] = input_cols_product[1] := by rw [← eprod_eq, Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_cols_product[2] = input_cols_product[2] := by rw [← eprod_eq, Vector.getElem_map]
  have ep3 : Expression.eval env.toEnvironment input_var_cols_product[3] = input_cols_product[3] := by rw [← eprod_eq, Vector.getElem_map]
  have ep4 : Expression.eval env.toEnvironment input_var_cols_product[4] = input_cols_product[4] := by rw [← eprod_eq, Vector.getElem_map]
  have ep5 : Expression.eval env.toEnvironment input_var_cols_product[5] = input_cols_product[5] := by rw [← eprod_eq, Vector.getElem_map]
  have ep6 : Expression.eval env.toEnvironment input_var_cols_product[6] = input_cols_product[6] := by rw [← eprod_eq, Vector.getElem_map]
  have ep7 : Expression.eval env.toEnvironment input_var_cols_product[7] = input_cols_product[7] := by rw [← eprod_eq, Vector.getElem_map]
  have ep8 : Expression.eval env.toEnvironment input_var_cols_product[8] = input_cols_product[8] := by rw [← eprod_eq, Vector.getElem_map]
  have ep9 : Expression.eval env.toEnvironment input_var_cols_product[9] = input_cols_product[9] := by rw [← eprod_eq, Vector.getElem_map]
  have ep10 : Expression.eval env.toEnvironment input_var_cols_product[10] = input_cols_product[10] := by rw [← eprod_eq, Vector.getElem_map]
  have ep11 : Expression.eval env.toEnvironment input_var_cols_product[11] = input_cols_product[11] := by rw [← eprod_eq, Vector.getElem_map]
  have ep12 : Expression.eval env.toEnvironment input_var_cols_product[12] = input_cols_product[12] := by rw [← eprod_eq, Vector.getElem_map]
  have ep13 : Expression.eval env.toEnvironment input_var_cols_product[13] = input_cols_product[13] := by rw [← eprod_eq, Vector.getElem_map]
  have ep14 : Expression.eval env.toEnvironment input_var_cols_product[14] = input_cols_product[14] := by rw [← eprod_eq, Vector.getElem_map]
  have ep15 : Expression.eval env.toEnvironment input_var_cols_product[15] = input_cols_product[15] := by rw [← eprod_eq, Vector.getElem_map]
  have ecar0 : Expression.eval env.toEnvironment input_var_cols_carry[0] = input_cols_carry[0] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar1 : Expression.eval env.toEnvironment input_var_cols_carry[1] = input_cols_carry[1] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar2 : Expression.eval env.toEnvironment input_var_cols_carry[2] = input_cols_carry[2] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar3 : Expression.eval env.toEnvironment input_var_cols_carry[3] = input_cols_carry[3] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar4 : Expression.eval env.toEnvironment input_var_cols_carry[4] = input_cols_carry[4] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar5 : Expression.eval env.toEnvironment input_var_cols_carry[5] = input_cols_carry[5] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar6 : Expression.eval env.toEnvironment input_var_cols_carry[6] = input_cols_carry[6] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar7 : Expression.eval env.toEnvironment input_var_cols_carry[7] = input_cols_carry[7] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar8 : Expression.eval env.toEnvironment input_var_cols_carry[8] = input_cols_carry[8] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar9 : Expression.eval env.toEnvironment input_var_cols_carry[9] = input_cols_carry[9] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar10 : Expression.eval env.toEnvironment input_var_cols_carry[10] = input_cols_carry[10] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar11 : Expression.eval env.toEnvironment input_var_cols_carry[11] = input_cols_carry[11] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar12 : Expression.eval env.toEnvironment input_var_cols_carry[12] = input_cols_carry[12] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar13 : Expression.eval env.toEnvironment input_var_cols_carry[13] = input_cols_carry[13] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar14 : Expression.eval env.toEnvironment input_var_cols_carry[14] = input_cols_carry[14] := by rw [← ecar_eq, Vector.getElem_map]
  have ecar15 : Expression.eval env.toEnvironment input_var_cols_carry[15] = input_cols_carry[15] := by rw [← ecar_eq, Vector.getElem_map]
  have ebl0 : Expression.eval env.toEnvironment input_var_cols_b_lower_byte_low_bytes[0] = input_cols_b_lower_byte_low_bytes[0] := by rw [← ebl_eq, Vector.getElem_map]
  have ebl1 : Expression.eval env.toEnvironment input_var_cols_b_lower_byte_low_bytes[1] = input_cols_b_lower_byte_low_bytes[1] := by rw [← ebl_eq, Vector.getElem_map]
  have ebl2 : Expression.eval env.toEnvironment input_var_cols_b_lower_byte_low_bytes[2] = input_cols_b_lower_byte_low_bytes[2] := by rw [← ebl_eq, Vector.getElem_map]
  have ebl3 : Expression.eval env.toEnvironment input_var_cols_b_lower_byte_low_bytes[3] = input_cols_b_lower_byte_low_bytes[3] := by rw [← ebl_eq, Vector.getElem_map]
  have ecl0 : Expression.eval env.toEnvironment input_var_cols_c_lower_byte_low_bytes[0] = input_cols_c_lower_byte_low_bytes[0] := by rw [← ecl_eq, Vector.getElem_map]
  have ecl1 : Expression.eval env.toEnvironment input_var_cols_c_lower_byte_low_bytes[1] = input_cols_c_lower_byte_low_bytes[1] := by rw [← ecl_eq, Vector.getElem_map]
  have ecl2 : Expression.eval env.toEnvironment input_var_cols_c_lower_byte_low_bytes[2] = input_cols_c_lower_byte_low_bytes[2] := by rw [← ecl_eq, Vector.getElem_map]
  have ecl3 : Expression.eval env.toEnvironment input_var_cols_c_lower_byte_low_bytes[3] = input_cols_c_lower_byte_low_bytes[3] := by rw [← ecl_eq, Vector.getElem_map]
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3, ep0, ep1, ep2, ep3, ep4, ep5, ep6, ep7, ep8, ep9,
    ep10, ep11, ep12, ep13, ep14, ep15, ecar0, ecar1, ecar2, ecar3, ecar4, ecar5, ecar6, ecar7, ecar8,
    ecar9, ecar10, ecar11, ecar12, ecar13, ecar14, ecar15, ebl0, ebl1, ebl2, ebl3, ecl0, ecl1, ecl2,
    ecl3] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  -- leading `is_real` binary gate (W11 cwr: byte sends are locally `is_real`-gated, shallow `assertZero`)
  · rcases hir_bin with h | h <;> simp [h]
  -- 3 subcircuit `⟨Assumptions, Spec⟩`: U16toU8(b), U16toU8(c), U16MSB(product)
  · exact ⟨hir_bin, fun h => (h_gated h).2.1⟩
  · exact ⟨hir_bin, fun h => (h_gated h).2.2.1⟩
  · refine ⟨⟨fun hmw => ?_, hmw_b⟩, ⟨h_pmb, fun hmw => (h_gated (hmw_real hmw)).2.2.2.2.2.2 hmw⟩⟩
    have hr1 : input_is_real = 1 := hmw_real hmw
    have pb2 : input_cols_product[2].val < 2 ^ 8 := (h_gated hr1).1.2.1 2 (by norm_num)
    have pb3 : input_cols_product[3].val < 2 ^ 8 := (h_gated hr1).1.2.1 3 (by norm_num)
    rw [byte_compose_val pb2 pb3 rfl]; omega
  -- 2 ungated `b_msb`/`c_msb` booleanity asserts (from the Spec's ungated bool)
  · rcases h_bmb with h | h <;> rw [h] <;> ring
  · rcases h_cmb with h | h <;> rw [h] <;> ring
  -- 2 op5 `MSB` byte sends: provide the `MSB` byte-row guarantee on a real row
  · refine fun hneg => ?_
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hlo3, hhi3, hreass3⟩ := (h_gated hr1).2.1 3
    dsimp only at hlo3 hhi3 hreass3
    obtain ⟨hbool, hiff⟩ := op5_iff_of_msb_eq hlo3 hhi3 hreass3 (h_gated hr1).2.2.2.1
    have hmlt : input_cols_b_msb.val < 256 := by
      rcases hbool with h | h <;> rw [h] <;> (first | rw [ZMod.val_zero] | rw [ZMod.val_one]) <;> norm_num
    exact (byteRowSpec_msb _ _).mpr ⟨⟨hmlt, hhi3⟩, hbool, hiff⟩
  · refine fun hneg => ?_
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hlo3, hhi3, hreass3⟩ := (h_gated hr1).2.2.1 3
    dsimp only at hlo3 hhi3 hreass3
    obtain ⟨hbool, hiff⟩ := op5_iff_of_msb_eq hlo3 hhi3 hreass3 (h_gated hr1).2.2.2.2.1
    have hmlt : input_cols_c_msb.val < 256 := by
      rcases hbool with h | h <;> rw [h] <;> (first | rw [ZMod.val_zero] | rw [ZMod.val_one]) <;> norm_num
    exact (byteRowSpec_msb _ _).mpr ⟨⟨hmlt, hhi3⟩, hbool, hiff⟩
  -- 16 carry `slice_range_check_u16` byte pulls
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 0 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 1 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 2 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 3 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 4 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 5 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 6 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 7 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 8 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 9 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 10 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 11 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 12 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 13 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 14 (by norm_num))
  · exact fun hneg => (byteRowSpec_range _ h16p).mpr ((h_gated (neg_inj.mp hneg)).1.2.2.1 15 (by norm_num))
  -- 8 product `slice_range_check_u8` byte-pair pulls
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 0 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 1 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 2 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 3 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 4 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 5 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 6 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 7 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 8 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 9 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 10 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 11 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 12 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 13 (by norm_num)⟩
  · exact fun hneg => (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_gated (neg_inj.mp hneg)).1.2.1 14 (by norm_num), (h_gated (neg_inj.mp hneg)).1.2.1 15 (by norm_num)⟩
  -- 4 sign-extend asserts
  · exact h_bsd
  · exact h_csd
  · rw [h_bsd]; rcases h_bmb with h | h <;> rw [h] <;> simp
  · rw [h_csd]; rcases h_cmb with h | h <;> rw [h] <;> simp
  -- 16 `is_real`-gated schoolbook carry-chain product equations
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 0 (by norm_num)
      rw [colSum_0] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 1 (by norm_num)
      rw [colSum_1] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 2 (by norm_num)
      rw [colSum_2] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 3 (by norm_num)
      rw [colSum_3] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 4 (by norm_num)
      rw [colSum_4] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 5 (by norm_num)
      rw [colSum_5] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 6 (by norm_num)
      rw [colSum_6] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 7 (by norm_num)
      rw [colSum_7] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 8 (by norm_num)
      rw [colSum_8] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 9 (by norm_num)
      rw [colSum_9] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 10 (by norm_num)
      rw [colSum_10] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 11 (by norm_num)
      rw [colSum_11] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 12 (by norm_num)
      rw [colSum_12] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 13 (by norm_num)
      rw [colSum_13] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 14 (by norm_num)
      rw [colSum_14] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain
  · rcases hir_bin with h | h
    · simp [h]
    · have hchain := (h_gated h).1.1 15 (by norm_num)
      rw [colSum_15] at hchain
      simp [productVal, carryVal, byteAt, extendedBytes, Vector.getElem_map, Vector.getElem_mapRange] at hchain
      rw [h, one_mul]; linear_combination hchain

set_option linter.unusedSectionVars false in
/-- `Spec` holds at the all-zero column struct whenever the gate is off (`is_real = 0`) — the
inactive-row discharge for composing chips whose populate leaves the struct zero (`DivRemChip`'s
`c_times_quotient_upper` on word rows and padding rows). The variant flags are arbitrary. -/
theorem spec_zero (b c : Word (ZMod p)) (is_mul is_mulh is_mulhu is_mulhsu is_mulw : ZMod p)
    {is_real : ZMod p} (hr : is_real = 0) :
    Spec (⟨b, c, zeroCols, is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
      : Inputs (ZMod p)) :=
  ⟨(mul_zero _).symm, (mul_zero _).symm, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    fun h1 => absurd (hr.symm.trans h1) zero_ne_one⟩

/-- Semantic readout at the `populate`d columns on an active row: `spec_populate` +
`result_semantic` packaged for composing chips — the value-level bridge from the witnessed product
struct to the `BitVec` product slices (`DivRemChip`'s `c_times_quotient` glue). -/
theorem semantic_populate {b c : Word (ZMod p)} (hb : b.isU64) (hc : c.isU64)
    (is_mul is_mulh is_mulhu is_mulhsu is_mulw : ZMod p)
    (hmul : is_mul = 0 ∨ is_mul = 1) (hmh : is_mulh = 0 ∨ is_mulh = 1)
    (hmhu : is_mulhu = 0 ∨ is_mulhu = 1) (hmhsu : is_mulhsu = 0 ∨ is_mulhsu = 1)
    (hmw : is_mulw = 0 ∨ is_mulw = 1)
    (hsum : is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 0 ∨
            is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1) :
    SemanticSpec
      (⟨b, c, populate b c is_mulh is_mulhsu is_mulw, 1,
        is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩ : Inputs (ZMod p))
      (populate b c is_mulh is_mulhsu is_mulw) :=
  result_semantic
    ⟨Or.inr rfl, fun _ => rfl, hmul, hmh, hmhu, hmhsu, hmw, hsum⟩
    (spec_populate hb hc is_mul is_mulh is_mulhu is_mulhsu is_mulw 1
      hmul hmh hmhu hmhsu hmw hsum) rfl

private theorem main_requirementsChannelsLawful (input_var : Var Inputs (ZMod p)) (i₀ : ℕ) :
    ((main input_var).operations i₀).RequirementsChannelsLawful
      (elaborated (p := p)).channelsWithGuarantees [] := by
  have h_byte : (byteChannel (p := p)).toRaw ∈
      (elaborated (p := p)).channelsWithGuarantees := by
    simp only [circuit_norm]
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
    simp only [Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_assert,
      Operations.subcircuitChannelsWithRequirements_interact,
      Operations.subcircuitChannelsWithRequirements_nil,
      FormalAssertion.toSubcircuit_channelsWithRequirements,
      U16toU8OperationSafe.channelsWithRequirements_eq,
      U16MSBOperation.channelsWithRequirements_eq,
      Gadgets.Equality.channelsWithRequirements_eq, List.append_nil,
      List.nil_subset]
  · intro channel h_channel
    simp only [main, Circuit.operations, Circuit.bind_def, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength] at h_channel
    simp only [Operations.shallowChannels_append, Operations.shallowChannels_subcircuit,
      Operations.shallowChannels_assert, Operations.shallowChannels_interact,
      Operations.shallowChannels_nil, List.nil_append] at h_channel
    simp only [ChannelInteraction.toRaw_channel, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, or_self] at h_channel
    subst channel
    exact Or.inl h_byte
  · intro env h_constraints
    simp only [main, Circuit.operations, Circuit.bind_def, assertion, assertZero, Channel.pullIf,
      HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength] at h_constraints ⊢
    simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, and_true, eval_sub,
      Expression.eval] at h_constraints
    have h_bool : Expression.eval env input_var.is_real = 0 ∨
        Expression.eval env input_var.is_real = 1 :=
      bool_of_mul_pred (by simpa only [sub_eq_add_neg] using h_constraints)
    have h_bool' : (ProvableStruct.eval env input_var).is_real = 0 ∨
        (ProvableStruct.eval env input_var).is_real = 1 := by
      simpa only [circuit_norm] using h_bool
    have h_pull (msg : ByteRow (Expression (ZMod p))) :
        (byteChannel.pulledIf input_var.is_real msg).toRaw.Requirements env := by
      rw [ChannelInteraction.toRaw_requirements]
      intro h1 h0
      simp only [pulledIf_mult, circuit_norm] at h1 h0
      exact off_gate_vacuous h_bool' h1 h0
    simp only [Operations.InChannelsOrRequirements, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, List.not_mem_nil, false_or, true_and, and_true]
    and_intros
    all_goals exact h_pull _

/-- The internal multiply semantic gadget as a Clean `FormalAssertion`: `is_real`-gated
multiply-family constraints over the `populate`d product/carry columns; no fresh witnesses.
Its semantic lemmas are consumed by chip proofs; Rust faithfulness is asserted only at chip level. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := main_requirementsChannelsLawful }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.MulOperation
