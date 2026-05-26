import SP1Clean.Chips.ALU.AddwChip.Cols
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Clean.Operations.AddwOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Addw.Common
import RISCV.Instructions
import RISCV.ForLean

/-! # `AddwChip` cols-level lemmas

Three non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `addwOp_spec_iff_rv64_addw` — bidirectional bridge between
  `AddwOp.Spec ⟨b, c, value, msb⟩` (under operand `isU64` bounds) and
  the (a)-shape pair `(Word.isU64 (constructed) ∧ BV64 (constructed) =
  RV64.addw c.toBitVec64 b.toBitVec64)`. The constructed Word is
  `#v[value[0], value[1], msb*65535, msb*65535]`. Forward uses
  `AddwOperation.spec`; backward inverts the sign-extension via
  `BitVec.setWidth_signExtend_eq_self` and `Word.setWidth_eq_low`.
- `allHold_iff_structural` — bridges `(_root_.Addw.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `CPUState.Gated.Spec`,
  `ALUTypeReader.Gated.Spec`, the op_a_0 = 0 gate, plus the semantic
  pair `(isU64 op_a_write_value ∧ BV64 = RV64.addw c b)` derived from
  `AddwOperation.iff_sp1_full`'s RHS through `addwOp_spec_iff_rv64_addw`.
  Used downstream by `SailBridge.lean` to reconstruct
  `(Addw.constraints (toMain cols)).allHold` from the structural
  conjuncts of `FormalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : AddwCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addw_value, addw_msb, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, AddwCols.ext_iff, CPUState.ext_iff,
    ALUTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- Bridge the `AddwOperation.spec` 32-bit BitVec equation +
sign-extension MSB to the 64-bit `RV64.addw` semantic. Given the
natural-form `AddwOp.Spec` plus operand `Word.isU64` bounds, the
sign-extended Word `#v[value[0], value[1], msb*65535, msb*65535]`
equals `RV64.addw c.toBitVec64 b.toBitVec64`. Used by
`addwOp_spec_iff_rv64_addw` (forward) and downstream by
`Assertion.soundness` to discharge the ADDW BitVec conjunct of
`FormalSpec`. -/
lemma rv64_addw_eq_of_addwop_spec
    (b c : Word (ZMod p)) (value : HWord (ZMod p)) (msb : ZMod p)
    (h_isU64_b : b.isU64) (h_isU64_c : c.isU64)
    (h_addwop : SP1Clean.AddwOp.Spec ⟨b, c, value, msb⟩) :
    Word.toBitVec64 #v[value[0], value[1], msb * 65535, msb * 65535] =
      RV64.addw c.toBitVec64 b.toBitVec64 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_allHold : (AddwOperation.constraints b c
        { value := value, msb := { msb := msb } } 1).allHold :=
    (SP1Clean.AddwOp.iff_sp1 ⟨b, c, value, msb⟩).mp h_addwop
  obtain ⟨h_isU32_v, h_addw_bv, h_msb_eq⟩ :=
    AddwOperation.spec h_isU64_b h_isU64_c h_allHold
  simp only [RV64.addw]
  have h_b_low :
      BitVec.extractLsb' 0 32 b.toBitVec64 = b.low.toBitVec32 := by
    rw [show BitVec.extractLsb' 0 32 b.toBitVec64 =
          BitVec.setWidth 32 b.toBitVec64 from rfl]
    exact Word.setWidth_eq_low h_isU64_b
  have h_c_low :
      BitVec.extractLsb' 0 32 c.toBitVec64 = c.low.toBitVec32 := by
    rw [show BitVec.extractLsb' 0 32 c.toBitVec64 =
          BitVec.setWidth 32 c.toBitVec64 from rfl]
    exact Word.setWidth_eq_low h_isU64_c
  rw [h_b_low, h_c_low]
  -- `execute_RTYPEW_pure_32_w b c .ADDW = b.low + c.low` (definitionally).
  -- After `simp only [RV64.addw]` the goal uses `BitVec.add` instead of `HAdd.hAdd`.
  rw [show b.low.toBitVec32.add c.low.toBitVec32 = HWord.toBitVec32 value by
    rw [h_addw_bv]; rfl]
  simp only at h_msb_eq h_isU32_v
  rw [HWord.sign_extend_32_to_64_msb h_isU32_v]
  rw [h_msb_eq]
  by_cases h : (HWord.toBitVec32 value).msb = true
  · simp [h]
  · simp [h]

set_option debug.skipKernelTC true in
-- `skipKernelTC` bypasses kernel deep-recursion on the `BitVec.toNat` +
-- `BitVec.signExtend` literal-evaluation cascade that the backward
-- inversion chain forces. Forward direction uses
-- `rv64_addw_eq_of_addwop_spec` plus a derivation of `Word.isU64` of the
-- constructed Word from `isU32 value` (via `AddwOperation.spec`) and
-- `msb ∈ {0, 1}` (via the MSB equation). Backward inverts the
-- sign-extension via `BitVec.setWidth_signExtend_eq_self` +
-- `sign_extend_32_to_64_msb`.
/-- Bidirectional bridge between `AddwOp.Spec` (under operand `isU64`
bounds) and the (a)-shape pair `(Word.isU64 (constructed) ∧ BV64
(constructed) = RV64.addw c.toBitVec64 b.toBitVec64)`, where the
constructed Word is `#v[value[0], value[1], msb*65535, msb*65535]`. -/
lemma addwOp_spec_iff_rv64_addw
    {b c : Word (ZMod p)} {value : HWord (ZMod p)} {msb : ZMod p}
    (h_isU64_b : b.isU64) (h_isU64_c : c.isU64) :
    SP1Clean.AddwOp.Spec ⟨b, c, value, msb⟩ ↔
      (Word.isU64 #v[value[0], value[1], msb * 65535, msb * 65535] ∧
       Word.toBitVec64 #v[value[0], value[1], msb * 65535, msb * 65535] =
         RV64.addw c.toBitVec64 b.toBitVec64) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h65535_val : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_natCast_of_lt (by omega)]
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have h65535_ne_zero : (65535 : ZMod p) ≠ 0 := by
    intro h
    have : (65535 : ZMod p).val = (0 : ZMod p).val := by rw [h]
    rw [h65535_val, h0_val] at this
    omega
  refine ⟨?_, ?_⟩
  · -- Forward: AddwOp.Spec → (isU64 ∧ BV64 = RV64.addw)
    intro h_addwop
    have h_allHold : (AddwOperation.constraints b c
          { value := value, msb := { msb := msb } } 1).allHold :=
      (SP1Clean.AddwOp.iff_sp1 ⟨b, c, value, msb⟩).mp h_addwop
    obtain ⟨h_isU32_v, _h_addw_bv, h_msb_eq⟩ :=
      AddwOperation.spec h_isU64_b h_isU64_c h_allHold
    refine ⟨?_, rv64_addw_eq_of_addwop_spec _ _ _ _ h_isU64_b h_isU64_c h_addwop⟩
    -- Derive isU64 from isU32 value and msb ∈ {0,1}.
    have ⟨hv0, hv1⟩ := HWord.lt_cases_of_isU32 h_isU32_v
    simp only at h_msb_eq
    apply Word.isU64_of_cases
    · simpa using hv0
    · simpa using hv1
    · -- msb * 65535: split on the if in h_msb_eq.
      rw [h_msb_eq]
      split_ifs <;> simp [show ((1 : ZMod p) * 65535) = 65535 from by ring,
                          show ((0 : ZMod p) * 65535) = 0 from by ring,
                          h0_val, h65535_val]
    · rw [h_msb_eq]
      split_ifs <;> simp [show ((1 : ZMod p) * 65535) = 65535 from by ring,
                          show ((0 : ZMod p) * 65535) = 0 from by ring,
                          h0_val, h65535_val]
  · -- Backward: (isU64 ∧ BV64 = RV64.addw) → AddwOp.Spec.
    rintro ⟨h_isU64_v, h_bv64⟩
    -- Step 1: derive isU32 value from isU64 of the constructed Word.
    have ⟨hv0_lt, hv1_lt, _h2_lt, _h3_lt⟩ := Word.lt_cases_of_isU64 h_isU64_v
    have h_isU32_value : HWord.isU32 value :=
      HWord.isU32_of_cases (by simpa using hv0_lt) (by simpa using hv1_lt)
    have h_value_unfold : (#v[value[0], value[1]] : HWord (ZMod p)) = value := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> rfl
    -- Step 2: derive BV32 eq via `setWidth 32` of both sides.
    have h_b_low_extract :
        BitVec.extractLsb' 0 32 b.toBitVec64 = b.low.toBitVec32 := by
      rw [show BitVec.extractLsb' 0 32 b.toBitVec64 =
            BitVec.setWidth 32 b.toBitVec64 from rfl]
      exact Word.setWidth_eq_low h_isU64_b
    have h_c_low_extract :
        BitVec.extractLsb' 0 32 c.toBitVec64 = c.low.toBitVec32 := by
      rw [show BitVec.extractLsb' 0 32 c.toBitVec64 =
            BitVec.setWidth 32 c.toBitVec64 from rfl]
      exact Word.setWidth_eq_low h_isU64_c
    -- LHS setWidth 32 = Word.low of constructed Word's toBitVec32.
    -- `Word.low #v[value[0], value[1], _, _] = #v[value[0], value[1]] = value`.
    have h_setwidth_lhs :
        BitVec.setWidth 32
          (Word.toBitVec64 (#v[value[0], value[1], msb * 65535, msb * 65535]
            : Word (ZMod p))) =
        HWord.toBitVec32 value := by
      rw [Word.setWidth_eq_low h_isU64_v]
      -- `Word.low #v[value[0], value[1], msb*65535, msb*65535] = #v[value[0], value[1]]`
      -- by definition.
      change HWord.toBitVec32 (#v[value[0], value[1]] : HWord (ZMod p)) = _
      rw [h_value_unfold]
    -- Apply setWidth to h_bv64.
    have h_setwidth : HWord.toBitVec32 value =
        BitVec.setWidth 32 (RV64.addw c.toBitVec64 b.toBitVec64) := by
      rw [← h_setwidth_lhs, h_bv64]
    simp only [RV64.addw] at h_setwidth
    rw [h_b_low_extract, h_c_low_extract,
        BitVec.setWidth_signExtend_eq_self (show 32 ≤ 64 from by omega)] at h_setwidth
    -- `h_setwidth : HWord.toBitVec32 value = b.low.toBitVec32 + c.low.toBitVec32`.
    -- Translate to `execute_RTYPEW_pure_32_w b c .ADDW` form.
    have h_bv32 : HWord.toBitVec32 value = execute_RTYPEW_pure_32_w b c .ADDW := by
      simp only [execute_RTYPEW_pure_32_w]
      exact h_setwidth
    -- Step 3: derive msb_eq via sign_extend_32_to_64_msb + Word.toBitVec64 injectivity.
    have h_ext : BitVec.signExtend 64 (HWord.toBitVec32 value) =
        Word.toBitVec64 (#v[value[0], value[1],
          if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0,
          if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0]
          : Word (ZMod p)) :=
      HWord.sign_extend_32_to_64_msb h_isU32_value
    -- Express `RV64.addw c b` as `signExtend 64 (HWord.toBitVec32 value)`.
    have h_rhs : RV64.addw c.toBitVec64 b.toBitVec64 =
        BitVec.signExtend 64 (HWord.toBitVec32 value) := by
      simp only [RV64.addw]
      rw [h_b_low_extract, h_c_low_extract, ← h_setwidth]
    -- Chain: BV64(#v[..., msb*65535, msb*65535]) = RV64.addw c b
    --   = signExtend 64 (HWord.toBitVec32 value)
    --   = BV64(#v[value[0], value[1], if BV32_v.msb then 65535 else 0, ...]).
    have h_bv_eq : Word.toBitVec64 (#v[value[0], value[1], msb * 65535, msb * 65535]
        : Word (ZMod p)) =
        Word.toBitVec64 (#v[value[0], value[1],
          if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0,
          if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0]
          : Word (ZMod p)) := by
      rw [h_bv64, h_rhs, h_ext]
    -- Extract msb*65535 = (if ... then 65535 else 0) via toNat injectivity.
    have h_isU64_other : Word.isU64
        (#v[value[0], value[1],
            if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0,
            if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0]
          : Word (ZMod p)) := by
      apply Word.isU64_of_cases
      · simpa using hv0_lt
      · simpa using hv1_lt
      all_goals (split_ifs <;> simp [h65535_val, h0_val])
    have h_toNat := congrArg BitVec.toNat h_bv_eq
    rw [Word.toBitVec64_toNat h_isU64_v, Word.toBitVec64_toNat h_isU64_other] at h_toNat
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at h_toNat
    have ⟨_, _, hm2_lt, _⟩ := Word.lt_cases_of_isU64 h_isU64_v
    have hm2_lt' : (msb * 65535).val < 2 ^ 16 := by simpa using hm2_lt
    have h_branch_val :
        (if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0).val =
          if (HWord.toBitVec32 value).msb = true then 65535 else 0 := by
      split_ifs <;> simp [h65535_val, h0_val]
    rw [h_branch_val] at h_toNat
    have h_branch_lt :
        (if (HWord.toBitVec32 value).msb = true then (65535 : ℕ) else 0) < 2 ^ 16 := by
      split_ifs <;> omega
    have h_msb_mul_val_eq :
        (msb * 65535).val =
          if (HWord.toBitVec32 value).msb = true then 65535 else 0 := by
      omega
    -- Lift val-equality back to ZMod-equality.
    have h_field_eq : msb * 65535 =
        (if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0) := by
      have h1 : (msb * 65535).val = ((if (HWord.toBitVec32 value).msb = true
                    then (65535 : ZMod p) else 0).val) := by
        rw [h_branch_val]; exact h_msb_mul_val_eq
      -- ZMod_val_inj_of_lt: need both sides < p. Both < 2^16 < 2^17 < p.
      have h_lhs_lt : (msb * 65535).val < p := by
        have := hm2_lt'
        have : (2 : ℕ) ^ 16 < p := by have : 2 ^ 17 < p := hp; omega
        omega
      have h_rhs_lt :
          (if (HWord.toBitVec32 value).msb = true then (65535 : ZMod p) else 0).val < p := by
        rw [h_branch_val]
        have : (2 : ℕ) ^ 16 < p := by have : 2 ^ 17 < p := hp; omega
        have hb := h_branch_lt
        omega
      -- Apply ZMod.val_injective via ZMod.val_cast_of_lt is overkill; use
      -- the fact that `(ZMod.val x : ZMod p) = x` for x : ZMod p.
      have h_val_inj : ∀ (x y : ZMod p), x.val = y.val → x = y := fun x y h => by
        have hx : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
        have hy : ((y.val : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
        rw [← hx, ← hy, h]
      exact h_val_inj _ _ h1
    have h_msb_eq : msb = if (HWord.toBitVec32 value).msb then 1 else 0 := by
      by_cases h_mbit : (HWord.toBitVec32 value).msb = true
      · simp only [h_mbit, if_true] at h_field_eq
        simp only [h_mbit, if_true]
        have : (msb - 1) * 65535 = 0 := by linear_combination h_field_eq
        rcases mul_eq_zero.mp this with h | h
        · linear_combination h
        · exact absurd h h65535_ne_zero
      · simp only [h_mbit, Bool.false_eq_true, if_false] at h_field_eq
        simp only [h_mbit, Bool.false_eq_true, if_false]
        rcases mul_eq_zero.mp h_field_eq with h | h
        · exact h
        · exact absurd h h65535_ne_zero
    -- Step 4: assemble AddwOp.Spec via iff_sp1_full + iff_sp1.
    have h_allHold := (AddwOperation.iff_sp1_full (cols :=
          { value := value, msb := { msb := msb } })
        h_isU64_b h_isU64_c).mpr
      ⟨h_isU32_value, h_bv32, h_msb_eq⟩
    exact (SP1Clean.AddwOp.iff_sp1 ⟨b, c, value, msb⟩).mpr h_allHold

/-- Extract `Word.isU64 op_c_memory.prev_value` from
`ALUTypeReader.Gated.Assertion.Spec` pinned at `is_real = is_trusted = 1`,
regardless of `imm_c`. For ADDW (imm_c = 0) the register-access byte-bus
fires and gives isU64 directly. For ADDIW (imm_c = 1) the byte-bus is
vacuous but `imm_c * (prev_value[i] - op_c[i]) = 0` together with
`op_c[i] < 65536` from `ProgramGated.Spec` give the per-limb bound. -/
private lemma isU64_op_c_of_alu_spec_pinned
    {clk_high clk_low : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ALUTypeReader (ZMod p)}
    (h_alu : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨clk_high, clk_low, 19, pc, op_a_write_value, cols, 1, 1⟩) :
    Word.isU64 cols.op_c_memory.prev_value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  -- Unfold the Gated.Spec into its 13 conjuncts.
  obtain ⟨_h_ir_bin, h_prog, _h_ra_a, _h_ra_b, h_ra_c, _, _, _, _,
          h_im0, h_im1, h_im2, h_im3⟩ := h_alu
  -- ProgramGated.Spec at mult = 1 ≠ 0 gives ProgramSpec.
  have h_prog' :
      SP1Clean.ProgramSpec
        (#v[pc[0], pc[1], pc[2], 19, cols.op_a, cols.op_b, 0, 0, 0,
            cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
            cols.op_a_0, 0, cols.imm_c] : fields 16 (ZMod p)) := by
    rcases h_prog with h | h
    · exact absurd h one_ne_zero
    · exact h
  obtain ⟨_h_trusted, _h_op_a_lt, _h_op_b_lt, h_op_c_lt, _h_op_a_0_bin, _h_op_a_0_iff,
          _h_imm_b_bin, h_imm_c_bin, _⟩ := h_prog'
  obtain ⟨h_oc0_lt, h_oc1_lt, h_oc2_lt, h_oc3_lt⟩ := h_op_c_lt
  -- Case on imm_c.
  by_cases h_imm_c : cols.imm_c = (0 : ZMod p)
  · -- ADDW: 1 - 0 ≠ 0, so byte-bus fires → isU64 directly.
    have h_mult_ne : ((1 : ZMod p) - cols.imm_c) ≠ 0 := by
      rw [h_imm_c]; simp
    simp only [SP1Clean.RegisterAccess.Assertion.Spec,
               SP1Clean.OperandAccess.AssertionGated.Spec] at h_ra_c
    exact (h_ra_c.resolve_left h_mult_ne).2.2
  · -- ADDIW: imm_c = 1; use prev_value[i] = op_c[i] + op_c bounds.
    have h_imm_c_one : cols.imm_c = (1 : ZMod p) := by
      rcases h_imm_c_bin with h | h
      · exact absurd h h_imm_c
      · exact h
    have h_pv0 : cols.op_c_memory.prev_value[0] = cols.op_c[0] := by
      rw [h_imm_c_one, one_mul] at h_im0
      linear_combination h_im0
    have h_pv1 : cols.op_c_memory.prev_value[1] = cols.op_c[1] := by
      rw [h_imm_c_one, one_mul] at h_im1
      linear_combination h_im1
    have h_pv2 : cols.op_c_memory.prev_value[2] = cols.op_c[2] := by
      rw [h_imm_c_one, one_mul] at h_im2
      linear_combination h_im2
    have h_pv3 : cols.op_c_memory.prev_value[3] = cols.op_c[3] := by
      rw [h_imm_c_one, one_mul] at h_im3
      linear_combination h_im3
    -- Convert field-level `cols.op_c[i] < 65536` to val-level via the
    -- definition of `<` on `ZMod p` (= val.val).
    have h_65536_val : (65536 : ZMod p).val = 65536 := by
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl]
      rw [ZMod.val_natCast_of_lt (by omega)]
    have h_oc0_val_lt : cols.op_c[0].val < 65536 := by
      have : cols.op_c[0].val < (65536 : ZMod p).val := h_oc0_lt
      omega
    have h_oc1_val_lt : cols.op_c[1].val < 65536 := by
      have : cols.op_c[1].val < (65536 : ZMod p).val := h_oc1_lt
      omega
    have h_oc2_val_lt : cols.op_c[2].val < 65536 := by
      have : cols.op_c[2].val < (65536 : ZMod p).val := h_oc2_lt
      omega
    have h_oc3_val_lt : cols.op_c[3].val < 65536 := by
      have : cols.op_c[3].val < (65536 : ZMod p).val := h_oc3_lt
      omega
    apply Word.isU64_of_cases
    · simp only [h_pv0]; exact (by simpa using h_oc0_val_lt)
    · simp only [h_pv1]; exact (by simpa using h_oc1_val_lt)
    · simp only [h_pv2]; exact (by simpa using h_oc2_val_lt)
    · simp only [h_pv3]; exact (by simpa using h_oc3_val_lt)

set_option maxHeartbeats 1200000 in
-- `maxHeartbeats` bump covers the `addwOp_spec_iff_rv64_addw.mpr`
-- elaboration cost (iff form involves the heavy `RV64.addw c b` BitVec
-- expression; defeq matching during the inferred-type check is
-- expensive).
/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Addw.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `ALUTypeReader.Gated.Assertion.Spec`,
`Main[13] = 0` (the chip-level `op_a_0` zero gate), and the semantic
RV64-addw conjunct (`Word.isU64` of the result + the BitVec equation),
under `is_real = Main[35] = 1`. The byte-decomposition + sign-extension
MSB witness threaded by SP1's `AddwOperation` internally is *not*
exposed in the RHS — it's reconstructed via `addwOp_spec_iff_rv64_addw`
from the BitVec equation, `Word.isU64` bounds of op_b / op_c (available
from `ALUTypeReader.Gated.Spec`'s `RegisterAccess.Spec` sub-conjuncts),
and the `iff_sp1_full` round-trip. Used inside the Sail clause's
external bridge to construct an `allHold` from the structural pieces
of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 36) (h_is_real : Main[35] = 1) :
    (_root_.Addw.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[35]⟩ ∧
       SP1Clean.ALUTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 19,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13], op_b := Main[14],
             op_b_memory :=
               { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                 access_timestamp :=
                   { prev_low := Main[19], diff_low_limb := Main[20] } },
             op_c := #v[Main[21], Main[22], Main[23], Main[24]],
             op_c_memory :=
               { prev_value := #v[Main[25], Main[26], Main[27], Main[28]],
                 access_timestamp :=
                   { prev_low := Main[29], diff_low_limb := Main[30] } },
             imm_c := Main[31] },
           Main[35], Main[35]⟩ ∧
       Main[13] = 0 ∧
       Word.isU64 (#v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535]
         : Word (ZMod p)) ∧
       Word.toBitVec64 #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535] =
         RV64.addw
           (Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]])
           (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Use iff_sp1 at the specific Inputs to bridge `AddwOperation.constraints.allHold`
  -- to `AddwOp.Spec ⟨…⟩`.
  have h_addwop_iff :
      (_root_.AddwOperation.constraints
        (#v[Main[15], Main[16], Main[17], Main[18]] : Vector (ZMod p) 4)
        (#v[Main[25], Main[26], Main[27], Main[28]] : Vector (ZMod p) 4)
        { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } } 1).allHold
      ↔ SP1Clean.AddwOp.Spec
          ⟨#v[Main[15], Main[16], Main[17], Main[18]],
           #v[Main[25], Main[26], Main[27], Main[28]],
           #v[Main[32], Main[33]],
           Main[34]⟩ :=
    (SP1Clean.AddwOp.iff_sp1
      ⟨#v[Main[15], Main[16], Main[17], Main[18]],
       #v[Main[25], Main[26], Main[27], Main[28]],
       #v[Main[32], Main[33]],
       Main[34]⟩).symm
  rw [_root_.Addw.allHold_constraints_iff Main, h_is_real,
      h_addwop_iff,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1]
  refine ⟨?_, ?_⟩
  · -- Forward: allHold + AddwOp.Spec → structural + (isU64 ∧ BV64 = RV64.addw).
    rintro ⟨h_addwop, h_cpu, h_alu, _, h_op_a_0⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 (#v[Main[15], Main[16], Main[17], Main[18]]
        : Word (ZMod p)) := by
      have h_ra_b := h_alu.2.2.2.1
      simp only [SP1Clean.RegisterAccess.Assertion.Spec,
                 SP1Clean.OperandAccess.AssertionGated.Spec] at h_ra_b
      exact (h_ra_b.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 (#v[Main[25], Main[26], Main[27], Main[28]]
        : Word (ZMod p)) := isU64_op_c_of_alu_spec_pinned h_alu
    obtain ⟨h_isU64_v, h_bv64⟩ :=
      (addwOp_spec_iff_rv64_addw h_isU64_b h_isU64_c).mp h_addwop
    exact ⟨h_cpu, h_alu, h_op_a_0, h_isU64_v, h_bv64⟩
  · -- Backward: structural + (isU64 ∧ BV64 = RV64.addw) → allHold + AddwOp.Spec.
    rintro ⟨h_cpu, h_alu, h_op_a_0, h_isU64_v, h_bv64⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 (#v[Main[15], Main[16], Main[17], Main[18]]
        : Word (ZMod p)) := by
      have h_ra_b := h_alu.2.2.2.1
      simp only [SP1Clean.RegisterAccess.Assertion.Spec,
                 SP1Clean.OperandAccess.AssertionGated.Spec] at h_ra_b
      exact (h_ra_b.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 (#v[Main[25], Main[26], Main[27], Main[28]]
        : Word (ZMod p)) := isU64_op_c_of_alu_spec_pinned h_alu
    -- Normalize `h_isU64_v` and `h_bv64` to the form `addwOp_spec_iff_rv64_addw`
    -- expects (`#v[value[0], value[1], …]` with `value = #v[Main[32], Main[33]]`).
    have h_isU64_v' : Word.isU64
        (#v[(#v[Main[32], Main[33]] : HWord (ZMod p))[0],
            (#v[Main[32], Main[33]] : HWord (ZMod p))[1],
            Main[34] * 65535, Main[34] * 65535] : Word (ZMod p)) := h_isU64_v
    have h_bv64' :
        Word.toBitVec64 (#v[(#v[Main[32], Main[33]] : HWord (ZMod p))[0],
                             (#v[Main[32], Main[33]] : HWord (ZMod p))[1],
                             Main[34] * 65535, Main[34] * 65535]
          : Word (ZMod p)) =
        RV64.addw (Word.toBitVec64 (#v[Main[25], Main[26], Main[27], Main[28]]
                    : Word (ZMod p)))
                  (Word.toBitVec64 (#v[Main[15], Main[16], Main[17], Main[18]]
                    : Word (ZMod p))) := h_bv64
    have h_addwop : SP1Clean.AddwOp.Spec
        ⟨#v[Main[15], Main[16], Main[17], Main[18]],
         #v[Main[25], Main[26], Main[27], Main[28]],
         #v[Main[32], Main[33]],
         Main[34]⟩ :=
      (addwOp_spec_iff_rv64_addw h_isU64_b h_isU64_c).mpr ⟨h_isU64_v', h_bv64'⟩
    refine ⟨h_addwop, h_cpu, h_alu, ?_, h_op_a_0⟩
    ring

-- Note: an `rv64_addiw_eq_of_addwop_spec` companion (lifting the same
-- AddwOperation.spec result to `RV64.addiw` for the `imm_c = 1` arm) is
-- planned for Phase 1.1 once `ALUTypeReader.Gated.Assertion.Spec` exposes
-- the trusted-instruction immediate sign-extension contract that the
-- bridge needs (currently bundled inside `ProgramGated.Spec`'s opaque
-- program-table lookup).

end SP1Clean.Addw
