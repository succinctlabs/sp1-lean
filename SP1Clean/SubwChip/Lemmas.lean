import SP1Clean.SubwChip.Cols
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Clean.Operations.SubwOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Subw.Common
import RISCV.Instructions

/-! # `SubwChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.Subw.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `SubwOp.Spec`,
  `CPUState.Gated.Spec`, `RTypeReader.Gated.Spec`, and the trailing
  `Main[13] = 0` op_a_0 gate. Used downstream by `SailBridge.lean` to
  reconstruct `(Subw.constraints (toMain cols)).allHold` from the
  structural conjuncts of `FormalSpec`.

Mirrors `SP1Clean/SubChip/Lemmas.lean` for the W-style result shape
(`{ value := #v[Main[28], Main[29]], msb := { msb := Main[30] } }`) and
opcode `20` (SUBW). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : SubwCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, subw_value, subw_msb, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, SubwCols.ext_iff, CPUState.ext_iff,
    RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Subw.constraints Main` is exactly the conjunction of `SubwOp.Spec`,
`CPUState.Gated.Assertion.Spec`, and `RTypeReader.Gated.Assertion.Spec`
over `fromMain Main`, under `is_real = Main[31] = 1`. The chip-level
free `Main[31] * (Main[31] - 1) = 0` gate is absorbed into both
Gated.Specs' first conjuncts. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 32) (h_is_real : Main[31] = 1) :
    (_root_.Subw.constraints Main).allHold ↔
      (SP1Clean.SubwOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          { value := #v[Main[28], Main[29]], msb := { msb := Main[30] } } ∧
       SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[31]⟩ ∧
       SP1Clean.RTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 20,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535],
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
             op_c := Main[21],
             op_c_memory :=
               { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                 access_timestamp :=
                   { prev_low := Main[26], diff_low_limb := Main[27] } } },
           Main[31], Main[31]⟩ ∧
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Subw.allHold_constraints_iff Main, h_is_real,
      SP1Clean.SubwOp.iff_sp1,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.RTypeReader.Gated.Assertion.Spec_iff_sp1]
  -- Drop the trivial `1 * (1 - 1) = 0` conjunct — both Gated.Specs already
  -- carry their own `is_real * (is_real - 1) = 0`.
  refine ⟨?_, ?_⟩
  · rintro ⟨h_subwop, h_cpu, h_rtr, _, h_op_a_0⟩
    exact ⟨h_subwop, h_cpu, h_rtr, h_op_a_0⟩
  · rintro ⟨h_subwop, h_cpu, h_rtr, h_op_a_0⟩
    refine ⟨h_subwop, h_cpu, h_rtr, ?_, h_op_a_0⟩
    ring

/-- Bridge the `SubwOperation.spec` 32-bit BitVec equation +
sign-extension MSB to the 64-bit `RV64.subw` semantic. Given the
natural-form `SubwOp.Spec` plus operand `Word.isU64` bounds, the
sign-extended Word `#v[value[0], value[1], msb*65535, msb*65535]`
equals `RV64.subw c.toBitVec64 b.toBitVec64`. Used by
`Assertion.soundness` to discharge the BitVec conjunct of
`FormalSpec`. -/
lemma rv64_subw_eq_of_subwop_spec
    (b c : Word (ZMod p)) (value : HWord (ZMod p)) (msb : ZMod p)
    (h_isU64_b : b.isU64) (h_isU64_c : c.isU64)
    (h_subwop : SP1Clean.SubwOp.Spec b c
      ({ value := value, msb := { msb := msb } } : SubwOperation (ZMod p))) :
    Word.toBitVec64 #v[value[0], value[1], msb * 65535, msb * 65535] =
      RV64.subw c.toBitVec64 b.toBitVec64 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Bridge the natural-form Spec to `SubwOperation.constraints.allHold`,
  -- then apply `SubwOperation.spec` for the 32-bit equation + msb fact.
  have h_allHold : (SubwOperation.constraints b c
        { value := value, msb := { msb := msb } } 1).allHold :=
    (SP1Clean.SubwOp.iff_sp1 _ _ _).mpr h_subwop
  obtain ⟨h_isU32_v, h_subw_bv, h_msb_eq⟩ :=
    SubwOperation.spec h_isU64_b h_isU64_c h_allHold
  -- Unfold `RV64.subw` and bridge `BitVec.extractLsb' 0 32 ·.toBitVec64`
  -- to `·.low.toBitVec32` via `Word.setWidth_eq_low` (which uses
  -- `BitVec.setWidth`; the two are defeq for narrowing).
  simp only [RV64.subw]
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
  -- Substitute the SubwOperation.spec equation:
  --   value.toBitVec32 = b.low.toBitVec32 - c.low.toBitVec32
  -- but the unfolded `RV64.subw` form uses `BitVec.sub` instead of `HSub.hSub`;
  -- bridge both directions.
  rw [show b.low.toBitVec32.sub c.low.toBitVec32 = HWord.toBitVec32 value by
    rw [h_subw_bv]; rfl]
  -- Apply `sign_extend_32_to_64_msb`: signExtend 64 value.toBitVec32 equals
  -- the Word with high limbs `if msb then 65535 else 0`. Combined with
  -- `msb = if … then 1 else 0`, the high limbs match `msb * 65535`.
  -- Reduce the `{ value, msb }` projections in `h_msb_eq` first.
  simp only at h_msb_eq h_isU32_v
  rw [HWord.sign_extend_32_to_64_msb h_isU32_v]
  -- Discharge `msb * 65535 = if … then 65535 else 0` via `h_msb_eq`.
  rw [h_msb_eq]
  by_cases h : (HWord.toBitVec32 value).msb = true
  · simp [h]
  · simp [h]

end SP1Clean.Subw
