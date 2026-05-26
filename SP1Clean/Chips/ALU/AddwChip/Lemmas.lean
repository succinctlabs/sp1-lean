import SP1Clean.Chips.ALU.AddwChip.Cols
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Clean.Operations.AddwOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Addw.Common
import RISCV.Instructions

/-! # `AddwChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.Addw.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `AddwOp.Spec`, `cpuStateSpec`,
  `aluTypeReaderSpec`, the two scalar gates. Used downstream by
  `SailBridge.lean` to reconstruct `(Addw.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`. -/

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

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Addw.constraints Main` is exactly the conjunction of `AddwOp.Spec`,
`CPUState.Gated.Spec`, and `ALUTypeReader.Gated.Spec` over `fromMain Main`,
under `is_real = Main[35] = 1`. The free `Main[35] * (Main[35] - 1) = 0`
gate is absorbed into both Gated.Specs' first conjuncts. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 36) (h_is_real : Main[35] = 1) :
    (_root_.Addw.constraints Main).allHold ↔
      (SP1Clean.AddwOp.Spec
          ⟨#v[Main[15], Main[16], Main[17], Main[18]],
           #v[Main[25], Main[26], Main[27], Main[28]],
           #v[Main[32], Main[33]],
           Main[34]⟩ ∧
       SP1Clean.CPUState.Gated.Assertion.Spec
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
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Use iff_sp1 at the specific Inputs to bridge `AddwOperation.constraints.allHold`
  -- to the new `AddwOp.Spec ⟨…⟩` form (provides ground term for unification).
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
  -- Drop the chip-level redundant `1 * (1 - 1) = 0`; absorbed into Gated.Specs.
  refine ⟨?_, ?_⟩
  · rintro ⟨h_addwop, h_cpu, h_alu, _, h_op_a_0⟩
    exact ⟨h_addwop, h_cpu, h_alu, h_op_a_0⟩
  · rintro ⟨h_addwop, h_cpu, h_alu, h_op_a_0⟩
    refine ⟨h_addwop, h_cpu, h_alu, ?_, h_op_a_0⟩
    ring

/-- Bridge the `AddwOperation.spec` 32-bit BitVec equation +
sign-extension MSB to the 64-bit `RV64.addw` semantic. Given the
natural-form `AddwOp.Spec` plus operand `Word.isU64` bounds, the
sign-extended Word `#v[value[0], value[1], msb*65535, msb*65535]`
equals `RV64.addw c.toBitVec64 b.toBitVec64`. Used by
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

-- Note: an `rv64_addiw_eq_of_addwop_spec` companion (lifting the same
-- AddwOperation.spec result to `RV64.addiw` for the `imm_c = 1` arm) is
-- planned for Phase 1.1 once `ALUTypeReader.Gated.Assertion.Spec` exposes
-- the trusted-instruction immediate sign-extension contract that the
-- bridge needs (currently bundled inside `ProgramGated.Spec`'s opaque
-- program-table lookup).

end SP1Clean.Addw
