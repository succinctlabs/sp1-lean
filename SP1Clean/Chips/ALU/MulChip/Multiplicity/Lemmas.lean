import SP1Clean.Chips.ALU.MulChip.Multiplicity.Cols
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Mul.Common

/-! # `MulChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas. Bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on the chip's
aggregate `is_real` sum (5-way) matching the adapter's trust marker.
Mirrors `SP1Clean/Chips/ALU/AddChip/Lemmas.lean:41`: recursive `ext` through
the `@[ext]`-marked sub-structures (`CPUState`, `RTypeReader`,
`MemoryAccessInSharedCols`, `UserModeReaderCols`) plus `Vector.ext`,
reducing to per-index equations closed by `rfl` (each `toMain`-projected
slot reduces by `@[reducible]` to the matching `cols` field) or by the
trust-marker precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : MulCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, a_word, carry, product, b_low_bytes, c_low_bytes,
                    b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend,
                    is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw, adapter_cols⟩
  have : adapter_cols.is_trusted = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw := by
    simpa using h_trusted
  simp [this, MulCols.ext_iff, CPUState.ext_iff,
        RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
        UserModeReaderCols.ext_iff]
  -- Remaining: Vector equalities for pc (3), a_word (4), carry (16), product (16),
  -- b_low_bytes (4), c_low_bytes (4), and the three 4-vector prev_value fields
  -- of the three MemoryAccess structs. All close pointwise via interval_cases.
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Mul.constraints Main` is the conjunction of `MulOp.Spec`, `cpuStateSpec`,
`rtypeReaderSpec`, and the 7 trailing scalar gates, under `is_real =
sum = 1`. Forward direction routes through `MulOp.of_sp1` for the
MulOperation conjunct and `cpuStateSpec_iff_sp1` / `rtypeReaderSpec_iff_sp1`
for the two reader conjuncts. Backward direction requires
`MulOp.allHold_of_main_holds` (currently `sorry`) — left as `sorry` here
since it's only needed by chip-level completeness which is out of scope. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 82)
    (h_is_real : Main[77] + Main[78] + Main[79] + Main[80] + Main[81] = 1) :
    (_root_.Mul.constraints Main).allHold ↔
      (SP1Clean.MulOp.Spec
          ⟨#v[Main[28], Main[29], Main[30], Main[31]],
           #v[Main[15], Main[16], Main[17], Main[18]],
           #v[Main[22], Main[23], Main[24], Main[25]],
           #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
              Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
              Main[46], Main[47]],
           #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
              Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
              Main[62], Main[63]],
           #v[Main[64], Main[65], Main[66], Main[67]],
           #v[Main[68], Main[69], Main[70], Main[71]],
           Main[72], Main[73], Main[74], Main[75], Main[76],
           Main[77], Main[78], Main[79], Main[80], Main[81]⟩ ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536)
          (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24)
          #v[Main[3], Main[4], Main[5]]
          #v[Main[28], Main[29], Main[30], Main[31]]
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
                  { prev_low := Main[26], diff_low_limb := Main[27] } } } ∧
       Main[77] * (Main[77] - 1) = 0 ∧
       Main[78] * (Main[78] - 1) = 0 ∧
       Main[79] * (Main[79] - 1) = 0 ∧
       Main[80] * (Main[80] - 1) = 0 ∧
       Main[81] * (Main[81] - 1) = 0 ∧
       (Main[77] + Main[78] + Main[79] + Main[80] + Main[81]) *
         (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] - 1) = 0 ∧
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Step 1: Expose the chip-level iff (10-tuple: 3 sub-allHolds + 7 scalars).
  change List.Forall SP1Constraint.toProp _ ↔ _
  rw [_root_.Mul.allHold_constraints_iff Main]
  -- Step 2: After the chip iff, the sub-allHolds carry `mult = sum`. Rewrite
  -- via `h_is_real` so they read `1`.
  rw [show (Main[77] + Main[78] + Main[79] + Main[80] + Main[81] : ZMod p) = 1
      from h_is_real]
  -- Step 3: Bridge CPUState and RTypeReader sub-allHolds to their Specs.
  rw [show List.Forall SP1Constraint.toProp
        (_root_.CPUState.constraints
          (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
          #v[Main[3] + 4, Main[4], Main[5]] 8 1)
        = (_root_.CPUState.constraints
            (CPUState.mk Main[0] Main[1] Main[2] #v[Main[3], Main[4], Main[5]])
            #v[Main[3] + 4, Main[4], Main[5]] 8 1).allHold from rfl,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1]
  rw [show List.Forall SP1Constraint.toProp
        (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
          #v[Main[3], Main[4], Main[5]]
          (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24)
          #v[Main[28], Main[29], Main[30], Main[31]] _ 1 1)
        = (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]]
            (Main[77] * 11 + Main[78] * 12 + Main[79] * 13 + Main[80] * 14 + Main[81] * 24)
            #v[Main[28], Main[29], Main[30], Main[31]] _ 1 1).allHold from rfl,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  -- Step 4: Bridge MulOperation sub-allHold to MulOp.Spec via of_sp1 (forward)
  --         and `allHold_of_main_holds` (backward — currently sorry'd inside MulOp,
  --         so we sorry the backward branch here too).
  refine ⟨?_, ?_⟩
  · -- Forward
    rintro ⟨h_mulop, h_cpu, h_rtr, b77, b78, b79, b81, b80, b_sum, h_op_a_0⟩
    -- Pull `Word.isU64 b/c` from `rtypeReaderSpec`'s 8th conjunct's 3rd
    -- subfield (the isU64 triple). Path: 7×`.2` + `.1` reaches conjunct 8;
    -- then `.2.2` reaches the isU64 sub-triple; then `.2.1`/`.2.2` for b/c.
    have h_isU64_b := h_rtr.2.2.2.2.2.2.2.1.2.2.2.1
    have h_isU64_c := h_rtr.2.2.2.2.2.2.2.1.2.2.2.2
    -- Bundle `Assumptions` for MulOp.of_sp1: `(sum=0 ∨ sum=1)` is trivial after
    -- `h_is_real`; the bounds conjunct supplies `isU64 b, c`.
    have h_mul_spec : SP1Clean.MulOp.Spec ⟨_, _, _, _, _, _, _, _, _, _, _, _,
                                            Main[77], Main[78], Main[79], Main[80], Main[81]⟩ :=
      SP1Clean.MulOp.of_sp1 _
        ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩
        (by change List.Forall SP1Constraint.toProp _; exact h_mulop)
    refine ⟨h_mul_spec, h_cpu, h_rtr, b77, b78, b79, b80, b81, ?_, h_op_a_0⟩
    -- aggregate-sum binarity: slot order in iff is 81 before 80; rearrange via
    -- `linear_combination` (matches `Aggregate.lean:291`).
    linear_combination b_sum * 1
  · -- Backward — requires MulOp.allHold_of_main_holds (sorry'd upstream).
    sorry

end SP1Clean.MulChip
