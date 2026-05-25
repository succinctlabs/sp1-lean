import SP1Clean.AddiChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Reader.ITypeReader
import SP1Chips.Addi.Common

/-! # `AddiChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real` (carried as the chip's
  `Assumptions` in `Circuit.lean`).
- `allHold_iff_structural` — bridges `(_root_.Addi.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `AddOp.Spec`, `cpuStateSpec`,
  `itypeReaderSpec`, the two scalar gates. Used downstream by
  `SailBridge.lean` to reconstruct `(Addi.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[29] = is_real` (which
matches the constraint compiler's emission — Main[29] is both `is_real` and
`is_trusted`). Recursive `ext` through `@[ext]`-marked sub-structures plus
`Vector.ext` reduces to per-element equations closed by `rfl` (each
`(toMain cols)[k]` reduces by `@[reducible]` to the matching `cols`
projection) or by the precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : AddiCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, op_a_write_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, AddiCols.ext_iff, CPUState.ext_iff,
    ITypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Addi.constraints Main` is exactly the conjunction of `AddOp.Spec`,
`CPUState.Gated.Assertion.Spec`, and `ITypeReader.Gated.Assertion.Spec`
over `fromMain Main`, under `is_real = Main[29] = 1`. The chip-level free
`Main[29] * (Main[29] - 1) = 0` gate is absorbed into both Gated.Specs'
first conjuncts. Used inside the Sail clause's external bridge
(`SailBridge.sail_correct_of_formalSpec`) to construct an `allHold` from
the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 30) (h_is_real : Main[29] = 1) :
    (_root_.Addi.constraints Main).allHold ↔
      (SP1Clean.AddOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[21], Main[22], Main[23], Main[24]]
          #v[Main[25], Main[26], Main[27], Main[28]] ∧
       SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[29]⟩ ∧
       SP1Clean.ITypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 1,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[25], Main[26], Main[27], Main[28]],
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
             op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] },
           Main[29], Main[29]⟩ ∧
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Addi.allHold_constraints_iff Main, h_is_real,
      SP1Clean.AddOp.iff_sp1,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.ITypeReader.Gated.Assertion.Spec_iff_sp1]
  -- Drop the chip-level redundant `1 * (1 - 1) = 0`; absorbed into Gated.Specs.
  refine ⟨?_, ?_⟩
  · rintro ⟨h_addop, h_cpu, h_itr, _, h_op_a_0⟩
    exact ⟨h_addop, h_cpu, h_itr, h_op_a_0⟩
  · rintro ⟨h_addop, h_cpu, h_itr, h_op_a_0⟩
    refine ⟨h_addop, h_cpu, h_itr, ?_, h_op_a_0⟩
    ring

end SP1Clean.Addi
