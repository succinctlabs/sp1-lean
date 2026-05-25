import SP1Clean.SubChip.Cols
import SP1Operations.Operation.SubOperation.SubOperation
import SP1Clean.Operations.SubOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Sub.Common

/-! # `SubChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery. Mirrors `SP1Clean/AddChip/Lemmas.lean` 1-for-1, swapping
`AddOp`/`AddOperation` → `SubOp`/`SubOperation` and opcode `0` → `2`.
Bodies are `sorry` for now — the directory-form scaffold targets the
structural layout first; the proof bodies follow the AddChip recipe
verbatim (recursive `ext` + `Vector.ext` for `fromMain_toMain`, and
`_root_.Sub.allHold_constraints_iff` + sub-Spec `iff_sp1` rewrites for
`allHold_iff_structural`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : SubCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  sorry

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Sub.constraints Main` is exactly the conjunction of `SubOp.Spec`,
`cpuStateSpec`, and `rtypeReaderSpec` over `fromMain Main`, under
`is_real = Main[32] = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Sub.constraints Main).allHold ↔
      (SP1Clean.SubOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          #v[Main[28], Main[29], Main[30], Main[31]] ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536) 2 #v[Main[3], Main[4], Main[5]]
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
       Main[32] * (Main[32] - 1) = 0 ∧
       Main[13] = 0) := by
  sorry

end SP1Clean.SubChip
