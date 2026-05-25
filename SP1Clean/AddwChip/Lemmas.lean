import SP1Clean.AddwChip.Cols
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Clean.Operations.AddwOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Addw.Common

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
`cpuStateSpec`, and `aluTypeReaderSpec` over `fromMain Main`, under
`is_real = Main[35] = 1`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 36) (h_is_real : Main[35] = 1) :
    (_root_.Addw.constraints Main).allHold ↔
      (SP1Clean.AddwOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[25], Main[26], Main[27], Main[28]]
          { value := #v[Main[32], Main[33]], msb := { msb := Main[34] } } ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.ALUTypeReader.aluTypeReaderSpec
          (Main[2] + Main[1] * 65536) 19 #v[Main[3], Main[4], Main[5]]
          #v[Main[32], Main[33], Main[34] * 65535, Main[34] * 65535]
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
            imm_c := Main[31] } ∧
       Main[35] * (Main[35] - 1) = 0 ∧
       Main[13] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Addw.allHold_constraints_iff Main, h_is_real,
    AddwOperation.allHold_constraints_iff,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ALUTypeReader.aluTypeReaderSpec_iff_sp1]
  simp [SP1Clean.AddwOp.Spec, SP1Clean.CPUState.cpuStateSpec,
        SP1Clean.ALUTypeReader.aluTypeReaderSpec, and_assoc]

end SP1Clean.Addw
