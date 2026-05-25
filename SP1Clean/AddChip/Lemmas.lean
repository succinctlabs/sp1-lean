import SP1Clean.AddChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.AddOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Add.Common

/-! # `AddChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real` (carried as the chip's
  `Assumptions` in `Circuit.lean`). Closes via recursive `ext` through the
  `@[ext]`-marked nested sub-structures (CPUState, RTypeReader,
  MemoryAccessInSharedCols, etc.) and `Vector.ext` reducing to per-element
  `rfl`s.
- `allHold_iff_structural` — bridges `(_root_.Add.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `AddOp.Spec`, `cpuStateSpec`,
  `rtypeReaderSpec`, the two scalar gates. Used downstream by
  `SailBridge.lean` to reconstruct `(Add.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[32] = is_real` (which
matches the constraint compiler's emission — Main[32] is both `is_real` and
`is_trusted`). Recursive `ext` through `@[ext]`-marked sub-structures plus
`Vector.ext` reduces to per-element equations closed by `rfl` (each
`(toMain cols)[k]` reduces by `@[reducible]` to the matching `cols`
projection) or by the precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : AddCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  -- Break up the cols structure.
  rcases cols with ⟨state, adapter, op_a_write_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  -- Apply all relevant ext lemmas
  simp [this, AddCols.ext_iff, CPUState.ext_iff,
    RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  -- All that remains are trivial Array equality using `interval_cases`.
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Add.constraints Main` is exactly the conjunction of `AddOp.Spec`,
`cpuStateSpec`, and `rtypeReaderSpec` over `fromMain Main`, under
`is_real = Main[32] = 1`. Used inside the Sail clause's external bridge
(`SailBridge.sail_correct_of_formalSpec`) to construct an `allHold` from
the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔
      (SP1Clean.AddOp.Spec
          #v[Main[15], Main[16], Main[17], Main[18]]
          #v[Main[22], Main[23], Main[24], Main[25]]
          #v[Main[28], Main[29], Main[30], Main[31]] ∧
       SP1Clean.CPUState.cpuStateSpec Main[2] Main[1] ∧
       SP1Clean.RTypeReader.rtypeReaderSpec
          (Main[2] + Main[1] * 65536) 0 #v[Main[3], Main[4], Main[5]]
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
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Add.allHold_constraints_iff Main, h_is_real,
    AddOperation.allHold_constraints_iff,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.AddOp.Spec, SP1Clean.CPUState.cpuStateSpec,
        SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

end SP1Clean.Add
