import SP1Clean.Chips.ALU.LtChip.Multiplicity.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Operations.GatedLtSignedOp
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common
import RISCV.Instructions

/-! # `LtChip` cols-level lemmas (directory-form scaffold)

Two non-trivial lemmas: `fromMain_toMain` (round-trip) and
`allHold_iff_structural` (the chip-level constraint bridge). Bodies are
`sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain`, conditional on the chip's
aggregate `is_real` sum matching the adapter's trust marker
(`cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`). Lifted
from `SP1Clean.AddChip/Lemmas.lean#fromMain_toMain` — recursive `ext`
through `@[ext]`-marked nested structures (CPUState, ALUTypeReader,
MemoryAccessInSharedCols, UserModeReaderCols) plus `Vector.ext` reduces
to per-element equations closed by `rfl` (each `(toMain cols)[k]`
reduces via `@[reducible]` to the matching `cols` projection) or by the
precondition on the `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : LtCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_slt + cols.is_sltu) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, compare_bit, u16_flags, not_eq_inv,
                    comparison_limbs, b_msb, c_msb, is_slt, is_sltu, adapter_cols⟩
  have : adapter_cols.is_trusted = is_slt + is_sltu := by simpa using h_trusted
  simp [this, LtCols.ext_iff, CPUState.ext_iff,
    ALUTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

-- TODO[clean-master-plan-phase-3,p3-lt-gated-iff-sp1]: blocked on missing
-- operation-level bridges between `GatedLtSignedOp.Assertion.FormalSpec` and
-- `LtOperationSigned.constraints.allHold` (similarly for the embedded
-- `GatedLtUnsignedOp`). Neither `GatedLtSignedOp.iff_sp1` nor
-- `GatedLtUnsignedOp.iff_sp1` exists today (verified 2026-05-25); only
-- `U16MSBOp.iff_sp1`, `U16CompareOp.iff_sp1`, and `LtOperationUnsigned`'s
-- direct `allHold_constraints_iff` are available.
--
-- Closure path (proposed new worklist row `p3-lt-gated-iff-sp1`):
--   1. Add `GatedLtUnsignedOp.iff_sp1 : Spec input ↔ allHold` under
--      `h_gate : input.gate = 1`, using `LtOperationUnsigned.allHold_constraints_iff`
--      + `U16CompareOp.iff_sp1` + per-conjunct `mul_eq_zero`/`sub_eq_zero`
--      rewrites. Est. ~150-200 lines.
--   2. Add `GatedLtSignedOp.iff_sp1 : Spec input ↔ allHold` under `h_gate := 1`,
--      composing `GatedLtUnsignedOp.iff_sp1` + 2× `U16MSBOp.iff_sp1` via
--      `LtOperationSigned.allHold_constraints_iff`. Est. ~100-150 lines.
--   3. Use both here + `CPUState.Assertion.Spec_iff_sp1` +
--      `ALUTypeReader.Assertion.Spec_iff_sp1` + `LtOperationSigned.spec.signed`/`.unsigned`
--      to bridge LHS ↔ RHS. Est. ~50-80 lines.
/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is the chip's canonical `FormalSpec`, under
`is_real = Main[32] + Main[33] = 1`. The RHS mirrors `LtChip.FormalSpec`
applied to `fromMain Main` and is exposed in flat-row form so soundness
can structurally destructure the chip Spec into SP1-native `allHold`
emissions. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44)
    (h_is_real : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔ FormalSpec (fromMain Main) := by
  sorry

end SP1Clean.LtChip
