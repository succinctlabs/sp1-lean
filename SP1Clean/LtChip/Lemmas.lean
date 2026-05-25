import SP1Clean.LtChip.Cols
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
