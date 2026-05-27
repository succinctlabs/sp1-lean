import SP1Clean.Chips.ALU.ShiftLeftChip.Multiplicity.Cols
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Common

/-! # `ShiftLeftChip` cols-level lemmas (stub).

Real `fromMain_toMain` + `allHold_iff_structural` deferred — bodies and
signatures are stubs. The Cols + Circuit scaffold is the priority. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeftChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (cols : ShiftLeftCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_sll + cols.is_sllw) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, result, c_bits, v_01, v_012, v_0123,
                    shift_u16, lower_limb, higher_limb, limb_result, sllw_msb,
                    is_sll, is_sllw, is_sllw_imm, adapter_cols⟩
  have h_trust : adapter_cols.is_trusted = is_sll + is_sllw := by
    simpa using h_trusted
  simp [h_trust, ShiftLeftCols.ext_iff, CPUState.ext_iff,
    ALUTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff, Array.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (intro i hi₁ hi₂; interval_cases i <;> rfl)

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 65)
    (h_is_real : Main[62] + Main[63] = 1) :
    (_root_.ShiftLeft.constraints Main).allHold ↔ True := by
  sorry

end SP1Clean.ShiftLeftChip
