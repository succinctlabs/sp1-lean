import SP1Clean.Chips.ALU.ShiftRightChip.Multiplicity.Cols
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Common

/-! # `ShiftRightChip` cols-level lemmas (stub). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (cols : ShiftRightCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted =
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, result, b_msb, srw_msb, c_bits,
                    v_01, v_012, v_0123, shifted_intermediates,
                    limb_result, shift_u16, is_srl, is_sra, is_srlw,
                    is_sraw, is_w_imm, adapter_cols⟩
  have h_trust : adapter_cols.is_trusted = is_srl + is_sra + is_srlw + is_sraw := by
    simpa using h_trusted
  simp [h_trust, ShiftRightCols.ext_iff, CPUState.ext_iff,
    ALUTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff, Array.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (intro i hi₁ hi₂; interval_cases i <;> rfl)

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 69)
    (h_is_real : Main[64] + Main[65] + Main[66] + Main[67] = 1) :
    (_root_.ShiftRight.constraints Main).allHold ↔ True := by
  sorry

end SP1Clean.ShiftRightChip
