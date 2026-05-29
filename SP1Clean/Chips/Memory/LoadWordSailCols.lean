import SP1Clean.Chips.Memory.LoadWordChip

/-! # Cols-level Sail helpers for `LoadWordChip` (Sail-isolation layer)

The Sail-monadic content for `LoadWord` lives here, quarantined out of the
pure-Clean `LoadWordChip.lean`. Mirrors `SP1Clean/Chips/ALU/AddChip/Cols.lean`'s
cols-level Sail-side helpers + round-trip lemmas. Consumed only by
`LoadWordSailBridge.lean`, which lifts SP1's
`_root_.Load.LoadWord.correct_lw` to a cols-parameterized equivalence.

Splitting this off keeps `LoadWordChip.lean` free of `open Sail`/`SailM`, so the
chip's Clean circuit + `FormalSpec` + soundness/completeness are pure-Clean and the
Sail equivalence is a thin, on-demand bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadWord

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail helpers + structural bridges (LW + LWU). -/

@[reducible] def sp1_op_a_cols (cols : LoadWordCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LoadWordCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_imm_c_cols (cols : LoadWordCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

@[reducible] def sp1_load_word_cols (cols : LoadWordCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64
    #v[cols.op_a_write_value_lo[0], cols.op_a_write_value_lo[1],
       (65535 : ZMod p) * cols.signed_extension_msb,
       (65535 : ZMod p) * cols.signed_extension_msb])
  return RETIRE_SUCCESS

def loadWordInitialState_cols (cols : LoadWordCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 44, fromMain Main = cols →
    (_root_.Load.LoadWord.constraints Main).initialState s

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_a_cols (fromMain Main) = _root_.Load.LoadWord.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_b_cols (fromMain Main) = _root_.Load.LoadWord.sp1_ob_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_imm_c_cols (fromMain Main) = _root_.Load.LoadWord.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_load_word_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_load_word_cols (fromMain Main) = _root_.Load.LoadWord.sp1_load_word Main := rfl

omit [Fact (2 ^ 17 < p)] in
/-- Cols round-trip. `is_trusted := Main[42] + Main[43] = is_lw + is_lwu`. -/
lemma fromMain_toMain (cols : LoadWordCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_lw + cols.is_lwu) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    load_prev_value, lmph, lmpl, lmf, lmdl, lmdh,
                    ob, oawvlo, sem, is_lw, is_lwu, adapter_cols⟩
  have : adapter_cols.is_trusted = is_lw + is_lwu := by simpa using h_trusted
  simp [this, LoadWordCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

end SP1Clean.LoadWord
