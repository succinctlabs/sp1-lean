import SP1Clean.Chips.Memory.LoadByteChip

/-! # Cols-level Sail helpers for `LoadByteChip` (Sail-isolation layer)

The Sail-monadic content for `LoadByte` lives here, quarantined out of the
pure-Clean `LoadByteChip.lean`. Mirrors `SP1Clean/Chips/ALU/AddChip/Cols.lean`'s
cols-level Sail-side helpers + round-trip lemmas. Consumed only by
`LoadByteSailBridge.lean`, which lifts SP1's
`_root_.Load.LoadByte.correct_lb` to a cols-parameterized equivalence.

Splitting this off keeps `LoadByteChip.lean` free of `open Sail`/`SailM`, so the
chip's Clean circuit + `FormalSpec` + soundness/completeness are pure-Clean and the
Sail equivalence is a thin, on-demand bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadByte

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail helpers + structural bridges (Phase 4 SailBridge prep)

LoadByte has two opcode variants: LB (signed, opcode 29) and LBU
(unsigned, opcode 32). Both share the same `sp1_load_byte` projector
(which reads the chip-stored `signed_extension_flag` to produce either
signed-extended or zero-extended write data). Two SailBridge theorems
(`sail_correct_of_allHold_lb` and `_lbu`) call `correct_lb` and
`correct_lbu` respectively. -/

@[reducible] def sp1_op_a_cols (cols : LoadByteCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LoadByteCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

/-- Note: LoadByte's `sp1_imm_c` uses `Main[21].val` directly (not
`Word.toNat`), unlike Store side. Matches `_root_.Load.LoadByte.sp1_imm_c`. -/
@[reducible] def sp1_imm_c_cols (cols : LoadByteCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

@[reducible] def sp1_load_byte_cols (cols : LoadByteCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64
    #v[cols.selected_byte + (65280 : ZMod p) * cols.signed_extension_flag,
       (65535 : ZMod p) * cols.signed_extension_flag,
       (65535 : ZMod p) * cols.signed_extension_flag,
       (65535 : ZMod p) * cols.signed_extension_flag])
  return RETIRE_SUCCESS

def loadByteInitialState_cols (cols : LoadByteCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 47, fromMain Main = cols →
    (_root_.Load.LoadByte.constraints Main).initialState s

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 47) :
    sp1_op_a_cols (fromMain Main) = _root_.Load.LoadByte.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 47) :
    sp1_op_b_cols (fromMain Main) = _root_.Load.LoadByte.sp1_ob_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 47) :
    sp1_imm_c_cols (fromMain Main) = _root_.Load.LoadByte.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_load_byte_cols_fromMain (Main : Vector (ZMod p) 47) :
    sp1_load_byte_cols (fromMain Main) = _root_.Load.LoadByte.sp1_load_byte Main := rfl

omit [Fact (2 ^ 17 < p)] in
/-- Cols round-trip. `is_trusted := Main[45] + Main[46] = is_lb + is_lbu`
(LoadByte's "is_real" is the sum of the two opcode flags). -/
lemma fromMain_toMain (cols : LoadByteCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_lb + cols.is_lbu) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    load_prev_value, lmph, lmpl, lmf, lmdl, lmdh,
                    ob2, ob1, ob0, sl, sllb, sb, sef,
                    is_lb, is_lbu, adapter_cols⟩
  have : adapter_cols.is_trusted = is_lb + is_lbu := by simpa using h_trusted
  simp [this, LoadByteCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

end SP1Clean.LoadByte
