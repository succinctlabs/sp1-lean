import SP1Clean.Chips.Memory.StoreHalfChip

/-! # Cols-level Sail helpers for `StoreHalfChip` (Sail-isolation layer)

The Sail-monadic content for `StoreHalf` lives here, quarantined out of the
pure-Clean `StoreHalfChip.lean`. Mirrors the `LoadDouble` pilot's cols-level
Sail-side helpers + round-trip lemmas. Consumed only by
`StoreHalfSailBridge.lean`, which lifts SP1's
`_root_.Store.StoreHalf.correct_sh` to a cols-parameterized equivalence.

Splitting this off keeps `StoreHalfChip.lean` free of `open Sail`/`SailM`, so the
chip's Clean circuit + `FormalSpec` + soundness/completeness are pure-Clean and the
Sail equivalence is a thin, on-demand bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.StoreHalf

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail helpers + structural bridge (Phase 4 SailBridge prep)

Sibling of `SP1Clean.StoreByte`'s Phase 4 helpers, width 2 (SH). Opcode 37. -/

@[reducible] def sp1_op_a_cols (cols : StoreHalfCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : StoreHalfCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_imm_c_cols (cols : StoreHalfCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat cols.adapter.op_c_imm)

@[reducible] def sp1_sb_cols (cols : StoreHalfCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)])
  let addr : BitVec 64 := Word.toBitVec64
    #v[cols.addr_value[0], cols.addr_value[1], cols.addr_value[2], (0 : ZMod p)]
  Sail.ConcurrencyInterfaceV1.write_ram 64 2 0#64 addr
    (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)
  return RETIRE_SUCCESS

def storeHalfInitialState_cols (cols : StoreHalfCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 45, fromMain Main = cols →
    (_root_.Store.StoreHalf.constraints Main).initialState s

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 45) :
    sp1_op_a_cols (fromMain Main) = _root_.Store.StoreHalf.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 45) :
    sp1_op_b_cols (fromMain Main) = _root_.Store.StoreHalf.sp1_ob_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 45) :
    sp1_imm_c_cols (fromMain Main) = _root_.Store.StoreHalf.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_sb_cols_fromMain (Main : Vector (ZMod p) 45) :
    sp1_sb_cols (fromMain Main) = _root_.Store.StoreHalf.sp1_sb Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (cols : StoreHalfCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    store_prev_value, smph, smpl, smf, smdl, smdh,
                    ob1, ob0, store_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, StoreHalfCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

end SP1Clean.StoreHalf
