import SP1Clean.Chips.Memory.LoadDoubleChip

/-! # Cols-level Sail helpers for `LoadDoubleChip` (Sail-isolation layer)

The Sail-monadic content for `LoadDouble` lives here, quarantined out of the
pure-Clean `LoadDoubleChip.lean`. Mirrors `SP1Clean/Chips/ALU/AddChip/Cols.lean`'s
cols-level Sail-side helpers + round-trip lemmas. Consumed only by
`LoadDoubleSailBridge.lean`, which lifts SP1's
`_root_.Load.LoadDouble.correct_ld` to a cols-parameterized equivalence.

Splitting this off keeps `LoadDoubleChip.lean` free of `open Sail`/`SailM`, so the
chip's Clean circuit + `FormalSpec` + soundness/completeness are pure-Clean and the
Sail equivalence is a thin, on-demand bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

@[reducible] def sp1_op_a_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_imm_c_cols (cols : LoadDoubleCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

/-- The chip's monadic `sp1_ld` projected off `LoadDoubleCols` fields
directly. Mirrors `_root_.Load.LoadDouble.sp1_ld Main` exactly on
`fromMain Main` (closes by `rfl` thanks to `@[reducible]`). -/
@[reducible] def sp1_ld_cols (cols : LoadDoubleCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)] + 4)
  Sail.write_reg op_a (Word.toBitVec64 cols.load_prev_value)
  return RETIRE_SUCCESS

/-- The cols-level initial-state precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. (Same shape as `SP1Clean.Add.addInitialState_cols`.) -/
def loadDoubleInitialState_cols (cols : LoadDoubleCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 39, fromMain Main = cols →
    (_root_.Load.LoadDouble.constraints Main).initialState s

/-! ### Round-trip lemmas (`<helper>_cols (fromMain Main) = _root_.Load.LoadDouble.<helper> Main`). -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_a_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_b_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_ob_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_imm_c_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_ld_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_ld_cols (fromMain Main) = _root_.Load.LoadDouble.sp1_ld Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real` (the UserMode
TrustMode marker — `fromMain` aliases `is_trusted := Main[38] = is_real`). -/
lemma fromMain_toMain (cols : LoadDoubleCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    load_prev_value, lmph, lmpl, lmf, lmdl, lmdh,
                    is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, LoadDoubleCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

end SP1Clean.LoadDouble
