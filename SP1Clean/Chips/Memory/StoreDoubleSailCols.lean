import SP1Clean.Chips.Memory.StoreDoubleChip

/-! # Cols-level Sail helpers for `StoreDoubleChip` (Sail-isolation layer)

The Sail-monadic content for `StoreDouble` lives here, quarantined out of the
pure-Clean `StoreDoubleChip.lean`. Mirrors `SP1Clean/Chips/ALU/AddChip/Cols.lean`'s
cols-level Sail-side helpers + round-trip lemmas. Consumed only by
`StoreDoubleSailBridge.lean`, which lifts SP1's
`_root_.Store.StoreDouble.correct` to a cols-parameterized equivalence.

Splitting this off keeps `StoreDoubleChip.lean` free of `open Sail`/`SailM`, so the
chip's Clean circuit + `FormalSpec` + soundness/completeness are pure-Clean and the
Sail equivalence is a thin, on-demand bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.StoreDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Cols-level Sail helpers + structural bridge (Phase 3 SailBridge prep)

Mirror of `SP1Clean.LoadDouble`'s Phase 2 helpers, swapping Load → Store
semantics. `_root_.Store.StoreDouble.spec_sb` is the Sail-side reference
(SP1Chips's misleading `sb` name — the helper is actually for SD width 8).
The `sp1_sb` projector reads from `Main[7..10]` (the op_a register value)
and writes via `Sail.ConcurrencyInterfaceV1.write_ram`. -/

@[reducible] def sp1_op_a_cols (cols : StoreDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : StoreDoubleCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

/-- For StoreDouble, the immediate is decoded from the 4-limb `op_c_imm`
via `Word.toNat`, not just `Main[21].val` (cf. `_root_.Store.StoreDouble.sp1_imm_c`). -/
@[reducible] def sp1_imm_c_cols (cols : StoreDoubleCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat cols.adapter.op_c_imm)

/-- The chip's monadic `sp1_sb` (a.k.a. SD) projected off `StoreDoubleCols`
fields directly. Mirrors `_root_.Store.StoreDouble.sp1_sb Main` on
`fromMain Main` (closes by `rfl` thanks to `@[reducible]`). -/
@[reducible] def sp1_sb_cols (cols : StoreDoubleCols (ZMod p)) :
    SailM ExecutionResult := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64
      #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)])
  let addr : BitVec 64 := Word.toBitVec64
    #v[cols.addr_value[0], cols.addr_value[1], cols.addr_value[2], (0 : ZMod p)]
  Sail.ConcurrencyInterfaceV1.write_ram 64 8 0#64 addr
    (Word.toBitVec64 cols.adapter.op_a_memory.prev_value)
  return RETIRE_SUCCESS

/-- The cols-level initial-state precondition: universally lifted over any
flat `Main` row that re-projects to the given `cols`. Same shape as
`SP1Clean.LoadDouble.loadDoubleInitialState_cols`. -/
def storeDoubleInitialState_cols (cols : StoreDoubleCols (ZMod p))
    (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 39, fromMain Main = cols →
    (_root_.Store.StoreDouble.constraints Main).initialState s

/-! ### Round-trip lemmas (`<helper>_cols (fromMain Main) = _root_.Store.StoreDouble.<helper> Main`). -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_a_cols (fromMain Main) = _root_.Store.StoreDouble.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_op_b_cols (fromMain Main) = _root_.Store.StoreDouble.sp1_ob_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_imm_c_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_imm_c_cols (fromMain Main) = _root_.Store.StoreDouble.sp1_imm_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_sb_cols_fromMain (Main : Vector (ZMod p) 39) :
    sp1_sb_cols (fromMain Main) = _root_.Store.StoreDouble.sp1_sb Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real` (the UserMode
TrustMode marker — `fromMain` aliases `is_trusted := Main[38] = is_real`). -/
lemma fromMain_toMain (cols : StoreDoubleCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addr_value, addr_top_two_limb_inv,
                    store_prev_value, smph, smpl, smf, smdl, smdh,
                    is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, StoreDoubleCols.ext_iff, CPUState.ext_iff, ITypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

end SP1Clean.StoreDouble
