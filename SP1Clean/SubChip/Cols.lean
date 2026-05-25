import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Sub.SubChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.SubOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `SubChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.Sub`: defines the `SubCols` column
struct (mirroring SP1's Rust `SubCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `SubCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_sub_cols`, `subInitialState_cols`).

NOTE: this directory currently uses namespace `SP1Clean.Sub` (matching
the module path) to coexist with the legacy single-file
`SP1Clean/SubChip.lean` whose namespace is `SP1Clean.Sub`. Once that file
is deleted, this namespace can be renamed to `SP1Clean.Sub` to match the
AddChip convention.

Mirrors the `SP1Clean.Add` template 1-for-1 (RType reader, opcode 2 swapping
in for opcode 0). Row width: **33** (`is_real = Main[32]`).

Imported (in order) by:
- `SP1Clean.Sub.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.Sub.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.Sub.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `SubCols<T, M: TrustMode>`.
Identical in shape to `SP1Clean.Add.AddCols`. -/
@[ext]
structure SubCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `SubCols` view. Mirrors the
index map in `SP1Chips/Sub/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[32]` (= `is_real`). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : SubCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   Main[32],
   ⟨Main[32]⟩⟩

/-- Right inverse of `fromMain`: pack a `SubCols` into a 33-element flat row
using the same index map as `fromMain`. -/
@[reducible] def toMain (cols : SubCols (ZMod p)) : Vector (ZMod p) 33 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0],
     cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2],
     cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0,
     cols.adapter.op_b,
     cols.adapter.op_b_memory.prev_value[0],
     cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2],
     cols.adapter.op_b_memory.prev_value[3],
     cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c,
     cols.adapter.op_c_memory.prev_value[0],
     cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2],
     cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.op_a_write_value[0], cols.op_a_write_value[1],
     cols.op_a_write_value[2], cols.op_a_write_value[3],
     cols.is_real]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : SubCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_sub_cols (cols : SubCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def subInitialState_cols (cols : SubCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 33, fromMain Main = cols →
    (_root_.Sub.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_a_cols (fromMain Main) = _root_.Sub.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_b_cols (fromMain Main) = _root_.Sub.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_op_c_cols (fromMain Main) = _root_.Sub.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_sub_cols_fromMain (Main : Vector (ZMod p) 33) :
    sp1_sub_cols (fromMain Main) = _root_.Sub.sp1_sub Main := rfl

/-! ## Chip-level `FormalSpec`

Mirrors `SP1Clean.Add.FormalSpec` swapping `AddOp` → `SubOp`, opcode `0`
→ `2`, `RV64.add` → `RV64.sub`. The pure BitVec `RV64.sub` semantic is the
trailing conjunct (conditional on `is_real = 1`); the monadic Sail
equivalence to `_root_.Sub.spec_sub` is recovered externally via
`sail_correct_of_formalSpec` in `SailBridge.lean`. The standalone
`is_real * (is_real - 1) = 0` binary gate is absorbed into both
`CPUState.Gated.Assertion.Spec` and `RTypeReader.Gated.Assertion.Spec`'s
first conjuncts (redundant but propositionally fine). -/
def FormalSpec (cols : SubCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.SubOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 2, cols.state.pc,
       cols.op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.toBitVec64 cols.op_a_write_value =
      RV64.sub (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
               (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Sub
