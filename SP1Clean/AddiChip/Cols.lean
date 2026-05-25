import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Chips.Addi.AddiChip
import SP1Clean.Reader.CPUState
import SP1Clean.TrustMode

/-! # `AddiChip` cols-level surface

Entry-point module for `SP1Clean.AddiChip`: defines the `AddiCols` column
struct (mirroring SP1's Rust `AddiCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `AddiCols` view, and the `cols`-level Sail-side
helpers (`sp1_op_{a,b,c}_cols`, `sp1_addi_cols`, `addiInitialState_cols`)
that mirror `_root_.Addi`'s Main-level definitions but project off
`AddiCols` fields directly.

Imported (in order) by:
- `SP1Clean.AddiChip.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.AddiChip.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.AddiChip.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge.

The aggregator `SP1Clean.AddiChip` re-exports all four. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddiCols<T, M: TrustMode>`.
The `adapter_cols : UserModeReaderCols T` slot is the last field, matching
Rust under `M = UserMode`. We don't carry an explicit `M` type parameter on
the struct because `deriving ProvableStruct` can't reduce through an abstract
`M`; future SupervisorMode chips would use a separate `*ColsSupervisor`
struct with `adapter_cols : EmptyCols T`. -/
@[ext]
structure AddiCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `AddiCols` view. Mirrors the
index map in `SP1Chips/Addi/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[29]` (= `is_real`) because the current extractor passes
`Main[29] Main[29]` to `ITypeReader.constraints`. When upstream regen lands
a separate `is_trusted` Main column, switch to that index. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 30) : AddiCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29],
   ⟨Main[29]⟩⟩

/-- Right inverse of `fromMain`: pack an `AddiCols` into a 30-element flat
row using the same index map as `fromMain`. Index 29 (= `is_real`) is also
the `adapter_cols.is_trusted` slot, matching `fromMain`'s aliasing (so the
round-trip lemma requires `cols.adapter_cols.is_trusted = cols.is_real`,
which is the chip's `Assumptions`). -/
@[reducible] def toMain (cols : AddiCols (ZMod p)) : Vector (ZMod p) 30 :=
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
     cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
     cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3],
     cols.op_a_write_value[0], cols.op_a_write_value[1],
     cols.op_a_write_value[2], cols.op_a_write_value[3],
     cols.is_real]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.Addi.sp1_op_{a,b,c}` and `_root_.Addi.sp1_addi`
projections directly off `AddiCols` fields. Each helper is `@[reducible]` so
the round-trip lemma `<helper>_cols (fromMain Main) = Addi.<helper> Main`
closes by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : AddiCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : AddiCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

/-- The I-type 12-bit immediate, decoded from limb 0 of `op_c_imm`. Mirrors
`_root_.Addi.sp1_op_c` which uses `Main[21].val`. -/
@[reducible] def sp1_op_c_cols (cols : AddiCols (ZMod p)) : BitVec 12 :=
  BitVec.ofNat 12 cols.adapter.op_c_imm[0].val

def sp1_addi_cols (cols : AddiCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

/-- The cols-level state-bus precondition for the per-row Sail clause:
universally lifted over any flat `Main` row that re-projects to the given
`cols`. Stated this way (rather than directly via `toMain cols`) so we
don't depend on a `fromMain (toMain cols) = cols` round-trip, which fails
by `rfl` due to `Vector` not having structural eta. Downstream consumers
that have `cols` in hand can specialize with `Main := toMain cols` (using
`SP1Clean.AddiChip.Lemmas.fromMain_toMain`). -/
def addiInitialState_cols (cols : AddiCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 30, fromMain Main = cols →
    (_root_.Addi.constraints Main).initialState s

/-! ### Round-trip lemmas

Each `cols`-level helper equals the corresponding `Main`-level def when
applied to `fromMain Main`. All hold by `rfl` thanks to `@[reducible]`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_a_cols (fromMain Main) = _root_.Addi.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_b_cols (fromMain Main) = _root_.Addi.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_op_c_cols (fromMain Main) = _root_.Addi.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_addi_cols_fromMain (Main : Vector (ZMod p) 30) :
    sp1_addi_cols (fromMain Main) = _root_.Addi.sp1_addi Main := rfl

end SP1Clean.Addi
