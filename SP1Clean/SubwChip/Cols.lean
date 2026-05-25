import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Subw.SubwChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.SubwOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `SubwChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.Subw`: defines the `SubwCols` column
struct, `fromMain`/`toMain` projections, and cols-level Sail-side helpers.

**Important divergence from `AddwChip`:** Subw uses `RTypeReader`, NOT
`ALUTypeReader`. There is no `SUBIW` pseudo-instruction in RV64I, so the
chip has a single variant (SUBW only). Row width: **32** (one less than
AddwChip's 36, due to the missing `op_c` 4-limb immediate slot and
`imm_c` column). `is_real = Main[31]`. Opcode index `20` (SUBW).

The 32-bit result is stored as 2 limbs (`Main[28..29]`) plus a `subw_msb`
column (`Main[30]`). The 4-limb `op_a_write_value` fed into RTypeReader
is reconstructed as `[subw_value[0], subw_value[1], subw_msb * 65535,
subw_msb * 65535]` (sign-extension).

Mirrors the `SP1Clean.Subw` template 1-for-1 (RType reader, opcode 20). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `SubwCols<T, M: TrustMode>`. -/
@[ext]
structure SubwCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  subw_value : Vector T 2
  subw_msb : T
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `SubwCols` view. Mirrors
`SP1Chips/Subw/Constraints.lean`'s index map: state[0..5], RTypeReader's
operand-register triple [6..27], subw_value[28..29], subw_msb[30],
is_real[31]. `adapter_cols.is_trusted` aliases `Main[31]`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 32) : SubwCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29]],
   Main[30], Main[31],
   ⟨Main[31]⟩⟩

/-- Right inverse of `fromMain`: pack a `SubwCols` into a 32-element flat row. -/
@[reducible] def toMain (cols : SubwCols (ZMod p)) : Vector (ZMod p) 32 :=
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
     cols.subw_value[0], cols.subw_value[1],
     cols.subw_msb,
     cols.is_real]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : SubwCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_subw_cols (cols : SubwCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64 #v[cols.subw_value[0], cols.subw_value[1],
                        cols.subw_msb * 65535, cols.subw_msb * 65535])

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def subwInitialState_cols (cols : SubwCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 32, fromMain Main = cols →
    (_root_.Subw.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_a_cols (fromMain Main) = _root_.Subw.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_b_cols (fromMain Main) = _root_.Subw.sp1_op_b Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_op_c_cols (fromMain Main) = _root_.Subw.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_subw_cols_fromMain (Main : Vector (ZMod p) 32) :
    sp1_subw_cols (fromMain Main) = _root_.Subw.sp1_subw Main := rfl

/-! ## Chip-level `FormalSpec`

The unified chip Spec, lifted here from `Circuit.lean` so `Lemmas.lean`
can reference it without importing the full circuit construction:
SUBW carry-chain arithmetic (`SubwOp.Spec`, Inputs-shape) plus the
flag-threaded sub-circuit composition (`CPUState.Gated` +
`RTypeReader.Gated`, opcode 20) plus the chip-level `op_a_0 = 0` gate
plus a pure BitVec `RV64.subw` semantic (conditional on `is_real = 1`).
The free `is_real * (is_real - 1) = 0` gate now lives inside both
Gated.Specs' first conjuncts. Mirrors `SP1Clean/SubChip/Cols.lean`'s
`FormalSpec` with the W-style sign-extended result shape
(`#v[value[0], value[1], msb*65535, msb*65535]`). -/
def FormalSpec (cols : SubwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let op_a_write_value : Word (ZMod p) :=
    #v[cols.subw_value[0], cols.subw_value[1],
       cols.subw_msb * 65535, cols.subw_msb * 65535]
  SP1Clean.SubwOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      { value := cols.subw_value, msb := { msb := cols.subw_msb } } ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 20, cols.state.pc,
       op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.toBitVec64 op_a_write_value =
      RV64.subw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Subw
