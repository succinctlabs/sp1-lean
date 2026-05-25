import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Mul.MulChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `MulChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.MulChip`: defines the `MulCols` column
struct, `fromMain`/`toMain` projections, cols-level Sail-side helpers,
and `FormalSpec`.

Row width **82**, R-type reader, opcode
`is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24`,
5 variants (MUL/MULH/MULHU/MULHSU/MULW).
`is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`.

Cols struct mirrors Rust `MulCols<T>`:
- state, adapter (RTypeReader)
- a_word (op_a_write_value), carry (16 limbs), product (16 limbs)
- b_lower_byte.low_bytes (4), c_lower_byte.low_bytes (4)
- b_msb, c_msb, product_msb.msb, b_sign_extend, c_sign_extend
- 5 selectors, adapter_cols

NOTE: namespace `SP1Clean.MulChip` (not `SP1Clean.Mul`) to coexist with
the legacy single-file `SP1Clean/MulChip.lean`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `MulCols<T, M: TrustMode>`. -/
@[ext]
structure MulCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  a_word : Vector T 4
  carry : Vector T 16
  product : Vector T 16
  b_low_bytes : Vector T 4
  c_low_bytes : Vector T 4
  b_msb : T
  c_msb : T
  product_msb : T
  b_sign_extend : T
  c_sign_extend : T
  is_mul : T
  is_mulh : T
  is_mulhu : T
  is_mulhsu : T
  is_mulw : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `MulCols` view. Mirrors
`SP1Chips/Mul/Common.lean`'s `allHold_constraints_iff` destructuring. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 82) : MulCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   #v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
      Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
      Main[46], Main[47]],
   #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
      Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
      Main[62], Main[63]],
   #v[Main[64], Main[65], Main[66], Main[67]],
   #v[Main[68], Main[69], Main[70], Main[71]],
   Main[72], Main[73], Main[74], Main[75], Main[76],
   Main[77], Main[78], Main[79], Main[80], Main[81],
   ⟨Main[77] + Main[78] + Main[79] + Main[80] + Main[81]⟩⟩

/-- Right inverse of `fromMain`. -/
@[reducible] def toMain (cols : MulCols (ZMod p)) : Vector (ZMod p) 82 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0],
     cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2],
     cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0, cols.adapter.op_b,
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
     cols.a_word[0], cols.a_word[1], cols.a_word[2], cols.a_word[3],
     cols.carry[0], cols.carry[1], cols.carry[2], cols.carry[3],
     cols.carry[4], cols.carry[5], cols.carry[6], cols.carry[7],
     cols.carry[8], cols.carry[9], cols.carry[10], cols.carry[11],
     cols.carry[12], cols.carry[13], cols.carry[14], cols.carry[15],
     cols.product[0], cols.product[1], cols.product[2], cols.product[3],
     cols.product[4], cols.product[5], cols.product[6], cols.product[7],
     cols.product[8], cols.product[9], cols.product[10], cols.product[11],
     cols.product[12], cols.product[13], cols.product[14], cols.product[15],
     cols.b_low_bytes[0], cols.b_low_bytes[1], cols.b_low_bytes[2], cols.b_low_bytes[3],
     cols.c_low_bytes[0], cols.c_low_bytes[1], cols.c_low_bytes[2], cols.c_low_bytes[3],
     cols.b_msb, cols.c_msb, cols.product_msb,
     cols.b_sign_extend, cols.c_sign_extend,
     cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : MulCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_mul_cols (cols : MulCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.a_word)

/-- Cols-level state-bus precondition. -/
def mulInitialState_cols (cols : MulCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 82, fromMain Main = cols →
    (_root_.Mul.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 82) :
    sp1_op_a_cols (fromMain Main) = _root_.Mul.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 82) :
    sp1_op_b_cols (fromMain Main) = _root_.Mul.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 82) :
    sp1_op_c_cols (fromMain Main) = _root_.Mul.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_mul_cols_fromMain (Main : Vector (ZMod p) 82) :
    sp1_mul_cols (fromMain Main) = _root_.Mul.sp1_mul_chip Main := rfl

/-! ## Chip-level `FormalSpec`

Composes `MulOp.Spec`, `cpuStateSpec`, `rtypeReaderSpec`, the 7 trailing
scalar gates (5 selector binaries + sum binary + op_a_0), and the 5
per-variant RV64 BitVec semantic equations (`RV64.mul`/`.mulh`/`.mulhu`/
`.mulhsu`/`.mulw`, each conditional on its selector being 1). The
opcode used inside `rtypeReaderSpec` links the selectors to the RV64
dispatch on the constraint side; the trailing RV64 conjuncts are the
semantic image of that opcode dispatch (one selector ⇒ one RV64 op).
Mirror of Add's `is_real = 1 → RV64.add …` conjunct
(`SP1Clean/AddChip/Cols.lean:204-207`), 5-way for the 5 selectors. -/
def FormalSpec (cols : MulCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_real : ZMod p :=
    cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw
  let opcode : ZMod p :=
    cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 +
    cols.is_mulhsu * 14 + cols.is_mulw * 24
  let bw : BitVec 64 := Word.toBitVec64 cols.adapter.op_b_memory.prev_value
  let cw : BitVec 64 := Word.toBitVec64 cols.adapter.op_c_memory.prev_value
  let aw : BitVec 64 := Word.toBitVec64 cols.a_word
  SP1Clean.MulOp.Spec
      ⟨cols.a_word,
       cols.adapter.op_b_memory.prev_value,
       cols.adapter.op_c_memory.prev_value,
       cols.carry, cols.product,
       cols.b_low_bytes, cols.c_low_bytes,
       cols.b_msb, cols.c_msb, cols.product_msb,
       cols.b_sign_extend, cols.c_sign_extend,
       cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw⟩ ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec clk_low opcode cols.state.pc
      cols.a_word cols.adapter ∧
  cols.is_mul * (cols.is_mul - 1) = 0 ∧
  cols.is_mulh * (cols.is_mulh - 1) = 0 ∧
  cols.is_mulhu * (cols.is_mulhu - 1) = 0 ∧
  cols.is_mulhsu * (cols.is_mulhsu - 1) = 0 ∧
  cols.is_mulw * (cols.is_mulw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_mul    = 1 → aw = RV64.mul    cw bw) ∧
  (cols.is_mulh   = 1 → aw = RV64.mulh   cw bw) ∧
  (cols.is_mulhu  = 1 → aw = RV64.mulhu  cw bw) ∧
  (cols.is_mulhsu = 1 → aw = RV64.mulhsu cw bw) ∧
  (cols.is_mulw   = 1 → aw = RV64.mulw   cw bw)

end SP1Clean.MulChip
