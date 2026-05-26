import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Bitwise.BitwiseChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `BitwiseChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.BitwiseChip`: defines the `BitwiseCols`
column struct, `fromMain`/`toMain` projections, and cols-level Sail-side
helpers.

The Bitwise chip is a fan-out chip covering **6 variants** (XOR/OR/AND ×
R/I), distinguished by the shared `ALUTypeReader`'s `imm_c` flag and a
three-way one-hot selector `(is_xor, is_or, is_and)`. Row width: **51**.
`is_real = is_xor + is_or + is_and` is the row's "this row participates"
indicator and must sum to 1.

The 8-byte AND/OR/XOR result lives in `bitwise_operation.bitwise_operation.result`
(`Main[40..47]`); the 4-limb u16 reconstruction `[a+b*256, c+d*256, e+f*256,
g+h*256]` is what gets written to `op_a`.

NOTE: this directory uses namespace `SP1Clean.BitwiseChip` to coexist
with the legacy single-file `SP1Clean/BitwiseChip.lean` whose namespace
is `SP1Clean.Bitwise`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `BitwiseCols<T, M: TrustMode>`. -/
@[ext]
structure BitwiseCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  bitwise_operation : BitwiseU16Operation T
  is_xor : T
  is_or : T
  is_and : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `BitwiseCols` view. Mirrors
`SP1Chips/Bitwise/Constraints.lean`'s index map. `adapter_cols.is_trusted`
aliases the aggregate `is_real` sum `Main[48] + Main[49] + Main[50]`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 51) : BitwiseCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   ⟨⟨#v[Main[32], Main[33], Main[34], Main[35]]⟩,
    ⟨#v[Main[36], Main[37], Main[38], Main[39]]⟩,
    ⟨#v[Main[40], Main[41], Main[42], Main[43],
        Main[44], Main[45], Main[46], Main[47]]⟩⟩,
   Main[48], Main[49], Main[50],
   ⟨Main[48] + Main[49] + Main[50]⟩⟩

/-- Right inverse of `fromMain`: pack a `BitwiseCols` into a 51-element flat row. -/
@[reducible] def toMain (cols : BitwiseCols (ZMod p)) : Vector (ZMod p) 51 :=
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
     cols.adapter.op_c[0], cols.adapter.op_c[1],
     cols.adapter.op_c[2], cols.adapter.op_c[3],
     cols.adapter.op_c_memory.prev_value[0],
     cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2],
     cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.imm_c,
     cols.bitwise_operation.b_low_bytes.low_bytes[0],
     cols.bitwise_operation.b_low_bytes.low_bytes[1],
     cols.bitwise_operation.b_low_bytes.low_bytes[2],
     cols.bitwise_operation.b_low_bytes.low_bytes[3],
     cols.bitwise_operation.c_low_bytes.low_bytes[0],
     cols.bitwise_operation.c_low_bytes.low_bytes[1],
     cols.bitwise_operation.c_low_bytes.low_bytes[2],
     cols.bitwise_operation.c_low_bytes.low_bytes[3],
     cols.bitwise_operation.bitwise_operation.result[0],
     cols.bitwise_operation.bitwise_operation.result[1],
     cols.bitwise_operation.bitwise_operation.result[2],
     cols.bitwise_operation.bitwise_operation.result[3],
     cols.bitwise_operation.bitwise_operation.result[4],
     cols.bitwise_operation.bitwise_operation.result[5],
     cols.bitwise_operation.bitwise_operation.result[6],
     cols.bitwise_operation.bitwise_operation.result[7],
     cols.is_xor, cols.is_or, cols.is_and]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : BitwiseCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def sp1_bitwise_cols (cols : BitwiseCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  let res := cols.bitwise_operation.bitwise_operation.result
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a
    (Word.toBitVec64 #v[res[0] + res[1] * 256, res[2] + res[3] * 256,
                        res[4] + res[5] * 256, res[6] + res[7] * 256])

/-- The cols-level state-bus precondition for the per-row Sail clause. -/
def bitwiseInitialState_cols (cols : BitwiseCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 51, fromMain Main = cols →
    (_root_.Bitwise.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 51) :
    sp1_op_a_cols (fromMain Main) = _root_.Xor.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 51) :
    sp1_op_b_cols (fromMain Main) = _root_.Xor.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 51) :
    sp1_op_c_cols (fromMain Main) = _root_.Xor.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_bitwise_cols_fromMain (Main : Vector (ZMod p) 51) :
    sp1_bitwise_cols (fromMain Main) = _root_.Bitwise.sp1_bitwise Main := rfl

/-! ## Chip-level `FormalSpec`

Mirrors the legacy single-file's `TraceSpec` shape:
- A propositional clause for the `BitwiseU16Operation` sub-fragment
  (no Clean wrapper yet — would compose `SP1Clean.BitwiseU16Op.assertion`
  once written; currently inlined as `List.Forall SP1Constraint.toProp`).
- CPU-state byte bounds.
- Full ALU-type reader spec (covers ProgramTable + 3 OperandAccess +
  imm_c switch).
- Boolean disjunctions on the 3 opcode selectors + their sum + `op_a_0`. -/
def FormalSpec (cols : BitwiseCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode_bw : ZMod p := cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0
  let is_real : ZMod p := cols.is_xor + cols.is_or + cols.is_and
  let ret_val : Word (ZMod p) :=
    (BitwiseU16Operation.constraints (F := ZMod p)
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.bitwise_operation opcode_bw is_real).1
  List.Forall SP1Constraint.toProp
    (BitwiseU16Operation.constraints (F := ZMod p)
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.bitwise_operation opcode_bw is_real).2 ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec clk_low
      (cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5)
      cols.state.pc ret_val cols.adapter ∧
  (cols.is_xor = 0 ∨ cols.is_xor = 1) ∧
  (cols.is_or = 0 ∨ cols.is_or = 1) ∧
  (cols.is_and = 0 ∨ cols.is_and = 1) ∧
  (is_real = 0 ∨ is_real - 1 = 0) ∧
  cols.adapter.op_a_0 = 0

end SP1Clean.BitwiseChip
