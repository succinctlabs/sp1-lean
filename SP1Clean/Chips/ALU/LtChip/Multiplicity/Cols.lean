import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Lt.LtChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Operations.GatedLtSignedOp
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `LtChip` cols-level surface (directory-form scaffold)

Entry-point module for `SP1Clean.LtChip`: defines the `LtCols` column
struct, `fromMain`/`toMain` projections, cols-level Sail-side helpers,
and `FormalSpec`.

Row width **44**, ALU-type reader, opcode `is_slt·9 + is_sltu·10`,
4 variants (SLT, SLTU, SLTI, SLTIU). `is_real = is_slt + is_sltu`.

The cols struct mirrors the SP1 `LtCols<T>` Rust struct:
- `state : CPUState T`
- `adapter : ALUTypeReader T`
- The `LtOperationSigned` cols (embedded inline as separate fields):
  - `compare_bit : T` (= cols.result.u16_compare_operation.bit, Main[34])
  - `u16_flags : Vector T 4` (Main[35..38])
  - `not_eq_inv : T` (Main[39])
  - `comparison_limbs : Vector T 2` (Main[40..41])
  - `b_msb : T` (Main[42])
  - `c_msb : T` (Main[43])
- `is_slt : T` (Main[32])
- `is_sltu : T` (Main[33])
- `adapter_cols : UserModeReaderCols T`

NOTE: namespace `SP1Clean.LtChip` (not `SP1Clean.Lt`) to coexist with
the legacy single-file `SP1Clean/LtChip.lean`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `LtCols<T, M: TrustMode>`. -/
@[ext]
structure LtCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  compare_bit : T
  u16_flags : Vector T 4
  not_eq_inv : T
  comparison_limbs : Vector T 2
  b_msb : T
  c_msb : T
  is_slt : T
  is_sltu : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LtCols` view. Mirrors the
index map from `SP1Chips/Lt/Common.lean`'s `allHold_constraints_iff_*`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : LtCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   Main[34],
   #v[Main[35], Main[36], Main[37], Main[38]],
   Main[39],
   #v[Main[40], Main[41]],
   Main[42], Main[43],
   Main[32], Main[33],
   ⟨Main[32] + Main[33]⟩⟩

/-- Right inverse of `fromMain`: pack an `LtCols` into a 44-element flat row. -/
@[reducible] def toMain (cols : LtCols (ZMod p)) : Vector (ZMod p) 44 :=
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
     cols.is_slt, cols.is_sltu,
     cols.compare_bit,
     cols.u16_flags[0], cols.u16_flags[1], cols.u16_flags[2], cols.u16_flags[3],
     cols.not_eq_inv,
     cols.comparison_limbs[0], cols.comparison_limbs[1],
     cols.b_msb, cols.c_msb]

/-! ## Cols-level Sail-side helpers -/

@[reducible] def sp1_op_a_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : LtCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c[0].val

def sp1_lt_cols (cols : LtCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 #v[cols.compare_bit, 0, 0, 0])

/-- Cols-level state-bus precondition. -/
def ltInitialState_cols (cols : LtCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 44, fromMain Main = cols →
    (_root_.Lt.constraints Main).initialState s

/-! ### Round-trip lemmas -/

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_a_cols (fromMain Main) = _root_.Slt.sp1_op_a Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_b_cols (fromMain Main) = _root_.Slt.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_c_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_op_c_cols (fromMain Main) = _root_.Slt.sp1_op_c Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_lt_cols_fromMain (Main : Vector (ZMod p) 44) :
    sp1_lt_cols (fromMain Main) = _root_.Lt.sp1_lt Main := rfl

/-! ## Chip-level `FormalSpec`

The unified chip Spec, structured as a flat conjunction of facts about
`cols`, one per sub-circuit emission in `main` (plus 4 scalar gates):

- `GatedLtSignedOp.Assertion.FormalSpec` — comparison arithmetic on the
  64-bit operands. Carries its own `gate = 0 ∨ <byte-range + carry>`
  disjunction; gate is `is_slt + is_sltu`.
- `CPUState.Gated.Assertion.Spec` — flag-threaded CPUState assertion
  (binary gate + state-bus + byte-opcode, all gated by `is_real`).
- `ALUTypeReader.Gated.Assertion.Spec` — program + 3 OperandAccess +
  imm_c switch, gated by `is_real`/`is_trusted`.
- 2 selector binaries (`is_slt`, `is_sltu` ∈ {0, 1}), the `is_real`
  sum-binary disjunction, and `op_a_0 = 0`.

No BitVec `RV64.slt`/`RV64.sltu` semantic clauses live here — bridging
the byte-level facts to the BitVec semantic would require going through
`LtOperationSigned.spec.signed`/`.unsigned` (SP1Operations side) via an
`iff_sp1` translation, which is exactly the legacy bridge we are
avoiding. Chip consumers that need the BitVec semantic derive it
externally (e.g. via a separate `sail_correct_*` theorem). -/
def FormalSpec (cols : LtCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_real : ZMod p := cols.is_slt + cols.is_sltu
  let op_a_write_value : Word (ZMod p) := #v[cols.compare_bit, 0, 0, 0]
  SP1Clean.GatedLtSignedOp.Assertion.FormalSpec
      ⟨cols.adapter.op_b_memory.prev_value,
       cols.adapter.op_c_memory.prev_value,
       cols.is_slt,
       cols.compare_bit, cols.u16_flags, cols.not_eq_inv,
       cols.comparison_limbs,
       cols.b_msb, cols.c_msb,
       is_real⟩ ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low,
       cols.is_slt * 9 + cols.is_sltu * 10, cols.state.pc,
       op_a_write_value, cols.adapter,
       is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (is_real = 0 ∨ is_real - 1 = 0) ∧
  cols.adapter.op_a_0 = 0

end SP1Clean.LtChip
