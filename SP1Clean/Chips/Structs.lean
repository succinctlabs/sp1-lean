import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.Reader.CPUState
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.TrustMode

/-! # Unified chip column structures

Central audit point for every IN-USE chip's `<X>Cols` struct and its
`fromMain`/`toMain` projections. Mirrors SP1's Rust per-chip `*Cols<T, M>`
under `M = UserMode`. Each chip's `Cols.lean` / `Aggregate.lean` /
single-file imports this and provides the chip-local Sail helpers and
`FormalSpec` (see `SP1Clean.Chips.Spec`).

Organization mirrors `SP1Clean/Chips/` directory layout:
ALU → Control → Memory. WIP redesigns under `Multiplicity/` define their
own parallel structs in-folder and are not unified here. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## ALU chips -/

namespace SP1Clean.Add

/-- The chip's column struct, mirroring SP1's Rust `AddCols<T, M: TrustMode>`
(`sp1/crates/core/machine/src/alu/add_sub/add.rs:47-62`). The
`adapter_cols : UserModeReaderCols T` slot is the last field, matching Rust
under `M = UserMode`. We don't carry an explicit `M` type parameter on the
struct because `deriving ProvableStruct` can't reduce through an abstract
`M`; future SupervisorMode chips would use a separate `*ColsSupervisor`
struct with `adapter_cols : EmptyCols T`. -/
@[ext]
structure AddCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `AddCols` view. Mirrors the
index map in `SP1Chips/Add/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[32]` (= `is_real`) because the current extractor passes
`Main[32] Main[32]` to `RTypeReader.constraints` (see
`SP1Chips/Add/Constraints.lean:21`). When upstream regen lands a separate
`is_trusted` Main column, switch to that index. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : AddCols (ZMod p) :=
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

/-- Right inverse of `fromMain`: pack an `AddCols` into a 33-element flat
row using the same index map as `fromMain`. Used internally by the
`sail_correct_of_formalSpec` bridge (see `SP1Clean.AddChip.SailBridge`) to
recover a `Main` satisfying `fromMain Main = cols`. Index 32 (= `is_real`)
is also the `adapter_cols.is_trusted` slot, matching `fromMain`'s aliasing
(so the round-trip lemma requires `cols.adapter_cols.is_trusted = cols.is_real`,
which is the chip's `Assumptions`). -/
@[reducible] def toMain (cols : AddCols (ZMod p)) : Vector (ZMod p) 33 :=
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

end SP1Clean.Add

namespace SP1Clean.Addi

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

end SP1Clean.Addi

namespace SP1Clean.Addw

/-- The chip's column struct, mirroring SP1's Rust `AddwCols<T, M: TrustMode>`.
The `adapter_cols : UserModeReaderCols T` slot is the last field, matching
Rust under `M = UserMode`. -/
@[ext]
structure AddwCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  addw_value : Vector T 2
  addw_msb : T
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `AddwCols` view. Mirrors the
index map in `SP1Chips/Addw/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[35]` (= `is_real`) because the current extractor passes
`Main[35] Main[35]` to `ALUTypeReader.constraints`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 36) : AddwCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33]],
   Main[34],
   Main[35],
   ⟨Main[35]⟩⟩

/-- Right inverse of `fromMain`: pack an `AddwCols` into a 36-element flat
row using the same index map as `fromMain`. Index 35 (= `is_real`) is also
the `adapter_cols.is_trusted` slot. -/
@[reducible] def toMain (cols : AddwCols (ZMod p)) : Vector (ZMod p) 36 :=
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
     cols.adapter.op_c[0], cols.adapter.op_c[1],
     cols.adapter.op_c[2], cols.adapter.op_c[3],
     cols.adapter.op_c_memory.prev_value[0],
     cols.adapter.op_c_memory.prev_value[1],
     cols.adapter.op_c_memory.prev_value[2],
     cols.adapter.op_c_memory.prev_value[3],
     cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.imm_c,
     cols.addw_value[0], cols.addw_value[1],
     cols.addw_msb,
     cols.is_real]

end SP1Clean.Addw

namespace SP1Clean.Sub

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

end SP1Clean.Sub

namespace SP1Clean.Subw

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

end SP1Clean.Subw

namespace SP1Clean.UType

/-- The chip's column struct, mirroring SP1's Rust `UTypeCols<T, M: TrustMode>`.
`addend` is the conditional `is_auipc * pc` carried into the AddOperation,
and `add_result` is the 64-bit AddOp output written to op_a. -/
@[ext]
structure UTypeCols (T : Type) where
  state : CPUState T
  adapter : JTypeReader T
  addend : Vector T 3
  add_result : Vector T 4
  is_auipc : T
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `UTypeCols` view. Mirrors
the index map in `SP1Chips/UType/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[30]` (= `is_real`) because the current extractor passes
`Main[30] Main[30]` to `JTypeReader.constraints`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 31) : UTypeCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    #v[Main[14], Main[15], Main[16], Main[17]],
    #v[Main[18], Main[19], Main[20], Main[21]]⟩,
   #v[Main[22], Main[23], Main[24]],
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29], Main[30],
   ⟨Main[30]⟩⟩

/-- Right inverse of `fromMain`: pack a `UTypeCols` into a 31-element flat
row using the same index map as `fromMain`. Slot 30 carries both `is_real`
and `adapter_cols.is_trusted` (matching `fromMain`'s aliasing), so the
round-trip lemma requires `cols.adapter_cols.is_trusted = cols.is_real`. -/
@[reducible] def toMain (cols : UTypeCols (ZMod p)) : Vector (ZMod p) 31 :=
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
     cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
     cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3],
     cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
     cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3],
     cols.addend[0], cols.addend[1], cols.addend[2],
     cols.add_result[0], cols.add_result[1],
     cols.add_result[2], cols.add_result[3],
     cols.is_auipc, cols.is_real]

end SP1Clean.UType

namespace SP1Clean.Bitwise

/-- The chip's column struct, mirroring SP1's Rust `BitwiseCols<T>`. -/
structure BitwiseCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  bitwise_operation : BitwiseU16Operation T
  is_xor : T
  is_or : T
  is_and : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `BitwiseCols` view. -/
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
    ⟨#v[Main[40], Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47]]⟩⟩,
   Main[48], Main[49], Main[50],
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[48]+Main[49]+Main[50]`), matching upstream's ALUTypeReader
   -- receiving the same sum for both `is_real` and `is_trusted`.
   ⟨Main[48] + Main[49] + Main[50]⟩⟩

end SP1Clean.Bitwise

namespace SP1Clean.Mul

/-- The chip's column struct, mirroring SP1's Rust `MulCols<T>` over
82 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Mul/Constraints.lean`. The struct groups the 16-limb carry
and product vectors into `Vector T 16` fields; the `U16toU8OperationSafe`
sub-fragments are inlined as `Vector T 4` (the SP1 struct's
`low_bytes` field). -/
structure MulCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4             -- Main[28..31] (== mul_operation.product[0..3])
  -- Phase 3c: MulOperation (45 cells) nested as a single field, replacing
  -- the previous 5 flat fields (carry:16, product:16, b_low_bytes:4,
  -- c_low_bytes:4, mul_aux_bits:5). The 5-field `mul_aux_bits` collapse
  -- (which existed to keep the struct under the 33-field ProvableStruct
  -- elaboration ceiling) is no longer needed; MulOperation's 9 nested
  -- fields naturally expose b_msb/c_msb/product_msb/b_sign_extend/c_sign_extend
  -- without flattening.
  mul_operation : MulOperation T            -- Main[32..76]
  -- Slot order matches upstream's `MulCols<T, M>` field declaration order in
  -- alu/mul/mod.rs (is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw). The
  -- previous Lean order put is_mulw at Main[79] and is_mulhu at Main[81] —
  -- bug: the constraint compiler emits the Rust struct order, so the Lean
  -- destructure was reading upstream's is_mulhu as is_mulw (and vice versa).
  -- Opcode mux `is_mulw * 13 + is_mulhu * 24` then dispatched the wrong
  -- variants. Fixed 2026-05-23.
  is_mul : T                                -- Main[77]
  is_mulh : T                               -- Main[78]
  is_mulhu : T                              -- Main[79]
  is_mulhsu : T                             -- Main[80]
  is_mulw : T                               -- Main[81]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `MulCols` view.
82 columns; `carry : Vector T 16`, `product : Vector T 16`,
`b_low_bytes/c_low_bytes : Vector T 4`, `mul_aux_bits : Vector T 5`
packed from contiguous Main slots. -/
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
   ⟨#v[Main[32], Main[33], Main[34], Main[35], Main[36], Main[37], Main[38],
       Main[39], Main[40], Main[41], Main[42], Main[43], Main[44], Main[45],
       Main[46], Main[47]],
    #v[Main[48], Main[49], Main[50], Main[51], Main[52], Main[53], Main[54],
       Main[55], Main[56], Main[57], Main[58], Main[59], Main[60], Main[61],
       Main[62], Main[63]],
    ⟨#v[Main[64], Main[65], Main[66], Main[67]]⟩,
    ⟨#v[Main[68], Main[69], Main[70], Main[71]]⟩,
    Main[72], Main[73], ⟨Main[74]⟩, Main[75], Main[76]⟩,
   Main[77], Main[78], Main[79], Main[80], Main[81],
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[77]+...+Main[81]`), matching the upstream RTypeReader receiving
   -- `E3 E3` (is_real, is_trusted) where `E3` is that sum.
   ⟨Main[77] + Main[78] + Main[79] + Main[80] + Main[81]⟩⟩

end SP1Clean.Mul

namespace SP1Clean.ShiftLeft

/-- The chip's column struct, mirroring SP1's Rust `ShiftLeftCols<T>`
over 65 field elements. The non-reader columns are grouped into named
Vector blocks where SP1's emission already treats them as a unit
(`c_bits`, `shift_u16`, `shifted_limbs`, `result`). -/
structure ShiftLeftCols (T : Type) where
  state : CPUState T
  -- Nested ALUTypeReader (Main[6..31]). `op_c : Word T` (4 limbs) and
  -- `imm_c : T` are part of this adapter, matching upstream's
  -- `adapter: ALUTypeReader<T>` field count + ordering. Replaces the
  -- prior 9-field inlining + 3 misnamed `shift_imm_low/shift_imm_high/msb`
  -- padding cells; see `SP1Chips/ShiftLeft/Constraints.lean:215` (the
  -- CS2 line that uses `op_c := #v[Main[21..24]]` and `imm_c := Main[31]`).
  adapter : ALUTypeReader T
  -- The 4-limb shifted result (committed to op_a register).
  result : Vector T 4                       -- Main[32..35]
  -- 6-bit decomposition of the shift amount mod 64 (Main[36..41]).
  c_bits : Vector T 6                       -- Main[36..41]
  -- Shift-power intermediates (Main[42..44]). Upstream Rust names these
  -- as three named scalars (`v_01, v_012, v_0123`) rather than a 3-vector.
  -- Phase 2.3 decomposition (open-question #4): split for name alignment.
  v_01 : T                                  -- Main[42] (was shift_pow[0])
  v_012 : T                                 -- Main[43] (was shift_pow[1])
  v_0123 : T                                -- Main[44] (was shift_pow[2])
  -- One-hot byte-shift selector over 4 byte positions (Main[45..48]).
  shift_u16 : Vector T 4                    -- Main[45..48]
  -- Shifted-limb intermediates (Main[49..56]). Upstream Rust names the
  -- two halves as `lower_limb: Word<T>` and `higher_limb: Word<T>`.
  -- Phase 2.3 decomposition (open-question #4): split the 8-vector.
  lower_limb : Vector T 4                   -- Main[49..52] (was limb_shift[0..3])
  higher_limb : Vector T 4                  -- Main[53..56] (was limb_shift[4..7])
  -- Intermediate result columns (Main[57..61]). Upstream Rust splits this
  -- into `limb_result: Word<T>` (4 cells) and `sllw_msb: U16MSBOperation<T>`
  -- (1 cell, the MSB witness for SLLW sign-extension fed to U16MSBOperation
  -- in the bridge — see CS0 in SP1Chips/ShiftLeft/Constraints.lean).
  -- Phase 2.3 decomposition (open-question #4): split the 5-vector.
  limb_result : Vector T 4                  -- Main[57..60] (was result_intermediate[0..3])
  sllw_msb : U16MSBOperation T              -- Main[61] (was result_intermediate[4])
  is_sll : T                                -- Main[62]
  is_sllw : T                               -- Main[63]
  -- Renamed from `sign_extend` to upstream's `is_sllw_imm` (Phase 2.3).
  -- Bridge: Main[64] = Main[63] * Main[31] = is_sllw * imm_c = is_slliw.
  is_sllw_imm : T                           -- Main[64] (was sign_extend)
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `ShiftLeftCols` view.
65 columns. Post-Phase-2.3 decomposition: `v_01/v_012/v_0123` are scalars
(Main[42..44]), `lower_limb`/`higher_limb` split the former 8-vector
(Main[49..56]), `limb_result`+`sllw_msb` split the former 5-vector
(Main[57..61]), and `is_sllw_imm` replaces the old `sign_extend`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 65) : ShiftLeftCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33], Main[34], Main[35]],
   #v[Main[36], Main[37], Main[38], Main[39], Main[40], Main[41]],
   Main[42], Main[43], Main[44],
   #v[Main[45], Main[46], Main[47], Main[48]],
   #v[Main[49], Main[50], Main[51], Main[52]],
   #v[Main[53], Main[54], Main[55], Main[56]],
   #v[Main[57], Main[58], Main[59], Main[60]],
   { msb := Main[61] },
   Main[62], Main[63], Main[64],
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[62]+Main[63]`).
   ⟨Main[62] + Main[63]⟩⟩

end SP1Clean.ShiftLeft

namespace SP1Clean.ShiftRight

structure ShiftRightCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  op_a_write_value : Vector T 4             -- Main[32..35] (= upstream `a : Word<T>`)
  -- Phase 3e: aux:28 decomposed into 11 named upstream sub-fields.
  -- Slot mapping verified against `SP1Chips/ShiftRight/Constraints.lean`
  -- (the U16MSBOperation calls at lines 191-197 pin Main[36]/[37], the
  -- bit-boolean asserts pin Main[38..43], the shift-pow chain E124-E135
  -- pins Main[45..47], the limb arithmetic pins Main[48..63]).
  b_msb : U16MSBOperation T                 -- Main[36]
  srw_msb : U16MSBOperation T               -- Main[37]
  c_bits : Vector T 6                       -- Main[38..43]
  sra_msb_v0123 : T                         -- Main[44]
  v_0123 : T                                -- Main[45]
  v_012 : T                                 -- Main[46]
  v_01 : T                                  -- Main[47]
  lower_limb : Vector T 4                   -- Main[48..51]
  higher_limb : Vector T 4                  -- Main[52..55]
  limb_result : Vector T 4                  -- Main[56..59]
  shift_u16 : Vector T 4                    -- Main[60..63]
  is_srl : T                                -- Main[64]
  is_sra : T                                -- Main[65]
  is_srlw : T                               -- Main[66]
  is_sraw : T                               -- Main[67]
  -- `is_w_imm = (is_srlw + is_sraw) * imm_c` (forced by bridge E47).
  -- Matches upstream's `is_w_imm: T` in `alu/sr/mod.rs:104`; the
  -- prior Lean name `sign_extend` was a misnomer — this is a
  -- W-variant immediate flag (used in opcode adjustment), not a
  -- sign-extension witness.
  is_w_imm : T                              -- Main[68] (was sign_extend)
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `ShiftRightCols` view.
69 columns; `intermediates_aux : Vector T 28` packed from Main[36..63]. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 69) : ShiftRightCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩,
   #v[Main[32], Main[33], Main[34], Main[35]],
   ⟨Main[36]⟩,                          -- b_msb : U16MSBOperation
   ⟨Main[37]⟩,                          -- srw_msb : U16MSBOperation
   #v[Main[38], Main[39], Main[40], Main[41], Main[42], Main[43]],  -- c_bits
   Main[44],                            -- sra_msb_v0123
   Main[45],                            -- v_0123
   Main[46],                            -- v_012
   Main[47],                            -- v_01
   #v[Main[48], Main[49], Main[50], Main[51]],  -- lower_limb
   #v[Main[52], Main[53], Main[54], Main[55]],  -- higher_limb
   #v[Main[56], Main[57], Main[58], Main[59]],  -- limb_result
   #v[Main[60], Main[61], Main[62], Main[63]],  -- shift_u16
   Main[64], Main[65], Main[66], Main[67], Main[68],
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[64]+Main[65]+Main[66]+Main[67]`).
   ⟨Main[64] + Main[65] + Main[66] + Main[67]⟩⟩

end SP1Clean.ShiftRight

namespace SP1Clean.Lt

/-- The chip's column struct, mirroring SP1's Rust `LtCols<T>`. -/
structure LtCols (T : Type) where
  state : CPUState T
  adapter : ALUTypeReader T
  is_slt : T
  is_sltu : T
  lt_operation : LtOperationSigned T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LtCols` view. Mirrors
the index map in `SP1Chips/Lt/Constraints.lean` (44 columns; the
`lt_operation` sub-struct is packed from `Main[34..43]`). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : LtCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]],
    ⟨#v[Main[25], Main[26], Main[27], Main[28]], ⟨Main[29], Main[30]⟩⟩,
    Main[31]⟩, Main[32], Main[33],
   { result :=
       { u16_compare_operation := { bit := Main[34] },
         u16_flags := #v[Main[35], Main[36], Main[37], Main[38]],
         not_eq_inv := Main[39],
         comparison_limbs := #v[Main[40], Main[41]] },
     b_msb := { msb := Main[42] },
     c_msb := { msb := Main[43] } },
   -- `adapter_cols.is_trusted` aliases the aggregate is_real sum
   -- (`Main[32]+Main[33]`), matching upstream's ALUTypeReader receiving
   -- the same sum for both `is_real` and `is_trusted`.
   ⟨Main[32] + Main[33]⟩⟩

end SP1Clean.Lt

namespace SP1Clean.DivRem

/-- Sub-record bundling the 14 named fields of upstream `DivRemCols`'s
"post-MulOperation" intermediates (Main[166..240]). Nested into `DivRemCols`
to keep the top-level field count tractable for `deriving ProvableStruct`
(the auto-deriver bails on flat structs with >~25 fields). -/
structure DivRemAuxPost (T : Type) where
  c_neg_operation : AddOperation T          -- Main[166..169]
  rem_neg_operation : AddOperation T        -- Main[170..173]
  remainder_lt_operation : LtOperationUnsigned T  -- Main[174..181]
  carry : Vector T 8                        -- Main[182..189]
  is_c_0 : IsZeroWordOperation T            -- Main[190..200]
  -- 8 one-hot mode flags (Main[201..208]): is_div, is_divu, is_rem,
  -- is_remu, is_divw, is_remw, is_divuw, is_remuw in declaration order.
  mode_flags : Vector T 8                   -- Main[201..208]
  is_overflow : T                           -- Main[209]
  is_overflow_b : IsEqualWordOperation T    -- Main[210..220]
  is_overflow_c : IsEqualWordOperation T    -- Main[221..231]
  b_msb : U16MSBOperation T                 -- Main[232]
  rem_msb : U16MSBOperation T               -- Main[233]
  c_msb : U16MSBOperation T                 -- Main[234]
  quot_msb : U16MSBOperation T              -- Main[235]
  -- Five single-bit flags (Main[236..240]): b_neg, b_neg_not_overflow,
  -- b_not_neg_not_overflow, is_real_not_word, rem_neg in order.
  neg_flags : Vector T 5                    -- Main[236..240]
deriving ProvableStruct

/-- The chip's column struct. The 246 columns mirror upstream
`DivRemCols<T, M>` declaration order (alu/divrem/mod.rs:58-200). The 14
aux_post fields are bundled into a `DivRemAuxPost` sub-record so the
total field count stays inside what `deriving ProvableStruct` can
chain-coerce. -/
structure DivRemCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4             -- Main[28..31] (= upstream `a : Word<T>`)
  -- Phase 3f: aux_pre:44 fully decomposed into 10 named upstream sub-fields.
  b : Vector T 4                            -- Main[32..35]
  c : Vector T 4                            -- Main[36..39]
  quotient : Vector T 4                     -- Main[40..43]
  quotient_comp : Vector T 4                -- Main[44..47]
  remainder_comp : Vector T 4               -- Main[48..51]
  remainder : Vector T 4                    -- Main[52..55]
  abs_remainder : Vector T 4                -- Main[56..59]
  abs_c : Vector T 4                        -- Main[60..63]
  max_abs_c_or_1 : Vector T 4               -- Main[64..67]
  c_times_quotient : Vector T 8             -- Main[68..75]
  c_times_quotient_lower : MulOperation T   -- Main[76..120]
  c_times_quotient_upper : MulOperation T   -- Main[121..165]
  aux_post : DivRemAuxPost T                -- Main[166..240], decomposed in sub-record
  -- Main[241..245]: per-mode multiplicity flags (Rust DivRemCols layout).
  -- The 3-flag (is_signed, is_w, is_rem) labels these previously carried
  -- were a mode-encoding placeholder that got out of sync with upstream
  -- — Rust has the 8-flag one-hot at Main[201..208] (see mode_flags in
  -- DivRemAuxPost) and reserves these cells for sub-operation multiplicity.
  c_neg : T                                 -- Main[241] (sign-flip flag for c)
  abs_c_alu_event : T                       -- Main[242] (mult arg to c_neg AddOp)
  abs_rem_alu_event : T                     -- Main[243] (mult arg to rem_neg AddOp)
  is_real : T                               -- Main[244]
  remainder_check_multiplicity : T          -- Main[245] (mult arg to remainder_lt_op)
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `DivRemCols` view. 246 columns,
all fields named per the upstream `DivRemCols<T, M>` declaration order. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 246) : DivRemCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   -- aux_pre[44]: 10 Word/Vector fields at Main[32..75].
   #v[Main[32], Main[33], Main[34], Main[35]],   -- b
   #v[Main[36], Main[37], Main[38], Main[39]],   -- c
   #v[Main[40], Main[41], Main[42], Main[43]],   -- quotient
   #v[Main[44], Main[45], Main[46], Main[47]],   -- quotient_comp
   #v[Main[48], Main[49], Main[50], Main[51]],   -- remainder_comp
   #v[Main[52], Main[53], Main[54], Main[55]],   -- remainder
   #v[Main[56], Main[57], Main[58], Main[59]],   -- abs_remainder
   #v[Main[60], Main[61], Main[62], Main[63]],   -- abs_c
   #v[Main[64], Main[65], Main[66], Main[67]],   -- max_abs_c_or_1
   #v[Main[68], Main[69], Main[70], Main[71],
      Main[72], Main[73], Main[74], Main[75]],   -- c_times_quotient
   -- c_times_quotient_lower (45 cells: Main[76..120])
   { carry := #v[Main[76], Main[77], Main[78], Main[79], Main[80], Main[81], Main[82],
                 Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89],
                 Main[90], Main[91]],
     product := #v[Main[92], Main[93], Main[94], Main[95], Main[96], Main[97], Main[98],
                   Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105],
                   Main[106], Main[107]],
     b_lower_byte := ⟨#v[Main[108], Main[109], Main[110], Main[111]]⟩,
     c_lower_byte := ⟨#v[Main[112], Main[113], Main[114], Main[115]]⟩,
     b_msb := Main[116], c_msb := Main[117],
     product_msb := ⟨Main[118]⟩,
     b_sign_extend := Main[119], c_sign_extend := Main[120] },
   -- c_times_quotient_upper (45 cells: Main[121..165])
   { carry := #v[Main[121], Main[122], Main[123], Main[124], Main[125], Main[126], Main[127],
                 Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134],
                 Main[135], Main[136]],
     product := #v[Main[137], Main[138], Main[139], Main[140], Main[141], Main[142], Main[143],
                   Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150],
                   Main[151], Main[152]],
     b_lower_byte := ⟨#v[Main[153], Main[154], Main[155], Main[156]]⟩,
     c_lower_byte := ⟨#v[Main[157], Main[158], Main[159], Main[160]]⟩,
     b_msb := Main[161], c_msb := Main[162],
     product_msb := ⟨Main[163]⟩,
     b_sign_extend := Main[164], c_sign_extend := Main[165] },
   -- aux_post (Main[166..240]) : DivRemAuxPost (14 fields)
   { c_neg_operation := ⟨#v[Main[166], Main[167], Main[168], Main[169]]⟩,
     rem_neg_operation := ⟨#v[Main[170], Main[171], Main[172], Main[173]]⟩,
     remainder_lt_operation :=
       { u16_compare_operation := ⟨Main[174]⟩,
         u16_flags := #v[Main[175], Main[176], Main[177], Main[178]],
         not_eq_inv := Main[179],
         comparison_limbs := #v[Main[180], Main[181]] },
     carry := #v[Main[182], Main[183], Main[184], Main[185],
                 Main[186], Main[187], Main[188], Main[189]],
     is_c_0 :=
       { is_zero_limb := #v[⟨Main[190], Main[191]⟩, ⟨Main[192], Main[193]⟩,
                            ⟨Main[194], Main[195]⟩, ⟨Main[196], Main[197]⟩],
         is_zero_first_half := Main[198],
         is_zero_second_half := Main[199],
         result := Main[200] },
     mode_flags := #v[Main[201], Main[202], Main[203], Main[204],
                      Main[205], Main[206], Main[207], Main[208]],
     is_overflow := Main[209],
     is_overflow_b :=
       { is_diff_zero :=
           { is_zero_limb := #v[⟨Main[210], Main[211]⟩, ⟨Main[212], Main[213]⟩,
                                ⟨Main[214], Main[215]⟩, ⟨Main[216], Main[217]⟩],
             is_zero_first_half := Main[218],
             is_zero_second_half := Main[219],
             result := Main[220] } },
     is_overflow_c :=
       { is_diff_zero :=
           { is_zero_limb := #v[⟨Main[221], Main[222]⟩, ⟨Main[223], Main[224]⟩,
                                ⟨Main[225], Main[226]⟩, ⟨Main[227], Main[228]⟩],
             is_zero_first_half := Main[229],
             is_zero_second_half := Main[230],
             result := Main[231] } },
     b_msb := ⟨Main[232]⟩, rem_msb := ⟨Main[233]⟩,
     c_msb := ⟨Main[234]⟩, quot_msb := ⟨Main[235]⟩,
     neg_flags := #v[Main[236], Main[237], Main[238], Main[239], Main[240]] },
   -- Legacy 3-flag labels (Main[241..245]).
   Main[241], Main[242], Main[243], Main[244], Main[245],
   ⟨Main[244]⟩⟩

end SP1Clean.DivRem

/-! ## Control chips -/

namespace SP1Clean.Branch

/-- The chip's column struct, mirroring SP1's Rust `BranchCols<T>`. -/
structure BranchCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  next_pc : Vector T 3                      -- Main[25..27]
  is_beq : T                                -- Main[28]
  is_bne : T                                -- Main[29]
  is_blt : T                                -- Main[30]
  is_bge : T                                -- Main[31]
  is_bltu : T                               -- Main[32]
  is_bgeu : T                               -- Main[33]
  -- Main[34] mirrors upstream's `is_branching: T` — forced equal under `is_real`
  -- to `is_beq*(b==c) + is_bne*(b!=c) + (is_bge+is_bgeu)*(b>=c) + (is_blt+is_bltu)*(b<c)`
  -- by the bridge's E94/E96 assertZeros. The previous Lean name `lt_is_signed`
  -- was a misnomer: this column is NOT the `is_signed` arg to LtOperationSigned
  -- (which is `is_blt + is_bge`); it is the branch-taken predicate output.
  is_branching : T                          -- Main[34] (Rust-aligned name)
  compare_operation : LtOperationSigned T   -- Main[35..44]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `BranchCols` view.
45 columns; `compare_operation : LtOperationSigned T` packed from
Main[35..44]. Note: `is_branching` at Main[34] *is* on the row
(Rust-aligned name; previously misnamed `lt_is_signed`). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 45) : BranchCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28], Main[29], Main[30], Main[31], Main[32], Main[33],
   Main[34],
   { result :=
       { u16_compare_operation := { bit := Main[35] },
         u16_flags := #v[Main[36], Main[37], Main[38], Main[39]],
         not_eq_inv := Main[40],
         comparison_limbs := #v[Main[41], Main[42]] },
     b_msb := { msb := Main[43] },
     c_msb := { msb := Main[44] } },
   ⟨Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33]⟩⟩

end SP1Clean.Branch

namespace SP1Clean.Jal

/-- The chip's column struct, mirroring SP1's Rust `JalCols<T>` over
31 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Jal/Constraints.lean`. -/
structure JalCols (T : Type) where
  state : CPUState T
  adapter : JTypeReader T
  next_pc : Vector T 4                      -- Main[22..25] (jump target, Main[25] is high limb)
  op_a_write_value : Vector T 4             -- Main[26..29] (return address = pc + 4)
  is_real : T                               -- Main[30]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `JalCols` view. Mirrors
the index map in `SP1Chips/Jal/Constraints.lean` (31 columns). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 31) : JalCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    #v[Main[14], Main[15], Main[16], Main[17]],
    #v[Main[18], Main[19], Main[20], Main[21]]⟩,
   #v[Main[22], Main[23], Main[24], Main[25]],
   #v[Main[26], Main[27], Main[28], Main[29]],
   Main[30],
   ⟨Main[30]⟩⟩

/-- Right inverse of `fromMain`: pack a `JalCols` into a 31-element flat
row using the same index map as `fromMain`. Slot 30 carries both `is_real`
and `adapter_cols.is_trusted` (matching `fromMain`'s aliasing), so the
round-trip lemma requires `cols.adapter_cols.is_trusted = cols.is_real`. -/
@[reducible] def toMain (cols : JalCols (ZMod p)) : Vector (ZMod p) 31 :=
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
     cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
     cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3],
     cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
     cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3],
     cols.next_pc[0], cols.next_pc[1], cols.next_pc[2], cols.next_pc[3],
     cols.op_a_write_value[0], cols.op_a_write_value[1],
     cols.op_a_write_value[2], cols.op_a_write_value[3],
     cols.is_real]

end SP1Clean.Jal

namespace SP1Clean.Jalr

/-- The chip's column struct, mirroring SP1's Rust `JalrCols<T>`. -/
structure JalrCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  is_real : T
  jump_target : Vector T 4
  op_a_write_value : Vector T 4
  lsb : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `JalrCols` view. Mirrors
the index map in `SP1Chips/Jalr/Constraints.lean` (35 columns). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 35) : JalrCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   Main[25],
   #v[Main[26], Main[27], Main[28], Main[29]],
   #v[Main[30], Main[31], Main[32], Main[33]],
   Main[34],
   ⟨Main[25]⟩⟩

end SP1Clean.Jalr

/-! ## Memory chips -/

namespace SP1Clean.LoadByte

/-- The chip's column struct, mirroring SP1's Rust `LoadByteCols<T>` over
47 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Load/LoadByte/Constraints.lean`. -/
structure LoadByteCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27] (op_b + imm_c, low 3 limbs)
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32] (the 4-limb loaded word)
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  offset_bit_2 : T                     -- Main[38] (selects which of 8 bytes)
  offset_bit_1 : T                     -- Main[39]
  offset_bit_0 : T                      -- Main[40]
  selected_limb : T                         -- Main[41]
  selected_limb_low_byte : T                     -- Main[42]
  selected_byte : T                           -- Main[43] (the loaded byte value)
  signed_extension_flag : T                 -- Main[44] (1 if sign bit set, 0 otherwise)
  is_lb : T                                 -- Main[45]
  is_lbu : T                                -- Main[46]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LoadByteCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 47) : LoadByteCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44],
   Main[45], Main[46], ⟨Main[45] + Main[46]⟩⟩

end SP1Clean.LoadByte

namespace SP1Clean.LoadHalf

structure LoadHalfCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32]
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  offset_bit_1 : T                      -- Main[38] (sub-word selector, weight 2)
  offset_bit_0 : T                      -- Main[39] (sub-double selector, weight 4)
  op_a_write_value_lo : T                   -- Main[40] (selected 16-bit half)
  signed_extension_msb : T                  -- Main[41] (MSB for sign-extension)
  is_lh : T                                 -- Main[42]
  is_lhu : T                                -- Main[43]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LoadHalfCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : LoadHalfCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], Main[39], Main[40], Main[41], Main[42], Main[43],
   ⟨Main[42] + Main[43]⟩⟩

end SP1Clean.LoadHalf

namespace SP1Clean.LoadWord

structure LoadWordCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32]
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  offset_bit : T                      -- Main[38] (selects high vs low word in double)
  op_a_write_value_lo : Vector T 2          -- Main[39..40] (selected 32-bit word's two limbs)
  signed_extension_msb : T                  -- Main[41] (MSB for sign-extension)
  is_lw : T                                 -- Main[42]
  is_lwu : T                                -- Main[43]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LoadWordCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : LoadWordCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38],
   #v[Main[39], Main[40]],
   Main[41], Main[42], Main[43], ⟨Main[42] + Main[43]⟩⟩

end SP1Clean.LoadWord

namespace SP1Clean.LoadDouble

structure LoadDoubleCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32] (loaded doubleword)
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  is_real : T                               -- Main[38]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LoadDoubleCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 39) : LoadDoubleCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], ⟨Main[38]⟩⟩

end SP1Clean.LoadDouble

namespace SP1Clean.LoadX0

structure LoadX0Cols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32]
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  offset_bit : Vector T 3        -- Main[38..40] (byte-position selectors)
  is_lb : T                                 -- Main[41]
  is_lbu : T                                -- Main[42]
  is_lh : T                                 -- Main[43]
  is_lhu : T                                -- Main[44]
  is_lw : T                                 -- Main[45]
  is_lwu : T                                -- Main[46]
  is_ld : T                                 -- Main[47]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `LoadX0Cols` view.
Mirrors the index map in `SP1Chips/Load/LoadX0/Constraints.lean`
(48 columns). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 48) : LoadX0Cols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   #v[Main[38], Main[39], Main[40]],
   Main[41], Main[42], Main[43], Main[44], Main[45], Main[46], Main[47],
   ⟨Main[41] + Main[42] + Main[43] + Main[44] + Main[45] + Main[46] + Main[47]⟩⟩

end SP1Clean.LoadX0

namespace SP1Clean.StoreByte

/-- The chip's column struct, mirroring SP1's Rust `StoreByteCols<T>` over
50 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Store/StoreByte/Constraints.lean`. -/
structure StoreByteCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27] (computed store addr)
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32] (prior word at store addr)
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  byte_selector_top : T                     -- Main[38] (selects which byte half)
  byte_selector_mid : T                     -- Main[39]
  byte_selector_lo : T                      -- Main[40]
  mem_limb : T                         -- Main[41] (byte being stored)
  mem_limb_low_byte : T                     -- Main[42]
  register_low_byte : T                           -- Main[43] (the new byte at the offset)
  increment : T                     -- Main[44] (intermediate: combined byte at offset)
  store_value : Vector T 4            -- Main[45..48] (new 4-limb word)
  is_real : T                               -- Main[49]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `StoreByteCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 50) : StoreByteCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], Main[39], Main[40], Main[41], Main[42], Main[43], Main[44],
   #v[Main[45], Main[46], Main[47], Main[48]],
   Main[49], ⟨Main[49]⟩⟩

end SP1Clean.StoreByte

namespace SP1Clean.StoreHalf

structure StoreHalfCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32]
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  offset_bit_1 : T                   -- Main[38]
  offset_bit_0 : T                   -- Main[39]
  store_value : Vector T 4            -- Main[40..43]
  is_real : T                               -- Main[44]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `StoreHalfCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 45) : StoreHalfCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], Main[39],
   #v[Main[40], Main[41], Main[42], Main[43]],
   Main[44], ⟨Main[44]⟩⟩

end SP1Clean.StoreHalf

namespace SP1Clean.StoreWord

/-- The chip's column struct, mirroring SP1's Rust `StoreWordCols<T>`. -/
structure StoreWordCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32]
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  offset_bit : T                      -- Main[38]
  store_value : Vector T 4            -- Main[39..42]
  is_real : T                               -- Main[43]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `StoreWordCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 44) : StoreWordCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38],
   #v[Main[39], Main[40], Main[41], Main[42]],
   Main[43], ⟨Main[43]⟩⟩

end SP1Clean.StoreWord

namespace SP1Clean.StoreDouble

structure StoreDoubleCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32]
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  is_real : T                               -- Main[38]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `StoreDoubleCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 39) : StoreDoubleCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], ⟨Main[38]⟩⟩

end SP1Clean.StoreDouble

namespace SP1Clean.MemoryGlobal

/-- Column struct for the boundary memory chips, mirroring SP1's
`MemoryInitCols<T>` at
`crates/core/machine/src/memory/global.rs:256-298`. Used by both
`MemoryGlobalInit` and `MemoryGlobalFinalize` — the two chips share
column layouts and differ only in the interaction-kind they emit on
(Init: `MemoryGlobalInitControl` / kind 14; Finalize:
`MemoryGlobalFinalizeControl` / kind 15) and in the direction of the
address-monotonicity check.

The `lt_cols`, `is_prev_addr_zero`, `is_index_zero` sub-operation
fields are kept as opaque field-element placeholders here — Phase 4's
scope is the column shape, not the internal constraint structure.
A follow-up sub-iter will promote `MemoryGlobalCols` to a full
`FormalAssertion` that includes the `LtOperationUnsigned` and
`IsZeroOperation` sub-circuits properly. -/
structure MemoryGlobalCols (T : Type) where
  /-- Top bits of the timestamp of the memory access. -/
  clk_high : T
  /-- Low bits of the timestamp of the memory access. -/
  clk_low : T
  /-- The index of the memory access (within the boundary bus). -/
  index : T
  /-- The address of the previous memory access in the boundary chain. -/
  prev_addr : Vector T 3
  /-- The address of this memory access. -/
  addr : Vector T 3
  /-- Comparison columns for `prev_addr < addr` (LtOperationUnsigned
  layout in SP1; opaque placeholder here). 6 field elements. -/
  lt_cols : Vector T 6
  /-- The value of the memory access. -/
  value : Word T
  /-- Lower half of the third limb of `value`. -/
  value_lower : T
  /-- Upper half of the third limb of `value`. -/
  value_upper : T
  /-- Whether the memory access is a real access. -/
  is_real : T
  /-- Whether we are making the `prev_addr < addr` assertion. -/
  is_comp : T
  /-- Validity of the previous state. The unique invalid state is
  when the chip only initializes address 0 once. -/
  prev_valid : T
  /-- Witness for `is_prev_addr_zero` (IsZeroOperation layout in SP1;
  3 field elements as opaque placeholder). -/
  is_prev_addr_zero : Vector T 3
  /-- Witness for `is_index_zero` (IsZeroOperation layout in SP1;
  3 field elements as opaque placeholder). -/
  is_index_zero : Vector T 3
deriving ProvableStruct

end SP1Clean.MemoryGlobal
