import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.FormalModel.Contracts.DivRem
import SP1Clean.FormalModel.Contracts.DivRemColumns
import RISCV.Instructions
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Consolidated specs — chip rows, stated against the RV64 ISA functions

The `Inputs` structs and semantic `Spec`s for the chip rows (`GeneralFormalCircuit`s). Final file in
the `Specs/` sequence (`Reader → Operation → Chip`).

Unlike the operation gadgets — whose `Spec`s are spelled out as `BitVec` equations — each **chip**
states its headline meaning in terms of the corresponding **RV64 ISA function** from
`RISCV/Instructions.lean` (`RV64.add`/`RV64.sub`/`RV64.addw`/`RV64.subw`/`RV64.and`/`RV64.or`/
`RV64.xor`), since the opcode is statically known per chip. The operand order matches the RV64
signature `f rs2_val rs1_val` with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`.

For ADD/SUB/AND/OR/XOR the RV64 function is *definitionally* the `BitVec` op (`add rs2 rs1 := rs1 +
rs2`), so the chip soundness proofs carry over unchanged. For the W-instructions ADDW/SUBW the RV64
function truncates-then-sign-extends, related to the gadget's `setWidth 32`/`signExtend` form by the
`rv64_addw_eq` / `rv64_subw_eq` lemmas below. -/


namespace SP1Clean.AddChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native Add-chip row.  Its arithmetic block follows the local Lean gadget, not Rust's
`AddOperation` type.  `Faithful.AddChip.reconfigure` is the explicit whole-chip bridge to the
extracted `AddCols` oracle.  The reader blocks remain layout-compatible while that migration proceeds. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
  add_operation : AddOperation.Columns F
deriving ProvableStruct

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (the committed
CPUState + register-adapter columns the chip reads). The `rs1`/`rs2` source operands are **not** separate
committed columns — they are projected from the adapter's register slots (`op_b_val`/`op_c_val` below), so
the chip's operand is *definitionally* the value the Memory bus pins. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1` source operand = the register read on the `op_b` memory slot (the value the Memory bus pins,
`op_b_memory.prev_value`). Projecting it from the adapter — rather than carrying a redundant top-level
`op_b_val` column — makes the chip's operand definitionally the register-read value, so the Sail bridge's
`rs1` read is grounded by the Memory bus with no added equality constraint. `@[reducible]` so proofs that
manipulate the adapter slot see through it. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The `rs2` source operand = the register read on the `op_c` memory slot (`op_c_memory.prev_value`). -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Semantic contract, composed from the sub-circuits' own `Spec`s. The three conjuncts: the
`RTypeReader` reader sub-`Spec` on the `state`/`adapter` blocks, the *proven* `is_real`-binary fact,
and the `is_real`-gated arithmetic meaning — on real rows the result column is the RV64 `ADD` of the
operands (`RV64.add op_c_val op_b_val = op_b_val + op_c_val`). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 0,
      wv0 := cols.add_operation.value[0], wv1 := cols.add_operation.value[1],
      wv2 := cols.add_operation.value[2], wv3 := cols.add_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = RV64.add (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.AddChip

namespace SP1Clean.AddiChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native Addi-chip row.  Its arithmetic block follows the local Lean gadget, not Rust's
`AddOperation` type.  `Faithful.addiChipReconfigure` is the explicit whole-chip bridge to the
extracted `AddiOracle.AddiCols` oracle.  The reader blocks remain the shared generated substrate. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  add_operation : AddOperation.Columns F
deriving ProvableStruct

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (the latter an
**I-type** `Extracted.ITypeReader` carrying the immediate). The `rs1` source operand and the immediate
are **not** separate committed columns — they are projected from the adapter (`op_b_val`/`op_c_val`
below), so the chip's operands are *definitionally* the values the reader pins. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
deriving ProvableStruct

/-- The `rs1` source operand = the register read on the `op_b` memory slot (the value the Memory bus pins,
`op_b_memory.prev_value`). Projecting it from the adapter — rather than carrying a redundant top-level
`op_b_val` column — makes the chip's operand definitionally the register-read value. `@[reducible]` so
proofs that manipulate the adapter slot see through it. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The second summand = the **immediate** word `op_c_imm` (the I-type analogue of the `rs2` read; *not* a
register read). Projected from the adapter rather than carried as a separate committed column. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

/-- Semantic contract, composed from the sub-circuits' own `Spec`s (inline because `Addi` reads the
**I-type** adapter): the `ITypeReader` sub-`Spec` on the `state`/`adapter`
blocks (gated by the `ADDI` opcode `1`, `wv* = add_operation.value`), the *proven* `is_real`-binary fact,
and the `is_real`-gated arithmetic meaning — on real rows the result column is the RV64 `ADD` of the
register operand and the immediate (`RV64.add op_c_val op_b_val = op_b_val + op_c_val`). Vacuous on
padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ITypeReader.Spec
    { cols := input.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := input.state.clk_high,
      clk_low := input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      pc := input.state.pc, opcode := 1,
      wv0 := cols.add_operation.value[0], wv1 := cols.add_operation.value[1],
      wv2 := cols.add_operation.value[2], wv3 := cols.add_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = RV64.add (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.AddiChip

namespace SP1Clean.SubChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- Native Sub-chip row. The reader blocks reuse the project substrate; only the arithmetic block is
owned by the local Lean gadget. `Faithful.SubChip.subChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
  sub_operation : SubOperation.Columns F
deriving ProvableStruct

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (as `AddChip`). The
`rs1`/`rs2` operands are projected from the adapter register slots — see `Inputs.op_b_val` below. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1`/`rs2` source operands = the register reads on the adapter's `op_b`/`op_c` memory slots (the
Memory-bus values), projected rather than carried as separate committed columns (see `AddChip`). -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Semantic contract, mirroring `AddChip` (the same three conjuncts, one `RTypeReader` sub-`Spec`).
The third conjunct: on real rows the result column is the RV64 `SUB` of the operands
(`RV64.sub op_c_val op_b_val = op_b_val - op_c_val`, the fixed `rs1 - rs2`
order — `SUB` is not commutative). -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 2,
      wv0 := cols.sub_operation.value[0], wv1 := cols.sub_operation.value[1],
      wv2 := cols.sub_operation.value[2], wv3 := cols.sub_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.sub_operation.value
      = RV64.sub (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.SubChip

namespace SP1Clean.AddwChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RV64 `ADDW` function equals the gadget's `signExtend 64 (setWidth 32 (rs1 + rs2))` form:
both truncate the operands to 32 bits, add, and sign-extend the low 32 bits to 64. -/
lemma rv64_addw_eq (x y : BitVec 64) :
    RV64.addw x y = (BitVec.setWidth 32 (y + x)).signExtend 64 := by
  simp only [RV64.addw, BitVec.add_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

/-- Native ADDW-chip row. The reader blocks reuse the project substrate; only the arithmetic block is
owned by the local Lean gadget (two witnessed low limbs + the composed sign-bit block).
`Faithful.AddwChip.addwChipReconfigure` is the sole bridge to Rust's separately generated whole-chip
row. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
  addw_operation : AddwOperation.Columns F
deriving ProvableStruct

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (ADDW's adapter is the
immediate-capable `ALUTypeReader`, unlike SUBW's `RTypeReader`). The
`rs1`/`rs2` operands are projected from the adapter register slots — see `Inputs.op_b_val` below. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- The `rs1`/`rs2` source operands = the register reads on the adapter's `op_b`/`op_c` memory slots (the
Memory-bus values, `op_b_memory.prev_value`/`op_c_memory.prev_value`). ADDW is register-register
(`imm_c = 0`), so `op_c_val` is the `rs2` read — projected rather than carried as a separate committed
column (cf. `SubwChip`/`AddChip`). `@[reducible]` so proofs see through to the adapter slots. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- The sign-extended W result word the reader writes for `rd`: the two low limbs `addw_operation.value`
plus the sign-fill `msb·0xFFFF` in the high two limbs (= the gadget's `AddwOperation.resultWord`). -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.addw_operation.value[0], cols.addw_operation.value[1],
     cols.addw_operation.msb.msb * 65535, cols.addw_operation.msb.msb * 65535]

/-- Semantic contract (inline for the **ALU** adapter, since ADDW's adapter is the immediate-capable
`ALUTypeReader`): the `ALUTypeReader` sub-`Spec` on the `state`/`adapter` blocks (opcode
`19`, `rd` write the sign-extended W result `resultWord`), the proven `is_real`-binary fact, and the
`is_real`-gated arithmetic meaning — on real rows the result word is the RV64 `ADDW` of the operands
(`RV64.addw op_c_val op_b_val` — the low-32 add sign-extended to 64). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ALUTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 19,
      wv0 := (resultWord cols)[0], wv1 := (resultWord cols)[1],
      wv2 := (resultWord cols)[2], wv3 := (resultWord cols)[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 (resultWord cols)
      = RV64.addw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.AddwChip

namespace SP1Clean.SubwChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RV64 `SUBW` function equals the gadget's `signExtend 64 (setWidth 32 (rs1 - rs2))` form. -/
lemma rv64_subw_eq (x y : BitVec 64) :
    RV64.subw x y = (BitVec.setWidth 32 (y - x)).signExtend 64 := by
  simp only [RV64.subw, BitVec.sub_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

/-- Native SUBW-chip row. The reader blocks reuse the project substrate; only the arithmetic block is
owned by the local Lean gadget (two witnessed low limbs + the composed sign-bit block).
`Faithful.SubwChip.subwChipReconfigure` is the sole bridge to Rust's separately generated whole-chip
row. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
  subw_operation : SubwOperation.Columns F
deriving ProvableStruct

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (as `SubChip`; SUBW's
adapter is the register `RTypeReader`). The `rs1`/`rs2` operands are projected — see `Inputs.op_b_val`. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1`/`rs2` source operands = the register reads on the adapter's `op_b`/`op_c` memory slots. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Semantic contract — the inlined R-type-with-readers contract (SUBW's opcode is `20`). The `op_a` write
value the reader carries is the **sign-extended** W result `[v0, v1, msb·65535, msb·65535]` (the gadget's
`SubwOperation.resultWord`), and the gated-arith conjunct is `toBitVec64 resultWord = RV64.subw op_c op_b`
(the low-32 subtract `rs1 - rs2` sign-extended; not commutative). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 20,
      wv0 := cols.subw_operation.value[0], wv1 := cols.subw_operation.value[1],
      wv2 := cols.subw_operation.msb.msb * 65535, wv3 := cols.subw_operation.msb.msb * 65535 } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 #v[cols.subw_operation.value[0], cols.subw_operation.value[1],
        cols.subw_operation.msb.msb * 65535, cols.subw_operation.msb.msb * 65535]
      = RV64.subw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.SubwChip

namespace SP1Clean.ShiftLeftChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (the committed
CPUState + ALU register-adapter columns the chip reads). The shift operand word (`rs1`, `op_b_val`) and
shift-amount source (`rs2`/immediate, `op_c_val`) are **adapter projections**, not committed columns; the
**variant flags** `is_sll`/`is_sllw`/`is_sllw_imm` are **witnessed `cols` columns** (read from `cols` in the
`Spec`, with `is_real = is_sll + is_sllw`), not `Inputs` fields. `ShiftLeft` uses the `ALUTypeReader`
because `op_c` may be an immediate (`SLLI`/`SLLIW`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- `rs1` operand = the `op_b` register read (`op_b_memory.prev_value`); the arithmetic C operand is
the `op_c_memory.prev_value` word returned by SP1's `ALUTypeReader.c()`. On immediate rows the reader
constraints bind this word to the decoded `adapter.op_c` shift amount. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Native ShiftLeft-chip row (Rust field order — the chip has no separate `is_real` column; the
real-row selector is `is_sll + is_sllw`). The reader blocks and the SLLW MSB block reuse the project
substrate (`Extracted.U16MSBOperation` is still a standalone generated module — the Branch/load
chip families compose the same gadget). `Faithful.shiftLeftChipReconfigure` is the sole bridge to
Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
  a : Word F
  c_bits : Vector F 6
  v_01 : F
  v_012 : F
  v_0123 : F
  shift_u16 : Vector F 4
  lower_limb : Word F
  higher_limb : Word F
  limb_result : Word F
  sllw_msb : Extracted.U16MSBOperation F
  is_sll : F
  is_sllw : F
  is_sllw_imm : F
deriving ProvableStruct

/-- The folded tail of the generated ShiftLeft `asserts` list, beginning immediately after the two
flag booleans and their combined boolean gate. This is a genuine proof boundary over the committed
chip row, not a claimed Rust operation. -/
def CoreSpec (cols : Columns (ZMod p)) : Prop :=
  let sll := cols.is_sll; let sllw := cols.is_sllw
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let s0 := cols.shift_u16[0]; let s1 := cols.shift_u16[1]
  let s2 := cols.shift_u16[2]; let s3 := cols.shift_u16[3]
  let byteShift := b4 + b5 * 2 * sll
  b0 * (b0 - 1) = 0 ∧ b1 * (b1 - 1) = 0 ∧ b2 * (b2 - 1) = 0 ∧
  b3 * (b3 - 1) = 0 ∧ b4 * (b4 - 1) = 0 ∧ b5 * (b5 - 1) = 0 ∧
  s0 * (byteShift - 0) = 0 ∧ s0 * (s0 - 1) = 0 ∧
  s1 * (byteShift - 1) = 0 ∧ s1 * (s1 - 1) = 0 ∧
  s2 * (byteShift - 2) = 0 ∧ s2 * (s2 - 1) = 0 ∧
  s3 * (byteShift - 3) = 0 ∧ s3 * (s3 - 1) = 0 ∧
  (sll + sllw) * ((s0 + s1 + s2 + s3) - 1) = 0 ∧
  cols.v_01 - (b0 + 1) * (b1 * 3 + 1) = 0 ∧
  cols.v_012 - cols.v_01 * (b2 * 15 + 1) = 0 ∧
  cols.v_0123 - cols.v_012 * (b3 * 255 + 1) = 0 ∧
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[2] * cols.v_0123
    - (cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[3] * cols.v_0123
    - (cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  cols.limb_result[0] - cols.lower_limb[0] * cols.v_0123 = 0 ∧
  cols.limb_result[1] - (cols.lower_limb[1] * cols.v_0123 + cols.higher_limb[0]) = 0 ∧
  cols.limb_result[2] - (cols.lower_limb[2] * cols.v_0123 + cols.higher_limb[1]) = 0 ∧
  cols.limb_result[3] - (cols.lower_limb[3] * cols.v_0123 + cols.higher_limb[2]) = 0 ∧
  sll * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  sll * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  sll * (s0 * (cols.a[2] - cols.limb_result[2])) = 0 ∧
  sll * (s0 * (cols.a[3] - cols.limb_result[3])) = 0 ∧
  sll * (s1 * cols.a[0]) = 0 ∧
  sll * (s1 * (cols.a[1] - cols.limb_result[0])) = 0 ∧
  sll * (s1 * (cols.a[2] - cols.limb_result[1])) = 0 ∧
  sll * (s1 * (cols.a[3] - cols.limb_result[2])) = 0 ∧
  sll * (s2 * cols.a[0]) = 0 ∧
  sll * (s2 * cols.a[1]) = 0 ∧
  sll * (s2 * (cols.a[2] - cols.limb_result[0])) = 0 ∧
  sll * (s2 * (cols.a[3] - cols.limb_result[1])) = 0 ∧
  sll * (s3 * cols.a[0]) = 0 ∧
  sll * (s3 * cols.a[1]) = 0 ∧
  sll * (s3 * cols.a[2]) = 0 ∧
  sll * (s3 * (cols.a[3] - cols.limb_result[0])) = 0 ∧
  sllw * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  sllw * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  sllw * (s1 * cols.a[0]) = 0 ∧
  sllw * (s1 * (cols.a[1] - cols.limb_result[0])) = 0 ∧
  sllw * (cols.sllw_msb.msb * 65535 - cols.a[2]) = 0 ∧
  sllw * (cols.sllw_msb.msb * 65535 - cols.a[3]) = 0 ∧
  cols.is_sllw_imm - sllw * cols.adapter.imm_c = 0 ∧
  cols.adapter.op_a_0 = 0

/-- Semantic, `is_real`-gated, **flag-gated** contract: on real rows the result column `cols.a` is the
RV64 shift-left of the operand by the shift amount, with the variant selected by the committed flag
columns (`cols.is_sll → RV64.sll`, the 64-bit logical left shift; `cols.is_sllw → RV64.sllw`, the
low-32 left shift sign-extended to 64). Operand order matches the RV64 signature `f rs2_val rs1_val`
with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sll = 1 →
      Word.toBitVec64 cols.a = RV64.sll (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_sllw = 1 →
      Word.toBitVec64 cols.a = RV64.sllw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.ShiftLeftChip

namespace SP1Clean.ShiftRightChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- As `ShiftLeftChip.Inputs`: the shift operand word (`rs1`, `op_b_val`), the shift-amount source word
(`rs2`/immediate, `op_c_val`), the `is_real` selector, and the threaded `state`/`adapter` blocks
(`ShiftRight` is also an `ALUTypeReader` ALU op — `SRLI`/`SRAI`/`SRLIW`/`SRAIW` take an immediate). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- Native ShiftRight-chip row (Rust field order — the chip has no separate `is_real` column; the
real-row selector is the four-flag sum). The reader blocks and the two MSB blocks reuse the project
substrate (`Extracted.U16MSBOperation` stays a standalone generated module).
`Faithful.shiftRightChipReconfigure` is the sole bridge to Rust's separately generated whole-chip
row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
  a : Word F
  b_msb : Extracted.U16MSBOperation F
  srw_msb : Extracted.U16MSBOperation F
  c_bits : Vector F 6
  sra_msb_v0123 : F
  v_0123 : F
  v_012 : F
  v_01 : F
  lower_limb : Word F
  higher_limb : Word F
  limb_result : Vector F 4
  shift_u16 : Vector F 4
  is_srl : F
  is_sra : F
  is_srlw : F
  is_sraw : F
  is_w_imm : F
deriving ProvableStruct

/-- The folded tail of the generated ShiftRight `asserts` list, beginning immediately after the four
flag booleans and their combined boolean gate.  This is a genuine proof boundary, not a claimed Rust
operation: the parent chip emits the five shallow gate constraints itself, then composes the tail
without making parent proofs normalize the remaining 53 assertions. -/
def CoreSpec (cols : Columns (ZMod p)) : Prop :=
  let srl := cols.is_srl; let sra := cols.is_sra; let srlw := cols.is_srlw; let sraw := cols.is_sraw
  let e14 := srl + sra; let e13 := srlw + sraw; let sum := srl + sra + srlw + sraw
  let b0 := cols.c_bits[0]; let b1 := cols.c_bits[1]; let b2 := cols.c_bits[2]
  let b3 := cols.c_bits[3]; let b4 := cols.c_bits[4]; let b5 := cols.c_bits[5]
  let s0 := cols.shift_u16[0]; let s1 := cols.shift_u16[1]
  let s2 := cols.shift_u16[2]; let s3 := cols.shift_u16[3]
  let byteShift := b4 + b5 * 2 * e14
  let bmsb := cols.b_msb.msb; let srwmsb := cols.srw_msb.msb
  let sraFill := cols.b_msb.msb * 65536 - cols.sra_msb_v0123
  -- immediate consistency
  cols.is_w_imm - e13 * cols.adapter.imm_c = 0 ∧
  -- c_bits booleans
  b0 * (b0 - 1) = 0 ∧ b1 * (b1 - 1) = 0 ∧ b2 * (b2 - 1) = 0 ∧
  b3 * (b3 - 1) = 0 ∧ b4 * (b4 - 1) = 0 ∧ b5 * (b5 - 1) = 0 ∧
  -- shift_u16 byte-shift selectors + booleans
  s0 * (byteShift - 0) = 0 ∧ s0 * (s0 - 1) = 0 ∧
  s1 * (byteShift - 1) = 0 ∧ s1 * (s1 - 1) = 0 ∧
  s2 * (byteShift - 2) = 0 ∧ s2 * (s2 - 1) = 0 ∧
  s3 * (byteShift - 3) = 0 ∧ s3 * (s3 - 1) = 0 ∧
  sum * ((s0 + s1 + s2 + s3) - 1) = 0 ∧
  -- inverted v_* power encodings
  cols.v_01 - (((1 - b0) + 1) * 2) * ((1 - b1) * 3 + 1) = 0 ∧
  cols.v_012 - cols.v_01 * ((1 - b2) * 15 + 1) = 0 ∧
  cols.v_0123 - cols.v_012 * ((1 - b3) * 255 + 1) = 0 ∧
  -- lower/higher limb split (limbs 2,3 carry the E14 factor)
  cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    - (cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) = 0 ∧
  cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    - (cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123) * e14
    - (cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123) * e14
    - (cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  -- limb_result reassembly (higher_limb[i] + lower_limb[i+1] * v_0123)
  cols.limb_result[0] - (cols.higher_limb[0] + cols.lower_limb[1] * cols.v_0123) = 0 ∧
  cols.limb_result[1] - (cols.higher_limb[1] + cols.lower_limb[2] * cols.v_0123) = 0 ∧
  cols.limb_result[2] - (cols.higher_limb[2] + cols.lower_limb[3] * cols.v_0123) = 0 ∧
  cols.limb_result[3] - cols.higher_limb[3] = 0 ∧
  -- MSB sign witnesses
  (srl + srlw) * bmsb = 0 ∧
  cols.sra_msb_v0123 - bmsb * cols.v_0123 = 0 ∧
  (e13 - 1) * srwmsb = 0 ∧
  -- SRL/SRA output placement (gated e14)
  e14 * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  e14 * (s0 * (cols.a[1] - cols.limb_result[1])) = 0 ∧
  e14 * (s0 * (cols.a[2] - cols.limb_result[2])) = 0 ∧
  e14 * (s0 * (cols.a[3] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s1 * (cols.a[0] - cols.limb_result[1])) = 0 ∧
  e14 * (s1 * (cols.a[1] - cols.limb_result[2])) = 0 ∧
  e14 * (s1 * (cols.a[2] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s1 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  e14 * (s2 * (cols.a[0] - cols.limb_result[2])) = 0 ∧
  e14 * (s2 * (cols.a[1] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s2 * (cols.a[2] - bmsb * 65535)) = 0 ∧
  e14 * (s2 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[0] - (cols.limb_result[3] + sraFill))) = 0 ∧
  e14 * (s3 * (cols.a[1] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[2] - bmsb * 65535)) = 0 ∧
  e14 * (s3 * (cols.a[3] - bmsb * 65535)) = 0 ∧
  -- SRLW/SRAW output placement (gated e13)
  e13 * (s0 * (cols.a[0] - cols.limb_result[0])) = 0 ∧
  e13 * (s0 * (cols.a[1] - (cols.limb_result[1] + sraFill))) = 0 ∧
  e13 * (s1 * (cols.a[0] - (cols.limb_result[1] + sraFill))) = 0 ∧
  e13 * (s1 * (cols.a[1] - bmsb * 65535)) = 0 ∧
  e13 * (cols.a[2] - srwmsb * 65535) = 0 ∧
  e13 * (cols.a[3] - srwmsb * 65535) = 0 ∧
  -- op_a_0 zeroing flag
  cols.adapter.op_a_0 = 0

/-- **Assertion half** — the literal meaning of the generated ShiftRight `asserts` *own* assertZero
list. `E14 = is_srl + is_sra` (the 64-bit-shift indicator) and `E13 = is_srlw + is_sraw` (the
word-shift indicator) gate the two output-placement blocks; the `v_*` powers are the **inverted**
right-shift form `2^(16 - bitShift)`. In exact upstream order this is the four flag booleans, their
combined boolean gate, then `CoreSpec`'s remaining 53 assertions. -/
def AssertSpec (cols : Columns (ZMod p)) : Prop :=
  let srl := cols.is_srl; let sra := cols.is_sra; let srlw := cols.is_srlw; let sraw := cols.is_sraw
  let sum := srl + sra + srlw + sraw
  srl * (srl - 1) = 0 ∧ sra * (sra - 1) = 0 ∧ srlw * (srlw - 1) = 0 ∧
    sraw * (sraw - 1) = 0 ∧ sum * (sum - 1) = 0 ∧ CoreSpec cols

/-- Semantic, `is_real`-gated, **flag-gated** contract with four variant conjuncts: on real rows the
result column `cols.a` is the RV64 right-shift selected by the committed flag (`cols.is_srl → RV64.srl`
logical, `cols.is_sra → RV64.sra` arithmetic, `cols.is_srlw → RV64.srlw` low-32 logical sign-extended,
`cols.is_sraw → RV64.sraw` low-32 arithmetic sign-extended). The operands are the **register reads** the
chip actually decomposes — `rs1 ↦ adapter.op_b_memory.prev_value` (the shifted value), `rs2 ↦
adapter.op_c_memory.prev_value` (the shift amount) — stated directly on the adapter columns, since SP1's
shift chip inlines the decomposition of the register read rather than passing a separate operand word to
an operation gadget. Operand order `f rs2 rs1`. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  let rs1 := input.adapter.op_b_memory.prev_value
  let rs2 := input.adapter.op_c_memory.prev_value
  input.is_real = 1 →
    (cols.is_srl = 1 →
      Word.toBitVec64 cols.a = RV64.srl (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_sra = 1 →
      Word.toBitVec64 cols.a = RV64.sra (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_srlw = 1 →
      Word.toBitVec64 cols.a = RV64.srlw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1)) ∧
    (cols.is_sraw = 1 →
      Word.toBitVec64 cols.a = RV64.sraw (Word.toBitVec64 rs2) (Word.toBitVec64 rs1))

end SP1Clean.ShiftRightChip

namespace SP1Clean.MulChip

-- `Mul`'s column sums reach `~2^20`, so the `MulOperation` gadget it composes is gated on `2^24 < p`;
-- the whole `Mul` chain (this `Spec` included) carries the same bound (unlike the `2^17` of other chips).
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- Native MUL-chip row. The reader blocks reuse the project substrate and the arithmetic block is the
shared `Extracted.MulOperation` column struct (still a standalone generated module — `DivRem` composes
the same gadget). The five variant selectors are committed columns. `Faithful.mulChipReconfigure` is
the sole bridge to Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
  a : Word F
  mul_operation : Extracted.MulOperation F
  is_mul : F
  is_mulh : F
  is_mulhu : F
  is_mulhsu : F
  is_mulw : F
deriving ProvableStruct

/-- The two operand words (as read for `rs1`/`rs2`), the `is_real` selector, and the **threaded reader
column blocks** `state`/`adapter` (as `AddChip`; `Mul`/`Mulh`/… are R-type register-register ops, so the
adapter is the register `RTypeReader`). The five variant selectors are *committed columns* of the row
(gated on in the `Spec` via `cols.is_mul` etc.), not inputs. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1`/`rs2` source operands = the register reads on the adapter's `op_b`/`op_c` memory slots. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- The five committed dispatch cells, projected away from MUL's large arithmetic witness.  Control
proofs use this small view so neither Lean nor an auditor must normalize the 45-cell multiplication
block merely to determine the selected instruction. -/
structure SelectorValues (F : Type) where
  is_mul : F
  is_mulh : F
  is_mulhu : F
  is_mulhsu : F
  is_mulw : F
deriving ProvableStruct

/-- Project the dispatch cells from a complete MUL row. -/
def selectors {F : Type} (cols : Columns F) : SelectorValues F :=
  ⟨cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw⟩

/-- Auditable control-flow contract for an active MUL-family row: exactly one committed variant
selector is set.  The native AIR derives this from the five selector boolean gates together with
`is_real = Σ selectors`; the Sail dispatch consumes precisely this proposition. -/
def SelectorOneHot (s : SelectorValues (ZMod p)) : Prop :=
  (s.is_mul = 1 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulh = 1 ∧ s.is_mul = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulhu = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhsu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulhsu = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulw = 0) ∨
  (s.is_mulw = 1 ∧ s.is_mul = 0 ∧ s.is_mulh = 0 ∧ s.is_mulhu = 0 ∧ s.is_mulhsu = 0)

/-- The chip-owned selector/routing part of the MUL AIR, separated from multiplication arithmetic
and reader semantics.  This is the stable contract proved directly from physical assertions and
used to justify active-row dispatch and the non-`x0` write route. -/
def ControlSpec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) : Prop :=
  let s := selectors cols
  (s.is_mul = 0 ∨ s.is_mul = 1) ∧
  (s.is_mulh = 0 ∨ s.is_mulh = 1) ∧
  (s.is_mulhu = 0 ∨ s.is_mulhu = 1) ∧
  (s.is_mulhsu = 0 ∨ s.is_mulhsu = 1) ∧
  (s.is_mulw = 0 ∨ s.is_mulw = 1) ∧
  input.is_real = s.is_mul + s.is_mulh + s.is_mulhu + s.is_mulhsu + s.is_mulw ∧
  input.adapter.op_a_0 = 0

/-- High-half kernel: extracting bits `64..127` of the *wide* (129-bit) product of two extensions
equals `setWidth 64` of the *narrow* (128-bit) product shifted right by 64. The two products agree on
their low 128 bits (`setWidth 128` of the wide product is the narrow product), so they agree on bits
`64..127`. The `MULH`/`MULHSU` bridges instantiate this; `MULHU`'s product is already 128-bit. -/
private lemma high64_mul (b' c' : BitVec 129) (b'' c'' : BitVec 128)
    (hb : b'' = BitVec.setWidth 128 b') (hc : c'' = BitVec.setWidth 128 c') :
    BitVec.extractLsb 127 64 (b' * c') = ((b'' * c'') >>> 64).setWidth 64 := by
  have hmul : b'' * c'' = BitVec.setWidth 128 (b' * c') := by
    rw [hb, hc]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_mul]
    rw [Nat.mod_mod_of_dvd _ ⟨2, by ring⟩, ← Nat.mul_mod]
  rw [hmul]; generalize (b' * c') = P; bv_decide

/-- `RV64.mul rs2 rs1 = rs1 * rs2` (commuted into the gadget's `b * c` form). -/
lemma rv64_mul_eq (x y : BitVec 64) : RV64.mul x y = y * x := by
  rw [RV64.mul, BitVec.mul_comm]

/-- `RV64.mulh`'s high-64-bit signed×signed product equals the gadget's `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulh_eq (x y : BitVec 64) :
    RV64.mulh x y = ((y.signExtend 128 * x.signExtend 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulh]; exact high64_mul _ _ _ _ (by bv_decide) (by bv_decide)

/-- `RV64.mulhu`'s high-64-bit unsigned×unsigned product (its inner `extractLsb' 0 128` is the
identity on the 128-bit product) equals the gadget's `setWidth 128`-product `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulhu_eq (x y : BitVec 64) :
    RV64.mulhu x y = ((y.setWidth 128 * x.setWidth 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulhu]
  generalize (BitVec.zeroExtend 128 y * BitVec.zeroExtend 128 x) = P
  bv_decide

/-- `RV64.mulhsu`'s high-64-bit signed(rs1)×unsigned(rs2) product equals the gadget's
`signExtend 128 (rs1) * setWidth 128 (rs2)` `>>>64 |>.setWidth 64` form. -/
lemma rv64_mulhsu_eq (x y : BitVec 64) :
    RV64.mulhsu x y = ((y.signExtend 128 * x.setWidth 128) >>> 64).setWidth 64 := by
  simp only [RV64.mulhsu]; exact high64_mul _ _ _ _ (by bv_decide) (by bv_decide)

/-- `RV64.mulw`'s low-32 product sign-extended to 64 equals the gadget's
`((rs1 * rs2).setWidth 32).signExtend 64` form. -/
lemma rv64_mulw_eq (x y : BitVec 64) :
    RV64.mulw x y = ((y * x).setWidth 32).signExtend 64 := by
  simp only [RV64.mulw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.extractLsb, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.reduceAdd, Nat.reduceSub]
  rw [Nat.mod_mod_of_dvd _ ⟨2 ^ 32, by norm_num⟩, ← Nat.mul_mod]

/-- Semantic contract, composed from the sub-circuits' own `Spec`s (as `AddChip`). Four conjuncts: the
`RTypeReader` reader sub-`Spec` on the `state`/`adapter` blocks (the register reads/write, gated by the
flag-weighted R-type opcode `is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24` and the
result `cols.a` as the `op_a` write value), the *proven* `is_real`-binary fact, the `is_real`-gated,
**flag-gated** arithmetic with five variant conjuncts: on real rows the result column `cols.a` is the RV64
multiply selected by the committed flag (`cols.is_mul → RV64.mul`, the low-64 product; `cols.is_mulh →
RV64.mulh`, signed×signed high 64; `cols.is_mulhu → RV64.mulhu`, unsigned×unsigned high 64; `cols.is_mulhsu
→ RV64.mulhsu`, signed×unsigned high 64; `cols.is_mulw → RV64.mulw`, low-32 product sign-extended to 64) —
and the *proven* selector **one-hot**: on real rows exactly one committed variant flag is set
(`SelectorOneHot (selectors cols)`, from the five selector boolean gates plus the circuit's
`is_real = Σ selectors` assert), so a real row cannot satisfy the five gated conjuncts vacuously.
Operand order matches the RV64 signature `f rs2_val rs1_val` with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`.
Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulhu * 13 + cols.is_mulhsu * 14
        + cols.is_mulw * 24,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_mul = 1 →
      Word.toBitVec64 cols.a = RV64.mul (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulh = 1 →
      Word.toBitVec64 cols.a = RV64.mulh (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulhu = 1 →
      Word.toBitVec64 cols.a = RV64.mulhu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulhsu = 1 →
      Word.toBitVec64 cols.a = RV64.mulhsu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_mulw = 1 →
      Word.toBitVec64 cols.a = RV64.mulw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))) ∧
  (input.is_real = 1 → SelectorOneHot (selectors cols))

end SP1Clean.MulChip

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (as `MulChip`;
`DIV`/`REM`/… are R-type register-register ops, so the adapter is the register `RTypeReader`). The
`rs1`/`rs2` register reads are projected from the adapter (`op_b_val`/`op_c_val` below). The arithmetic
**operands** `b`/`c` are *separate committed columns* of `DivRemChip.Columns`, tied to these reads by the chip's
own-asserts E20–E47 — equal to the read for the 64-bit variants, the sign/zero-extension of the low 32 bits
for the W-variants. The eight variant selectors are likewise *committed columns* of `DivRemChip.Columns` (gated on in
the `Spec` via `cols.is_div` etc.), not inputs. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- Component-wise verifier evaluation of the DivRem chip input. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real,
         state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- The `rs1` source = the register read on the `op_b` memory slot (`op_b_memory.prev_value`, the value the
Memory bus pins). The `Spec` and Sail bridge state the RV64 identity on this **raw read**; this is correct even
for the W-variants because `RV64.divw`/`divuw`/`remw`/`remuw` truncate their inputs to the low 32 bits. The
flag-dependent arithmetic operand (read for 64-bit ops, sign/zero-extension for W-ops) lives in the committed
`DivRemChip.Columns.b` column, not here. `@[reducible]` so proofs that manipulate the adapter slot see through it. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The `rs2` source = the register read on the `op_c` memory slot (`op_c_memory.prev_value`). -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Public chip contract: reader/bus-facing row plumbing plus the stable semantic `DivRemContract.RowSpec`.
The latter gives names to the binary real-row gate, unique committed case, and eight independently
verifiable RV64 results. Division by zero and signed overflow are specified by the RV64 functions
themselves; they are not hidden side assumptions. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := DivRemContract.encodedOpcode cols,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  DivRemContract.RowSpec input.is_real input.op_b_val input.op_c_val cols.a cols

end SP1Clean.DivRemChip

namespace SP1Clean.JalChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native JAL-chip row.  The two arithmetic blocks follow the local Lean gadget
(`AddOperation.Columns`), not Rust's `AddOperation` type; `Faithful.jalChipReconfigure` is the
explicit whole-chip bridge to the extracted `JalOracle.JalColumns` oracle.  The reader blocks
remain the shared generated substrate. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.JTypeReader F
  add_operation : AddOperation.Columns F
  op_a_operation : AddOperation.Columns F
deriving ProvableStruct

/-- The committed **J-type** row blocks the chip reads: the `is_real` selector, the CPUState block
`state` (clk + `pc`), and the J-type register adapter `adapter` (the destination `op_a`/`op_a_0`, its
`op_a_memory` timestamp, and the two immediate words `op_b_imm`/`op_c_imm`). Unlike the ALU chips there
are **no** `op_b_val`/`op_c_val` register operands — both source operands are immediates carried in the
adapter. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.JTypeReader F
deriving ProvableStruct

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand both of the chip's `AddOperation`s add to (`pc + imm = next_pc`, `pc + 4 = link`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- Semantic contract for the JAL row, composed from the J-type reader sub-`Spec` plus the
`is_real`-gated jump/link semantics. On a real row: the jump target `add_operation.value = pc + op_b_imm`
(`op_b_imm` is the sign-extended 21-bit immediate — the actual `BitVec 21` ↔ word relation is a received
decode fact, supplied at the Sail bridge), and — when `rd ≠ x0` (`op_a_0 = 0`) — the link-address write
`op_a_operation.value = pc + 4`. The final conjunct records that the jump target's low limb
(`add_operation.value[0]`) is divisible by 4 — i.e. the target is 4-byte aligned — forced by the
in-circuit alignment `Range` byte-lookup (`value[0] · 4⁻¹ < 2^14`); the Sail bridge lifts it to the whole
word (so alignment is no longer an assumed bridge precondition). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.JTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 46,
      wv0 := cols.op_a_operation.value[0], wv1 := cols.op_a_operation.value[1],
      wv2 := cols.op_a_operation.value[2], wv3 := cols.op_a_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 cols.adapter.op_b_imm) ∧
  (input.is_real = 1 → cols.adapter.op_a_0 = 0 →
    Word.toBitVec64 cols.op_a_operation.value
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod p))) ∧
  (input.is_real = 1 → (cols.add_operation.value[0]).val % 4 = 0)

end SP1Clean.JalChip

namespace SP1Clean.UTypeChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native U-type chip row.  The arithmetic block follows the local Lean gadget
(`AddOperation.Columns`), not Rust's `AddOperation` type; `Faithful.uTypeChipReconfigure` is the
explicit whole-chip bridge to the extracted `UTypeOracle.UTypeColumns` oracle.  The reader blocks
remain the shared generated substrate. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.JTypeReader F
  addend : Vector F 3
  add_operation : AddOperation.Columns F
  is_auipc : F
deriving ProvableStruct

/-- The committed **U-type** row blocks the chip reads: the `is_real` selector, the CPUState block `state`
(clk + `pc`), the J-type register adapter `adapter` (the destination `op_a`/`op_a_0`, its `op_a_memory`
timestamp, and the two immediate words `op_b_imm`/`op_c_imm`), and the variant selector `is_auipc`
(`1` = AUIPC, `0` = LUI). Like JAL there are **no** register operands — the immediate is carried in the
adapter; unlike JAL the chip additionally commits `is_auipc` (and the `addend` column, in the output
`Columns`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.JTypeReader F
  is_auipc : F
deriving ProvableStruct

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand of the chip's `AddOperation` for AUIPC (`pc + imm`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The 20-bit U-type immediate recovered from the committed `op_b_imm` limbs (the high 20 bits of the
constrained 32-bit immediate). Appears identically in the chip's decode `Assumption` (LHS) and the `Spec`
(the `RV64.lui`/`RV64.auipc` argument), so the proofs never unfold its extraction formula. -/
def immOf (adapter : Extracted.JTypeReader (ZMod p)) : BitVec 20 :=
  BitVec.ofNat 20 (adapter.op_b_imm[0].val / 4096 + adapter.op_b_imm[1].val * 16)

/-- Semantic contract for the U-type row, composed from the J-type reader sub-`Spec` plus the
`is_real`-gated, flag-gated `RV64.lui`/`RV64.auipc` semantics (mirroring `MulChip`'s flag-gated form).
On a real
row with `rd ≠ x0` (`op_a_0 = 0`, where the additive `is_real - op_a_0` gate fires): LUI (`is_auipc = 0`)
writes `RV64.lui imm`, AUIPC (`is_auipc = 1`) writes `RV64.auipc imm pc`, with `imm := immOf adapter` and
`pc := toBitVec64 pcWord`. The `op_b_imm` ↔ `imm` decode relation is a chip `Assumption` (a trace/program-ROM
guarantee). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.JTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := input.is_auipc * 48 + (1 - input.is_auipc) * 49,
      wv0 := cols.add_operation.value[0], wv1 := cols.add_operation.value[1],
      wv2 := cols.add_operation.value[2], wv3 := cols.add_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_auipc = 0 ∨ input.is_auipc = 1) ∧
  (input.is_real = 1 → cols.adapter.op_a_0 = 0 → input.is_auipc = 0 →
    Word.toBitVec64 cols.add_operation.value = RV64.lui (immOf cols.adapter)) ∧
  (input.is_real = 1 → cols.adapter.op_a_0 = 0 → input.is_auipc = 1 →
    Word.toBitVec64 cols.add_operation.value
      = RV64.auipc (immOf cols.adapter) (Word.toBitVec64 (pcWord cols)))

end SP1Clean.UTypeChip

namespace SP1Clean.JalrChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native JALR-chip row.  The two arithmetic blocks follow the local Lean gadget
(`AddOperation.Columns`), not Rust's `AddOperation` type; `Faithful.jalrChipReconfigure` is the
explicit whole-chip bridge to the extracted `JalrOracle.JalrColumns` oracle.  The reader blocks
remain the shared generated substrate. -/
structure Columns (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  add_operation : AddOperation.Columns F
  op_a_operation : AddOperation.Columns F
  lsb : F
deriving ProvableStruct

/-- The committed **I-type** row blocks the JALR chip reads: the `is_real` selector, the CPUState block
`state` (clk + `pc`), and the I-type register adapter `adapter` (the destination `op_a`/`op_a_0` with its
`op_a_memory` write timestamp, the **source register** `op_b` = rs1 with its `op_b_memory` read block, and
the immediate word `op_c_imm`). Unlike JAL the jump base is a register operand (rs1) carried in the
adapter's `op_b_memory.prev_value`, not the program counter. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
deriving ProvableStruct

/-- The rs1 register value as a 4-limb word — the `op_b` source read's prior value, the `a` operand of the
jump `AddOperation` (`rs1 + imm = target`). -/
def rs1Word (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand of the link `AddOperation` (`pc + 4 = link`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The committed, **LSB-cleared** next-pc word the chip feeds `CPUState` — the jump target
`add_operation.value` with its low bit removed (`value[0] - lsb`), faithful to RISC-V JALR's
`(rs1 + imm) & ~1` and the Sail `BitVec.update target 0 0#1`. Named by the `Spec`'s LSB-clearing
conjunct and the Sail bridge. -/
def nextPcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.add_operation.value[0] - cols.lsb, cols.add_operation.value[1],
     cols.add_operation.value[2], 0]

/-- Semantic contract for the JALR row, composed from the I-type reader sub-`Spec` plus the
`is_real`-gated jump/link semantics. On a real row: the jump target `add_operation.value = rs1 + op_c_imm`
(`op_c_imm` is the sign-extended 12-bit immediate — the `BitVec 12` ↔ word relation is a received decode
fact, supplied at the Sail bridge), the `lsb` witness is binary, and — when `rd ≠ x0` (`op_a_0 = 0`) — the
link-address write `op_a_operation.value = pc + 4`. The committed next_pc is the LSB-cleared
`nextPcWord`. The final conjunct records that this cleared low limb (`add_operation.value[0] - lsb`)
is divisible by 4 — i.e. the jump target is 4-byte aligned — forced by the in-circuit alignment
`Range` byte-lookup (`(value[0] - lsb) · 4⁻¹ < 2^14`); the Sail bridge lifts it to the whole word.
The final conjunct exposes the **LSB-clearing relation** itself — the committed `nextPcWord` is the
jump target with bit 0 cleared (`~~~1#64 &&&`, the Sail-free form of `BitVec.update _ 0 0#1`) — so the
Sail bridge *derives* it from this `Spec` rather than assuming it. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ITypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := 47,
      wv0 := cols.op_a_operation.value[0], wv1 := cols.op_a_operation.value[1],
      wv2 := cols.op_a_operation.value[2], wv3 := cols.op_a_operation.value[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (cols.lsb = 0 ∨ cols.lsb = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = Word.toBitVec64 (rs1Word cols) + Word.toBitVec64 cols.adapter.op_c_imm) ∧
  (input.is_real = 1 → cols.adapter.op_a_0 = 0 →
    Word.toBitVec64 cols.op_a_operation.value
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod p))) ∧
  (input.is_real = 1 → (cols.add_operation.value[0] - cols.lsb).val % 4 = 0) ∧
  (input.is_real = 1 →
    Word.toBitVec64 (nextPcWord cols) = ~~~(1#64) &&& Word.toBitVec64 cols.add_operation.value)

end SP1Clean.JalrChip

namespace SP1Clean.BranchChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native Branch-chip row (Rust field order). The reader blocks and the compare block reuse the
project substrate (`Extracted.LtOperationSigned` is still a standalone generated module — the Lt
chip composes the same gadget family). `Faithful.BranchChip.branchChipReconfigure` is the sole
bridge to Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  next_pc : Vector F 3
  is_beq : F
  is_bne : F
  is_blt : F
  is_bge : F
  is_bltu : F
  is_bgeu : F
  is_branching : F
  compare_operation : Extracted.LtOperationSigned F
deriving ProvableStruct

/-- The committed **B-type** row blocks the Branch chip reads: the `is_real` selector (bound in-circuit to
the flag sum `Σ is_b*`), the CPUState block `state` (clk + `pc`), and the immutable I-type register adapter
`adapter` (the two **source reads** rs1 = `op_a_memory.prev_value`, rs2 = `op_b_memory.prev_value`, and the
sign-extended branch-offset immediate `op_c_imm`). Branches have **no** destination write. The six opcode
flags, `is_branching`, the `compare_operation`, and `next_pc` are committed **columns** (witnessed in
`main`), not inputs. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
deriving ProvableStruct

/-- The rs1 register value as a 4-limb word — the `op_a` source read's prior value, the `a`/`b` operand of
the compare (`a < b`, with `a ↦ rs1`). -/
def rs1Word (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_a_memory.prev_value[0], cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2], cols.adapter.op_a_memory.prev_value[3]]

/-- The rs2 register value as a 4-limb word — the `op_b` source read's prior value. -/
def rs2Word (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand both of the chip's `AddOperation`s add to (`pc + imm = taken target`, `pc + 4 = fall-through`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The committed `next_pc` (three 16-bit limbs) padded to a 4-limb word. -/
def nextPcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2], 0]

/-- The reconstructed branch opcode `Σ is_b* · k` (BEQ 40 … BGEU 45), fed to the program-bus read. -/
def branchOpcode (cols : Columns (ZMod p)) : ZMod p :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 + cols.is_bge * 43
    + cols.is_bltu * 44 + cols.is_bgeu * 45

/-- The six opcode flags and the `is_branching` decision are all binary. -/
def flagsBinary (cols : Columns (ZMod p)) : Prop :=
  (cols.is_beq = 0 ∨ cols.is_beq = 1) ∧ (cols.is_bne = 0 ∨ cols.is_bne = 1) ∧
  (cols.is_blt = 0 ∨ cols.is_blt = 1) ∧ (cols.is_bge = 0 ∨ cols.is_bge = 1) ∧
  (cols.is_bltu = 0 ∨ cols.is_bltu = 1) ∧ (cols.is_bgeu = 0 ∨ cols.is_bgeu = 1) ∧
  (cols.is_branching = 0 ∨ cols.is_branching = 1)

/-- The active branch-opcode selector is exactly one-hot.  This is semantic row information:
the six physical flag gates and `is_real = Σ flags` establish it in the chip soundness proof, and
the Sail bridge consumes it to select the unique B-type instruction. -/
def flagsOneHot (cols : Columns (ZMod p)) : Prop :=
  (cols.is_beq = 1 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bne = 1 ∧ cols.is_beq = 0 ∧ cols.is_blt = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_blt = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_bge = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bge = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bltu = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bltu = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bge = 0 ∧ cols.is_bgeu = 0) ∨
    (cols.is_bgeu = 1 ∧ cols.is_beq = 0 ∧ cols.is_bne = 0 ∧ cols.is_blt = 0 ∧
      cols.is_bge = 0 ∧ cols.is_bltu = 0)

/-- Semantic contract for the Branch row, composed from the immutable I-type reader sub-`Spec`, the proven
binary facts, and the `is_real`-gated branch semantics. The next_pc value is split into a *provable* half
(gated by `is_branching` — the two `AddOperation` targets) and a *compare-dependent* half (the six-way
flag-dispatched decision relating `is_branching` to the RISC-V condition on rs1/rs2, routed through the
skeletal `LtOperationSigned`). On a real row:
- if `is_branching = 1`, `next_pc = pc + op_c_imm` (the sign-extended offset is a received decode fact,
  supplied at the Sail bridge); if `is_branching = 0`, `next_pc = pc + 4`;
- and `is_branching` is taken iff the opcode's condition holds (`BEQ ↔ rs1 = rs2`, `BLT ↔ rs1 <ₛ rs2`, …);
- and the branch target's low limb (`next_pc[0]`) is divisible by 4 — i.e. the target is 4-byte aligned —
  forced by the in-circuit alignment `Range` byte-lookup (`next_pc[0] · 4⁻¹ < 2^14`); the Sail bridge lifts
  it to the whole word (so alignment is no longer an assumed bridge precondition).
Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ITypeReaderImmutable.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := branchOpcode cols } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  flagsBinary cols ∧
  (input.is_real = 1 → flagsOneHot cols) ∧
  (input.is_real = 1 → cols.is_branching = 1 →
    Word.toBitVec64 (nextPcWord cols)
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 cols.adapter.op_c_imm) ∧
  (input.is_real = 1 → cols.is_branching = 0 →
    Word.toBitVec64 (nextPcWord cols)
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod p))) ∧
  (input.is_real = 1 →
    (cols.is_beq = 1 →
      (cols.is_branching = 1 ↔ Word.toBitVec64 (rs1Word cols) = Word.toBitVec64 (rs2Word cols))) ∧
    (cols.is_bne = 1 →
      (cols.is_branching = 1 ↔ Word.toBitVec64 (rs1Word cols) ≠ Word.toBitVec64 (rs2Word cols))) ∧
    (cols.is_blt = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).slt (Word.toBitVec64 (rs2Word cols)) = true)) ∧
    (cols.is_bge = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).slt (Word.toBitVec64 (rs2Word cols)) = false)) ∧
    (cols.is_bltu = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).ult (Word.toBitVec64 (rs2Word cols)) = true)) ∧
    (cols.is_bgeu = 1 →
      (cols.is_branching = 1 ↔
        (Word.toBitVec64 (rs1Word cols)).ult (Word.toBitVec64 (rs2Word cols)) = false))) ∧
  (input.is_real = 1 → (cols.next_pc[0]).val % 4 = 0)

end SP1Clean.BranchChip
