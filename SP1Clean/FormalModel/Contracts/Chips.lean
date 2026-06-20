import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Extracted.AddChip
import SP1Clean.Extracted.AddiChip
import SP1Clean.Extracted.AddwChip
import SP1Clean.Extracted.SubChip
import SP1Clean.Extracted.SubwChip
import SP1Clean.Extracted.BitwiseChip
import SP1Clean.Extracted.ShiftLeftChip
import SP1Clean.Extracted.ShiftRightChip
import SP1Clean.Extracted.MulChip
import SP1Clean.Extracted.DivRemChip
import SP1Clean.Extracted.JalChip
import SP1Clean.Extracted.JalrChip
import SP1Clean.Extracted.BranchChip
import SP1Clean.Extracted.UTypeChip
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

open Extracted (AddCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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

/-- Semantic contract, composed from the sub-circuits' own `Spec`s. The four conjuncts: the two reader
sub-`Spec`s on the `state`/`adapter` blocks, the *proven* `is_real`-binary fact, and the `is_real`-gated
arithmetic meaning — on real rows the result column is the RV64 `ADD` of the operands
(`RV64.add op_c_val op_b_val = op_b_val + op_c_val`). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : AddCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  True ∧
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

open Extracted (AddiCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
def Spec (input : Inputs (ZMod p)) (cols : AddiCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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

open Extracted (SubCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance neZero_spec : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

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

/-- Semantic contract, mirroring `AddChip`. The fourth conjunct: on real rows the result column is the
RV64 `SUB` of the operands (`RV64.sub op_c_val op_b_val = op_b_val - op_c_val`, the fixed `rs1 - rs2`
order — `SUB` is not commutative). -/
def Spec (input : Inputs (ZMod p)) (cols : SubCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  True ∧
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

open Extracted (AddwCols)
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

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (ADDW's adapter is the
immediate-capable `ALUTypeReader`, per `Extracted/AddwChip.lean`, unlike SUBW's `RTypeReader`). The
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
def resultWord (cols : AddwCols (ZMod p)) : Word (ZMod p) :=
  #v[cols.addw_operation.value[0], cols.addw_operation.value[1],
     cols.addw_operation.msb.msb * 65535, cols.addw_operation.msb.msb * 65535]

/-- Semantic contract (inline for the **ALU** adapter, since ADDW's adapter is the immediate-capable
`ALUTypeReader`): the `ALUTypeReader` sub-`Spec` on the `state`/`adapter` blocks (opcode
`19`, `rd` write the sign-extended W result `resultWord`), the proven `is_real`-binary fact, and the
`is_real`-gated arithmetic meaning — on real rows the result word is the RV64 `ADDW` of the operands
(`RV64.addw op_c_val op_b_val` — the low-32 add sign-extended to 64). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : AddwCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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

open Extracted (SubwCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RV64 `SUBW` function equals the gadget's `signExtend 64 (setWidth 32 (rs1 - rs2))` form. -/
lemma rv64_subw_eq (x y : BitVec 64) :
    RV64.subw x y = (BitVec.setWidth 32 (y - x)).signExtend 64 := by
  simp only [RV64.subw, BitVec.sub_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  omega

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
def Spec (input : Inputs (ZMod p)) (cols : SubwCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  True ∧
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

open Extracted (ShiftLeftCols)
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

/-- `rs1` operand = the `op_b` register read (`op_b_memory.prev_value`); `rs2` operand = the ALU operand
word `adapter.op_c` (the `op_c` register read, or the immediate). Mirrors `LtChip.Inputs`. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c

/-- Semantic, `is_real`-gated, **flag-gated** contract: on real rows the result column `cols.a` is the
RV64 shift-left of the operand by the shift amount, with the variant selected by the committed flag
columns (`cols.is_sll → RV64.sll`, the 64-bit logical left shift; `cols.is_sllw → RV64.sllw`, the
low-32 left shift sign-extended to 64). Operand order matches the RV64 signature `f rs2_val rs1_val`
with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : ShiftLeftCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sll = 1 →
      Word.toBitVec64 cols.a = RV64.sll (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_sllw = 1 →
      Word.toBitVec64 cols.a = RV64.sllw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

end SP1Clean.ShiftLeftChip

namespace SP1Clean.ShiftRightChip

open Extracted (ShiftRightCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- As `ShiftLeftChip.Inputs`: the shift operand word (`rs1`, `op_b_val`), the shift-amount source word
(`rs2`/immediate, `op_c_val`), the `is_real` selector, and the threaded `state`/`adapter` blocks
(`ShiftRight` is also an `ALUTypeReader` ALU op — `SRLI`/`SRAI`/`SRLIW`/`SRAIW` take an immediate). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- Semantic, `is_real`-gated, **flag-gated** contract with four variant conjuncts: on real rows the
result column `cols.a` is the RV64 right-shift selected by the committed flag (`cols.is_srl → RV64.srl`
logical, `cols.is_sra → RV64.sra` arithmetic, `cols.is_srlw → RV64.srlw` low-32 logical sign-extended,
`cols.is_sraw → RV64.sraw` low-32 arithmetic sign-extended). The operands are the **register reads** the
chip actually decomposes — `rs1 ↦ adapter.op_b_memory.prev_value` (the shifted value), `rs2 ↦
adapter.op_c_memory.prev_value` (the shift amount) — stated directly on the adapter columns, since SP1's
shift chip inlines the decomposition of the register read rather than passing a separate operand word to
an operation gadget. Operand order `f rs2 rs1`. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : ShiftRightCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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

open Extracted (MulCols)
-- `Mul`'s column sums reach `~2^20`, so the `MulOperation` gadget it composes is gated on `2^24 < p`;
-- the whole `Mul` chain (this `Spec` included) carries the same bound (unlike the `2^17` of other chips).
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The two operand words (as read for `rs1`/`rs2`), the `is_real` selector, and the **threaded reader
column blocks** `state`/`adapter` (as `AddChip`; `Mul`/`Mulh`/… are R-type register-register ops, so the
adapter is the register `RTypeReader`). The five variant selectors are *committed columns* of `MulCols`
(gated on in the `Spec` via `cols.is_mul` etc.), not inputs. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1`/`rs2` source operands = the register reads on the adapter's `op_b`/`op_c` memory slots. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

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
  simp only [RV64.mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mul_comm]

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

/-- Semantic contract, composed from the sub-circuits' own `Spec`s (as `AddChip`). Three conjuncts: the
`RTypeReader` reader sub-`Spec` on the `state`/`adapter` blocks (the register reads/write, gated by the
flag-weighted R-type opcode `is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24` and the
result `cols.a` as the `op_a` write value), the *proven* `is_real`-binary fact, and the `is_real`-gated,
**flag-gated** arithmetic with five variant conjuncts: on real rows the result column `cols.a` is the RV64
multiply selected by the committed flag (`cols.is_mul → RV64.mul`, the low-64 product; `cols.is_mulh →
RV64.mulh`, signed×signed high 64; `cols.is_mulhu → RV64.mulhu`, unsigned×unsigned high 64; `cols.is_mulhsu
→ RV64.mulhsu`, signed×unsigned high 64; `cols.is_mulw → RV64.mulw`, low-32 product sign-extended to 64).
Operand order matches the RV64 signature `f rs2_val rs1_val` with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`.
Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : MulCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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
      Word.toBitVec64 cols.a = RV64.mulw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.MulChip

namespace SP1Clean.DivRemChip

open Extracted (DivRemCols)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (as `MulChip`;
`DIV`/`REM`/… are R-type register-register ops, so the adapter is the register `RTypeReader`). The
`rs1`/`rs2` register reads are projected from the adapter (`op_b_val`/`op_c_val` below). The arithmetic
**operands** `b`/`c` are *separate committed columns* of `DivRemCols`, tied to these reads by the chip's
own-asserts E20–E47 — equal to the read for the 64-bit variants, the sign/zero-extension of the low 32 bits
for the W-variants. The eight variant selectors are likewise *committed columns* of `DivRemCols` (gated on in
the `Spec` via `cols.is_div` etc.), not inputs. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.RTypeReader F
deriving ProvableStruct

/-- The `rs1` source = the register read on the `op_b` memory slot (`op_b_memory.prev_value`, the value the
Memory bus pins). The `Spec` and Sail bridge state the RV64 identity on this **raw read**; this is correct even
for the W-variants because `RV64.divw`/`divuw`/`remw`/`remuw` truncate their inputs to the low 32 bits. The
flag-dependent arithmetic operand (read for 64-bit ops, sign/zero-extension for W-ops) lives in the committed
`DivRemCols.b` column, not here. `@[reducible]` so proofs that manipulate the adapter slot see through it. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- The `rs2` source = the register read on the `op_c` memory slot (`op_c_memory.prev_value`). -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Semantic contract, composed from the sub-circuits' own `Spec`s (as `MulChip`). Three conjuncts: the
`RTypeReader` reader sub-`Spec` on the `state`/`adapter` blocks (the register reads/write, gated by the
flag-weighted R-type opcode and the result `cols.a` as the `op_a` write value), the *proven* `is_real`-binary
fact, and the `is_real`-gated, **flag-gated** arithmetic with eight variant conjuncts: on real rows the
result column `cols.a` is the RV64 divide/remainder selected by the committed flag (`cols.is_div →
RV64.div`, signed 64-bit quotient; `cols.is_divu → RV64.divu`, unsigned; `cols.is_rem → RV64.rem`,
signed remainder; `cols.is_remu → RV64.remu`, unsigned; and the four `*w` word variants `divw`/`remw`/
`divuw`/`remuw`, 32-bit operated then sign-extended to 64). Operand order matches the RV64 signature
`f rs2_val rs1_val` with `rs1 ↦ op_b_val`, `rs2 ↦ op_c_val`. Vacuous on padding.

The per-flag overflow/divide-by-zero side conditions (SP1's `DivRemCols.eval`) are not yet folded in. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
        + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_div = 1 →
      Word.toBitVec64 cols.a = RV64.div (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_divu = 1 →
      Word.toBitVec64 cols.a = RV64.divu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_rem = 1 →
      Word.toBitVec64 cols.a = RV64.rem (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_remu = 1 →
      Word.toBitVec64 cols.a = RV64.remu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_divw = 1 →
      Word.toBitVec64 cols.a = RV64.divw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_remw = 1 →
      Word.toBitVec64 cols.a = RV64.remw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_divuw = 1 →
      Word.toBitVec64 cols.a = RV64.divuw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_remuw = 1 →
      Word.toBitVec64 cols.a = RV64.remuw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

end SP1Clean.DivRemChip

namespace SP1Clean.JalChip

open Extracted (JalColumns)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
def pcWord (cols : JalColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- Semantic contract for the JAL row, composed from the J-type reader sub-`Spec` plus the
`is_real`-gated jump/link semantics. On a real row: the jump target `add_operation.value = pc + op_b_imm`
(`op_b_imm` is the sign-extended 21-bit immediate — the actual `BitVec 21` ↔ word relation is a received
decode fact, supplied at the Sail bridge), and — when `rd ≠ x0` (`op_a_0 = 0`) — the link-address write
`op_a_operation.value = pc + 4`. Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : JalColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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
      = Word.toBitVec64 (pcWord cols) + Word.toBitVec64 (#v[4, 0, 0, 0] : Word (ZMod p)))

end SP1Clean.JalChip

namespace SP1Clean.UTypeChip

open Extracted (UTypeColumns)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The committed **U-type** row blocks the chip reads: the `is_real` selector, the CPUState block `state`
(clk + `pc`), the J-type register adapter `adapter` (the destination `op_a`/`op_a_0`, its `op_a_memory`
timestamp, and the two immediate words `op_b_imm`/`op_c_imm`), and the variant selector `is_auipc`
(`1` = AUIPC, `0` = LUI). Like JAL there are **no** register operands — the immediate is carried in the
adapter; unlike JAL the chip additionally commits `is_auipc` (and the `addend` column, in the output
`UTypeColumns`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.JTypeReader F
  is_auipc : F
deriving ProvableStruct

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand of the chip's `AddOperation` for AUIPC (`pc + imm`). -/
def pcWord (cols : UTypeColumns (ZMod p)) : Word (ZMod p) :=
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
def Spec (input : Inputs (ZMod p)) (cols : UTypeColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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

open Extracted (JalrColumns)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
def rs1Word (cols : JalrColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand of the link `AddOperation` (`pc + 4 = link`). -/
def pcWord (cols : JalrColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- Semantic contract for the JALR row, composed from the I-type reader sub-`Spec` plus the
`is_real`-gated jump/link semantics. On a real row: the jump target `add_operation.value = rs1 + op_c_imm`
(`op_c_imm` is the sign-extended 12-bit immediate — the `BitVec 12` ↔ word relation is a received decode
fact, supplied at the Sail bridge), the `lsb` witness is binary, and — when `rd ≠ x0` (`op_a_0 = 0`) — the
link-address write `op_a_operation.value = pc + 4`. The committed next_pc is the LSB-cleared
`nextPcWord`. The final conjunct records that this cleared low limb (`add_operation.value[0] - lsb`)
is divisible by 4 — i.e. the jump target is 4-byte aligned — forced by the in-circuit alignment
`Range` byte-lookup (`(value[0] - lsb) · 4⁻¹ < 2^14`); the Sail bridge lifts it to the whole word.
Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : JalrColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
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
  (input.is_real = 1 → (cols.add_operation.value[0] - cols.lsb).val % 4 = 0)

end SP1Clean.JalrChip

namespace SP1Clean.BranchChip

open Extracted (BranchColumns)
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
def rs1Word (cols : BranchColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_a_memory.prev_value[0], cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2], cols.adapter.op_a_memory.prev_value[3]]

/-- The rs2 register value as a 4-limb word — the `op_b` source read's prior value. -/
def rs2Word (cols : BranchColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
     cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand both of the chip's `AddOperation`s add to (`pc + imm = taken target`, `pc + 4 = fall-through`). -/
def pcWord (cols : BranchColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The committed `next_pc` (three 16-bit limbs) padded to a 4-limb word. -/
def nextPcWord (cols : BranchColumns (ZMod p)) : Word (ZMod p) :=
  #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2], 0]

/-- The reconstructed branch opcode `Σ is_b* · k` (BEQ 40 … BGEU 45), fed to the program-bus read. -/
def branchOpcode (cols : BranchColumns (ZMod p)) : ZMod p :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 + cols.is_bge * 43
    + cols.is_bltu * 44 + cols.is_bgeu * 45

/-- The six opcode flags and the `is_branching` decision are all binary. -/
def flagsBinary (cols : BranchColumns (ZMod p)) : Prop :=
  (cols.is_beq = 0 ∨ cols.is_beq = 1) ∧ (cols.is_bne = 0 ∨ cols.is_bne = 1) ∧
  (cols.is_blt = 0 ∨ cols.is_blt = 1) ∧ (cols.is_bge = 0 ∨ cols.is_bge = 1) ∧
  (cols.is_bltu = 0 ∨ cols.is_bltu = 1) ∧ (cols.is_bgeu = 0 ∨ cols.is_bgeu = 1) ∧
  (cols.is_branching = 0 ∨ cols.is_branching = 1)

/-- Semantic contract for the Branch row, composed from the immutable I-type reader sub-`Spec`, the proven
binary facts, and the `is_real`-gated branch semantics. The next_pc value is split into a *provable* half
(gated by `is_branching` — the two `AddOperation` targets) and a *compare-dependent* half (the six-way
flag-dispatched decision relating `is_branching` to the RISC-V condition on rs1/rs2, routed through the
skeletal `LtOperationSigned`). On a real row:
- if `is_branching = 1`, `next_pc = pc + op_c_imm` (the sign-extended offset is a received decode fact,
  supplied at the Sail bridge); if `is_branching = 0`, `next_pc = pc + 4`;
- and `is_branching` is taken iff the opcode's condition holds (`BEQ ↔ rs1 = rs2`, `BLT ↔ rs1 <ₛ rs2`, …).
Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : BranchColumns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ITypeReaderImmutable.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := branchOpcode cols } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  flagsBinary cols ∧
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
        (Word.toBitVec64 (rs1Word cols)).ult (Word.toBitVec64 (rs2Word cols)) = false)))

end SP1Clean.BranchChip
