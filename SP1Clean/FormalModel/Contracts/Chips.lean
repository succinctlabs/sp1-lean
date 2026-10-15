module

public import SP1Clean.FormalModel.Contracts.Operations
public import SP1Clean.FormalModel.Contracts.Readers
public import SP1Clean.Semantics.Specs.DivRem
public import SP1Clean.Circuits.Types.DivRem
public import SP1Clean.Circuits.Types.LtOperationSigned
public import SP1Clean.Circuits.Types.U16MSBOperation
public import SP1Clean.Semantics.ISA.RV64
public import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Shared chip contracts

Row types and semantic specifications awaiting separation into feature modules. Each contract
composes reader obligations with RV64 instruction semantics; multi-opcode chips select their
meaning through row flags. Operand order follows `f rs2_val rs1_val`, with `rs1` supplied by
`op_b_val` and `rs2` by `op_c_val`.

Multiplication has its own row types in `Circuits/Types/Mul` and contract in
`Semantics/Specs/Chips/Mul`; consumers import those modules directly.
-/


@[expose] public section

namespace SP1Clean.AddChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native Add-chip row.  Its arithmetic block follows the local Lean gadget, not Rust's
`AddOperation` type.  `Faithful.addChipReconfigure` is the explicit whole-chip bridge to the
extracted `AddCols` oracle.  The reader blocks remain layout-compatible while that migration proceeds. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
  add_operation : Circuits.Types.AddOperation F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (the committed
CPUState + register-adapter columns the chip reads). The `rs1`/`rs2` source operands are **not** separate
committed columns — they are projected from the adapter's register slots (`op_b_val`/`op_c_val` below), so
the chip's operand is *definitionally* the value the Memory bus pins. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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
extracted `AddiOracle.AddiCols` oracle.  The reader blocks also use the shared native column types. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ITypeReader F
  add_operation : Circuits.Types.AddOperation F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The `is_real` selector and the **threaded reader column blocks** `state`/`adapter` (the latter an
**I-type** `Circuits.Types.ITypeReader` carrying the immediate). The `rs1` source operand and the immediate
are **not** separate committed columns — they are projected from the adapter (`op_b_val`/`op_c_val`
below), so the chip's operands are *definitionally* the values the reader pins. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ITypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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

/-- Native Sub-chip row. The reader blocks reuse the project substrate; only the arithmetic block is
owned by the local Lean gadget. `Faithful.subChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
  sub_operation : SubOperation.Columns F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (as `AddChip`). The
`rs1`/`rs2` operands are projected from the adapter register slots — see `Inputs.op_b_val` below. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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
  exact (BitVec.setWidth_add y x (by omega)).symm

/-- Native ADDW-chip row. The reader blocks reuse the project substrate; only the arithmetic block is
owned by the local Lean gadget (two witnessed low limbs + the composed sign-bit block).
`Faithful.addwChipReconfigure` is the sole bridge to Rust's separately generated whole-chip
row. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ALUTypeReader F
  addw_operation : AddwOperation.Columns F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (ADDW's adapter is the
immediate-capable `ALUTypeReader`, unlike SUBW's `RTypeReader`). The
`rs1`/`rs2` operands are projected from the adapter register slots — see `Inputs.op_b_val` below. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ALUTypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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
`Faithful.subwChipReconfigure` is the sole bridge to Rust's separately generated whole-chip
row. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
  subw_operation : SubwOperation.Columns F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The `is_real` selector and the threaded reader column blocks `state`/`adapter` (as `SubChip`; SUBW's
adapter is the register `RTypeReader`). The `rs1`/`rs2` operands are projected — see `Inputs.op_b_val`. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.RTypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
(`Circuits.Types.AddOperation`); `Faithful.jalChipReconfigure` is the
explicit whole-chip bridge to the extracted `JalOracle.JalColumns` oracle.  The reader blocks
also use the shared native column types. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.JTypeReader F
  add_operation : Circuits.Types.AddOperation F
  op_a_operation : Circuits.Types.AddOperation F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The committed **J-type** row blocks the chip reads: the `is_real` selector, the CPUState block
`state` (clk + `pc`), and the J-type register adapter `adapter` (the destination `op_a`/`op_a_0`, its
`op_a_memory` timestamp, and the two immediate words `op_b_imm`/`op_c_imm`). Unlike the ALU chips there
are **no** `op_b_val`/`op_c_val` register operands — both source operands are immediates carried in the
adapter. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.JTypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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
(`Circuits.Types.AddOperation`); `Faithful.uTypeChipReconfigure` is the
explicit whole-chip bridge to the extracted `UTypeOracle.UTypeColumns` oracle.  The reader blocks
also use the shared native column types. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.JTypeReader F
  addend : Vector F 3
  add_operation : Circuits.Types.AddOperation F
  is_auipc : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The committed **U-type** row blocks the chip reads: the `is_real` selector, the CPUState block `state`
(clk + `pc`), the J-type register adapter `adapter` (the destination `op_a`/`op_a_0`, its `op_a_memory`
timestamp, and the two immediate words `op_b_imm`/`op_c_imm`), and the variant selector `is_auipc`
(`1` = AUIPC, `0` = LUI). Like JAL there are **no** register operands — the immediate is carried in the
adapter; unlike JAL the chip additionally commits `is_auipc` (and the `addend` column, in the output
`Columns`). -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.JTypeReader F
  is_auipc : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The program counter as a 4-limb word (the three committed `pc` limbs + a zero high limb): the `a`
operand of the chip's `AddOperation` for AUIPC (`pc + imm`). -/
def pcWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]

/-- The 20-bit U-type immediate recovered from the committed `op_b_imm` limbs (the high 20 bits of the
constrained 32-bit immediate). Appears identically in the chip's decode `Assumption` (LHS) and the `Spec`
(the `RV64.lui`/`RV64.auipc` argument), so the proofs never unfold its extraction formula. -/
def immOf (adapter : Circuits.Types.JTypeReader (ZMod p)) : BitVec 20 :=
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
(`Circuits.Types.AddOperation`); `Faithful.jalrChipReconfigure` is the
explicit whole-chip bridge to the extracted `JalrOracle.JalrColumns` oracle.  The reader blocks
also use the shared native column types. -/
structure Columns (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ITypeReader F
  add_operation : Circuits.Types.AddOperation F
  op_a_operation : Circuits.Types.AddOperation F
  lsb : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- The committed **I-type** row blocks the JALR chip reads: the `is_real` selector, the CPUState block
`state` (clk + `pc`), and the I-type register adapter `adapter` (the destination `op_a`/`op_a_0` with its
`op_a_memory` write timestamp, the **source register** `op_b` = rs1 with its `op_b_memory` read block, and
the immediate word `op_c_imm`). Unlike JAL the jump base is a register operand (rs1) carried in the
adapter's `op_b_memory.prev_value`, not the program counter. -/
structure Inputs (F : Type) where
  is_real : F
  state : Circuits.Types.CPUState F
  adapter : Circuits.Types.ITypeReader F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

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
fact, supplied at the Sail bridge) and — when `rd ≠ x0` (`op_a_0 = 0`) — the link-address write
`op_a_operation.value = pc + 4`. The committed next_pc is the LSB-cleared
`nextPcWord`. The penultimate conjunct records that this cleared low limb (`add_operation.value[0] - lsb`)
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
