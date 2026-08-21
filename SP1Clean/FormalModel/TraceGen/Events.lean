import SP1Clean.Math.Word

/-! # Trace generation — the semantic events of the register-adapter families

The completeness direction of the AIR needs a *source of rows*: a real SP1 execution produces a
list of instruction events, SP1's `generate_trace` turns each into a row, and the AIR is supposed
to hold on the result. `ToClean/Air/TableBuild.lean` supplies the generic half of that chain (a
component builds a valid row from any semantic input satisfying its `ProverAssumptions`); this
directory supplies the SP1 half — the *event* a real trace is made of, the typed row it builds,
and the proof that the built row satisfies the chip's `ProverAssumptions`.

This file is the first piece: the **event record** and its **well-formedness**, both stated in
plain `ℕ` (executor data), with no field element and no column layout in sight. `Inputs.lean`
turns an event into a typed chip input; `Readers.lean` proves the reader-family contracts of the
blocks it builds.

## Why one record for a whole family

The register-adapter families — not the chips — determine what an event must carry. `RTypeEvent`
is the `Extracted.RTypeReader` family: three register operands, `op_a` written, `op_b`/`op_c`
read. That is the shape of the **R-type ALU chips** (`Add`, `Sub`, `Subw`, `Mul`, `DivRem`), which
is why the record — and every lemma stated over the blocks built from it — is shared, and only
the final three-line assembly into a particular chip's `Inputs` is per-chip.

The three sibling adapters get sibling records here, one per family, differing only in the `op_c`
slot and in how many register accesses the row makes:

| record | chips of the family | `op_c` slot | register accesses |
| --- | --- | --- | --- |
| `RTypeEvent` | Add, Sub, Subw, Mul, DivRem | `rs2` register read | 3 |
| `ITypeEvent` | Addi, Branch, Jalr, the 9 memory chips | 64-bit immediate | 2 |
| `ALUTypeEvent` | Addw, Bitwise, Lt, ShiftLeft, ShiftRight | either, per `imm_c` | 2 or 3 |
| `JTypeEvent` | Jal, UType | 64-bit immediate | 1 |

`ALUTypeEvent` is the only one whose row shape is *row-dependent*: SP1's `ALUTypeRecord` carries
`c : Option<MemoryRecordEnum>`, and `ALUTypeReader::populate` either fills the `op_c` access block
from that record (register row, `imm_c = 0`) or copies the immediate into `prev_value` and zeroes
both timestamp columns (immediate row, `imm_c = 1`). Its `WellFormed` therefore has two conjuncts
gated on `immC = 0` — the only gated conjuncts in this file, and each is gated exactly because the
fact it states is about a register access that an immediate row does not make.

## What the record deliberately does *not* carry

- **The result.** An ALU row's output word is *generated* — it is the chip circuit's own witness
  payload, computed by `Native/Operations/…/Populate.lean` from the operands — so supplying it
  would be supplying something the builder must not be trusted with. `Inputs.lean` builds only the
  `size Inputs` committed input cells; `Air.Flat.Component.buildRow` computes the rest.
- **`is_real`.** Real rows are built with `is_real = 1`; SP1's zero padding to a power-of-two
  height is a separate (and much weaker) obligation, discharged once by
  `TraceGen.addPaddingInputs` in `Inputs.lean`.

Provenance of the numbers quoted below (paths relative to the sibling `sp1` checkout, at the
pinned semantic revision): `crates/core/executor/src/lib.rs` — `pub const CLK_INC: u32 = 8`; and
`crates/core/executor/src/events/memory.rs` — `enum MemoryAccessPosition { UntrustedInstruction =
0, Memory = 1, C = 2, B = 3, A = 4 }`, the intra-window offsets at which the row's register
accesses are timestamped. `Model/Semantics/MicroTime.lean` names the same two constants for the
grounding engine (`ordinaryClkInc`, `regEffectOffset`); this layer keeps the offsets as literals
so that it does not have to import the Sail-dependent semantics substrate. -/

namespace SP1Clean.TraceGen

/--
One executed **R-type ALU instruction**, exactly the executor data SP1's `generate_trace` reads
for such a row: the CPU state (`clk`, `pc`), the decoded opcode, the three register indices, the
two source values, the value the destination register currently holds, and the timestamps of each
register's previous access.

Everything is a canonical `ℕ` — a trace event, not a row: no field elements, no limb splitting,
no timestamp differences. `Inputs.lean` performs all of that.
-/
structure RTypeEvent where
  /-- The row's CPU clock — SP1's global execution clock at this instruction (`AluEvent::clk`).
  The bus messages use its low 24 bits; `clk >>> 24` is the committed `clk_high`. -/
  clk : ℕ
  /-- The program counter this instruction was fetched from (48 bits, three u16 limbs). -/
  pc : ℕ
  /-- The executor's opcode discriminant. The *input columns are opcode-independent* — the R-type
  adapter commits no opcode column, and the opcode reaches the AIR through the Program-bus fetch —
  so the builder ignores it. It is carried here because the multi-opcode chips of this family
  (`Bitwise`, `Lt`, `Mul`, `DivRem`, the shifts) select their variant flags / `ProverHint` from
  it. -/
  opcode : ℕ
  /-- The destination register index `rd` (`op_a`). -/
  opA : ℕ
  /-- The first source register index `rs1` (`op_b`). -/
  opB : ℕ
  /-- The second source register index `rs2` (`op_c`). -/
  opC : ℕ
  /-- The value read from `rs1`. -/
  b : ℕ
  /-- The value read from `rs2`. -/
  c : ℕ
  /-- The value `rd` held before this instruction overwrote it (`MemoryRecordEnum::
  previous_record` of the `op_a` **write**). It is committed because the offline-memory argument
  must be handed back the record the write displaces. -/
  prevA : ℕ
  /-- The timestamp of the previous access to `rd`. -/
  prevTsA : ℕ
  /-- The timestamp of the previous access to `rs1`. -/
  prevTsB : ℕ
  /-- The timestamp of the previous access to `rs2`. -/
  prevTsC : ℕ

namespace RTypeEvent

/--
**What makes an event a real trace event.** Every conjunct is a fact about SP1's *execution* —
none is a fact about a circuit.

Six of them are what the built row's `ProverAssumptions` needs (`clk_mod`, `opA_ne_zero`,
`opA_lt`, and the three `prevTs*_lt`). The other six — `pc_lt`, `opB_lt`, `opC_lt`, `b_lt`,
`c_lt`, `prevA_lt` — are the *faithfulness* half: they are what makes the built row **mean** the
event, since a value that did not fit would be silently truncated by the limb split. They are not
cited by `AddChip.proverAssumptions_of_event`, and are kept because everything downstream of it
(the Sail bridge, the Program-bus decode facts) needs them.

The conjuncts, and the trace fact each encodes (the field docstrings repeat this beside each):

* `clk_mod` — the executor starts the clock at 1 and advances it by `CLK_INC = 8` per
  instruction, so every instruction's clock is `≡ 1 (mod 8)`.
* `pc_lt` — the program counter is a 48-bit address (SP1 commits it as three u16 limbs).
* `opA_lt` / `opB_lt` / `opC_lt` — register indices name one of the 32 architectural registers.
* `opA_ne_zero` — the destination is not `x0`. RISC-V discards writes to `x0`, and SP1 routes
  `rd = x0` ALU instructions to the separate `AluX0` chip, whose row sets `op_a_0 = 1`; so this
  is the *routing* condition that says the event belongs to this chip at all.
* `b_lt` / `c_lt` / `prevA_lt` — register contents are 64-bit values.
* `prevTsA_lt` / `prevTsB_lt` / `prevTsC_lt` — timestamps strictly increase, so each register's
  previous access is strictly earlier than *this* row's access to it: `op_a` is written at
  `clk + 4`, `op_b` read at `clk + 3`, `op_c` read at `clk + 2` (`MemoryAccessPosition`).

Not present, deliberately. (i) Nothing about limbs, differences, or ranges of *derived* columns:
the `isU64` of every committed word, the `< 2^16` of every limb, the `< 2^24` of every committed
previous-access clock, and the two byte-decomposition bounds of every timestamp difference are all
**derived** in `Readers.lean` — they are properties of the builder, not demands on the trace.
(ii) No separate "this row's accesses stay inside the current 24-bit clock window" conjunct: that
is a *consequence* of `clk_mod`, not an extra demand (`TraceGen.clk_window_of_mod`).
-/
structure WellFormed (e : RTypeEvent) : Prop where
  /-- The clock is `≡ 1 (mod 8)`: the executor's `CLK_INC = 8` discipline, starting at 1 (syscall
  rows advance by `264 = 8 · 33`, which preserves it). This is what the `CPUState` row's 13-bit
  range check on `(clk_0_16 - 1) / 8` records — and it is *also* what keeps this row's register
  accesses (at `clk + 1 … clk + 4`) inside the current 24-bit clock window, since the largest
  `≡ 1 (mod 8)` value below `2^24` is `2^24 - 7` (`TraceGen.clk_window_of_mod`). -/
  clk_mod : e.clk % 8 = 1
  /-- The program counter is a 48-bit address. -/
  pc_lt : e.pc < 2 ^ 48
  /-- `rd` is an architectural register index. -/
  opA_lt : e.opA < 32
  /-- `rs1` is an architectural register index. -/
  opB_lt : e.opB < 32
  /-- `rs2` is an architectural register index. -/
  opC_lt : e.opC < 32
  /-- `rd ≠ x0` — the `rd = x0` form of an ALU instruction is executed by the `AluX0` chip. -/
  opA_ne_zero : e.opA ≠ 0
  /-- `rs1`'s content is a 64-bit value. -/
  b_lt : e.b < 2 ^ 64
  /-- `rs2`'s content is a 64-bit value. -/
  c_lt : e.c < 2 ^ 64
  /-- `rd`'s displaced content is a 64-bit value. -/
  prevA_lt : e.prevA < 2 ^ 64
  /-- `rd`'s previous access is strictly before this row's write of it (at `clk + 4`). -/
  prevTsA_lt : e.prevTsA < e.clk + 4
  /-- `rs1`'s previous access is strictly before this row's read of it (at `clk + 3`). -/
  prevTsB_lt : e.prevTsB < e.clk + 3
  /-- `rs2`'s previous access is strictly before this row's read of it (at `clk + 2`). -/
  prevTsC_lt : e.prevTsC < e.clk + 2

end RTypeEvent

/-! ## The I-type family

`Extracted.ITypeReader`: `op_a` written, `op_b` read, and `op_c` a **decoded immediate** rather
than a register — so an I-type row makes only two register accesses, at `MemoryAccessPosition`
offsets `A = 4` and `B = 3`. -/

/--
One executed **I-type instruction** (`ITypeRecord`): the CPU state, the decoded opcode, the two
register indices, the 64-bit immediate, the `rs1` value, the value `rd` currently holds, and the
two previous-access timestamps.

Same shape as `RTypeEvent` with the `op_c` register triple (`opC`, `c`, `prevTsC`) replaced by the
single field `imm`. Serves `Addi` today; `Branch`, `Jalr` and the nine memory chips read the same
adapter.
-/
structure ITypeEvent where
  /-- The row's CPU clock (`clk`); the bus messages use its low 24 bits. -/
  clk : ℕ
  /-- The program counter this instruction was fetched from (48 bits, three u16 limbs). -/
  pc : ℕ
  /-- The executor's opcode discriminant. The input columns are opcode-independent (the opcode
  reaches the AIR through the Program-bus fetch), so the builder ignores it; it is carried for the
  multi-opcode chips of this family (`Branch`, the loads and stores). -/
  opcode : ℕ
  /-- The destination register index `rd` (`op_a`). -/
  opA : ℕ
  /-- The source register index `rs1` (`op_b`). -/
  opB : ℕ
  /-- The decoded immediate (`ITypeRecord::op_c`, a `u64` — already sign-extended by the decoder).
  It is committed as the four-limb word `op_c_imm`, and is *not* a register read. -/
  imm : ℕ
  /-- The value read from `rs1`. -/
  b : ℕ
  /-- The value `rd` held before this instruction overwrote it. -/
  prevA : ℕ
  /-- The timestamp of the previous access to `rd`. -/
  prevTsA : ℕ
  /-- The timestamp of the previous access to `rs1`. -/
  prevTsB : ℕ

namespace ITypeEvent

/--
**What makes an event a real I-type trace event.** As `RTypeEvent.WellFormed`, minus the three
`op_c` register conjuncts and plus `imm_lt`; every conjunct is a fact about SP1's *execution*.

The conjuncts, and the trace fact each encodes:

* `clk_mod` — the executor's `CLK_INC = 8` discipline, starting at 1.
* `pc_lt` — the program counter is a 48-bit address.
* `opA_lt` / `opB_lt` — register indices name one of the 32 architectural registers.
* `opA_ne_zero` — the destination is not `x0` (those rows are routed to a separate chip).
* `imm_lt` — the decoded immediate is a 64-bit value; SP1's decoder sign-extends it to `u64`
  before it reaches the record, so the committed word is the immediate, untruncated.
* `b_lt` / `prevA_lt` — register contents are 64-bit values.
* `prevTsA_lt` / `prevTsB_lt` — timestamps strictly increase, so each register's previous access
  is strictly earlier than this row's access to it (`op_a` written at `clk + 4`, `op_b` read at
  `clk + 3`).

Nothing about limbs, differences, or ranges of derived columns, and no clock-window conjunct: as
for `RTypeEvent`, those are consequences of the builder and of `clk_mod` (`clk_window_of_mod`).
-/
structure WellFormed (e : ITypeEvent) : Prop where
  /-- The clock is `≡ 1 (mod 8)`: the executor's `CLK_INC = 8` discipline, starting at 1. -/
  clk_mod : e.clk % 8 = 1
  /-- The program counter is a 48-bit address. -/
  pc_lt : e.pc < 2 ^ 48
  /-- `rd` is an architectural register index. -/
  opA_lt : e.opA < 32
  /-- `rs1` is an architectural register index. -/
  opB_lt : e.opB < 32
  /-- `rd ≠ x0` — the `rd = x0` form is executed by a separate chip. -/
  opA_ne_zero : e.opA ≠ 0
  /-- The decoded immediate is a 64-bit value. -/
  imm_lt : e.imm < 2 ^ 64
  /-- `rs1`'s content is a 64-bit value. -/
  b_lt : e.b < 2 ^ 64
  /-- `rd`'s displaced content is a 64-bit value. -/
  prevA_lt : e.prevA < 2 ^ 64
  /-- `rd`'s previous access is strictly before this row's write of it (at `clk + 4`). -/
  prevTsA_lt : e.prevTsA < e.clk + 4
  /-- `rs1`'s previous access is strictly before this row's read of it (at `clk + 3`). -/
  prevTsB_lt : e.prevTsB < e.clk + 3

end ITypeEvent

/-! ## The ALU-type family

`Extracted.ALUTypeReader`: the immediate-capable ALU adapter. `op_a` is written and `op_b` read as
always, but the `op_c` slot is a **four-limb word plus its own access block**, and the committed
`imm_c` flag says which of the two forms the row is in. -/

/--
One executed **ALU-type instruction** (`ALUTypeRecord`): as `RTypeEvent`, plus the `imm_c` flag
that distinguishes the register-register form from the immediate-`c` form.

`opC` carries whichever the row is in: on a register row (`immC = 0`) it is the `rs2` **index** and
`c` is the value read from it; on an immediate row (`immC = 1`) it is the decoded 64-bit
**immediate**, the row makes no `op_c` access, and `c` / `prevTsC` are unused. That is exactly
`ALUTypeRecord`'s `op_c : u64` together with `c : Option<MemoryRecordEnum>`.
-/
structure ALUTypeEvent where
  /-- The row's CPU clock (`clk`); the bus messages use its low 24 bits. -/
  clk : ℕ
  /-- The program counter this instruction was fetched from (48 bits, three u16 limbs). -/
  pc : ℕ
  /-- The executor's opcode discriminant — ignored by the builder (the input columns are
  opcode-independent), carried for the multi-opcode chips of this family (`Bitwise`, `Lt`, the
  shifts). -/
  opcode : ℕ
  /-- The destination register index `rd` (`op_a`). -/
  opA : ℕ
  /-- The first source register index `rs1` (`op_b`). -/
  opB : ℕ
  /-- The `op_c` operand: the `rs2` register **index** on a register row (`immC = 0`), the decoded
  64-bit **immediate** on an immediate row (`immC = 1`). Committed as a four-limb word either way
  (`ALUTypeReader::populate`'s `self.op_c = Word::from(record.op_c)`). -/
  opC : ℕ
  /-- `1` on an immediate-`c` row (`ALUTypeRecord::c.is_none()`), `0` on a register row. -/
  immC : ℕ
  /-- The value read from `rs1`. -/
  b : ℕ
  /-- The value read from `rs2` on a register row (unused on an immediate row). -/
  c : ℕ
  /-- The value `rd` held before this instruction overwrote it. -/
  prevA : ℕ
  /-- The timestamp of the previous access to `rd`. -/
  prevTsA : ℕ
  /-- The timestamp of the previous access to `rs1`. -/
  prevTsB : ℕ
  /-- The timestamp of the previous access to `rs2` (unused on an immediate row). -/
  prevTsC : ℕ

namespace ALUTypeEvent

/--
**What makes an event a real ALU-type trace event.** As `RTypeEvent.WellFormed`, plus `immC_bool`,
and with the two `op_c`-*register* conjuncts gated on `immC = 0` — an immediate row makes no
`op_c` register access, so there is no index to bound and no previous access to order.

The conjuncts, and the trace fact each encodes:

* `clk_mod` — the executor's `CLK_INC = 8` discipline, starting at 1.
* `pc_lt` — the program counter is a 48-bit address.
* `opA_lt` / `opB_lt` — register indices name one of the 32 architectural registers.
* `opA_ne_zero` — the destination is not `x0` (those rows are routed to `AluX0`).
* `immC_bool` — `imm_c` is a flag: `ALUTypeReader::populate` sets it from
  `record.c.is_none()`.
* `opC_lt` — the `op_c` operand fits the committed four-limb word, in **either** form (a register
  index trivially, a decoded immediate because the decoder produced a `u64`).
* `opC_reg` — on a **register** row the `op_c` operand is an architectural register index. This is
  the faithfulness half for `opC`: the memory access the reader emits uses `op_c[0]` as its
  register address.
* `b_lt` / `c_lt` / `prevA_lt` — register contents are 64-bit values.
* `prevTsA_lt` / `prevTsB_lt` — timestamps strictly increase, so `rd`'s and `rs1`'s previous
  accesses are strictly before this row's (at `clk + 4` / `clk + 3`).
* `prevTsC_reg` — on a **register** row, likewise for `rs2` (read at `clk + 2`). Gated: on an
  immediate row `ALUTypeReader::populate` never calls `populate_timestamp` for the `op_c` slot —
  it zeroes both timestamp columns — and the reader's `op_c` guarantee is gated off by
  `is_real - imm_c`, so there is no ordering fact to state.

As for `RTypeEvent`: no limb, difference, or range conjuncts (all derived in `Readers.lean`), and
no clock-window conjunct (a consequence of `clk_mod`).
-/
structure WellFormed (e : ALUTypeEvent) : Prop where
  /-- The clock is `≡ 1 (mod 8)`: the executor's `CLK_INC = 8` discipline, starting at 1. -/
  clk_mod : e.clk % 8 = 1
  /-- The program counter is a 48-bit address. -/
  pc_lt : e.pc < 2 ^ 48
  /-- `rd` is an architectural register index. -/
  opA_lt : e.opA < 32
  /-- `rs1` is an architectural register index. -/
  opB_lt : e.opB < 32
  /-- `rd ≠ x0` — the `rd = x0` form of an ALU instruction is executed by the `AluX0` chip. -/
  opA_ne_zero : e.opA ≠ 0
  /-- `imm_c` is a flag. -/
  immC_bool : e.immC = 0 ∨ e.immC = 1
  /-- The `op_c` operand fits the committed four-limb word, in either form. -/
  opC_lt : e.opC < 2 ^ 64
  /-- On a register row, `rs2` is an architectural register index. -/
  opC_reg : e.immC = 0 → e.opC < 32
  /-- `rs1`'s content is a 64-bit value. -/
  b_lt : e.b < 2 ^ 64
  /-- `rs2`'s content is a 64-bit value. -/
  c_lt : e.c < 2 ^ 64
  /-- `rd`'s displaced content is a 64-bit value. -/
  prevA_lt : e.prevA < 2 ^ 64
  /-- `rd`'s previous access is strictly before this row's write of it (at `clk + 4`). -/
  prevTsA_lt : e.prevTsA < e.clk + 4
  /-- `rs1`'s previous access is strictly before this row's read of it (at `clk + 3`). -/
  prevTsB_lt : e.prevTsB < e.clk + 3
  /-- On a register row, `rs2`'s previous access is strictly before this row's read of it (at
  `clk + 2`). -/
  prevTsC_reg : e.immC = 0 → e.prevTsC < e.clk + 2

end ALUTypeEvent

/-! ## The J-type family

`Extracted.JTypeReader`: `op_a` written, and **both** `op_b` and `op_c` decoded immediates — so a
J-type row makes a single register access, the `op_a` write at `MemoryAccessPosition::A = 4`. -/

/--
One executed **J-type instruction** (`JTypeRecord`): the CPU state, the decoded opcode, the
destination register index, the two decoded 64-bit immediates, the value `rd` currently holds, and
the timestamp of `rd`'s previous access.

The two immediates are opcode-specific — for `Jal` they are the jump offset and the link value,
for `UType` `op_b` is the U-type immediate `sign_extend(imm << 12)` and `op_c` is zero — so this
record bounds them and nothing more; a chip that needs the *shape* of its immediate states it
separately (see `JTypeEvent.UTypeImm`).
-/
structure JTypeEvent where
  /-- The row's CPU clock (`clk`); the bus messages use its low 24 bits. -/
  clk : ℕ
  /-- The program counter this instruction was fetched from (48 bits, three u16 limbs). -/
  pc : ℕ
  /-- The executor's opcode discriminant. The `UType` chip's `is_auipc` selector is built from it
  (`AUIPC = 48`, `LUI = 49`); the input columns are otherwise opcode-independent. -/
  opcode : ℕ
  /-- The destination register index `rd` (`op_a`). -/
  opA : ℕ
  /-- The decoded `op_b` immediate (`JTypeRecord::op_b`, a `u64`), committed as `op_b_imm`. -/
  immB : ℕ
  /-- The decoded `op_c` immediate (`JTypeRecord::op_c`, a `u64`), committed as `op_c_imm`. -/
  immC : ℕ
  /-- The value `rd` held before this instruction overwrote it. -/
  prevA : ℕ
  /-- The timestamp of the previous access to `rd`. -/
  prevTsA : ℕ

namespace JTypeEvent

/--
**What makes an event a real J-type trace event.** The shortest of the four: one register access,
two immediates.

The conjuncts, and the trace fact each encodes:

* `clk_mod` — the executor's `CLK_INC = 8` discipline, starting at 1.
* `pc_lt` — the program counter is a 48-bit address.
* `opA_lt` — `rd` names one of the 32 architectural registers.
* `opA_ne_zero` — the destination is not `x0`. (`UType` rows with `rd = x0` are real, and the
  chip's AIR handles them through `op_a_0 = 1`; this layer's completeness theorem covers the
  `rd ≠ x0` rows, exactly as the chip's `ProverAssumptions` asks with `op_a_0 = 0`.)
* `immB_lt` / `immC_lt` — the decoded immediates are 64-bit values, so the committed words are
  them, untruncated.
* `prevA_lt` — `rd`'s displaced content is a 64-bit value.
* `prevTsA_lt` — timestamps strictly increase, so `rd`'s previous access is strictly before this
  row's write of it (at `clk + 4`).
-/
structure WellFormed (e : JTypeEvent) : Prop where
  /-- The clock is `≡ 1 (mod 8)`: the executor's `CLK_INC = 8` discipline, starting at 1. -/
  clk_mod : e.clk % 8 = 1
  /-- The program counter is a 48-bit address. -/
  pc_lt : e.pc < 2 ^ 48
  /-- `rd` is an architectural register index. -/
  opA_lt : e.opA < 32
  /-- `rd ≠ x0` — the rows this layer's completeness theorem covers. -/
  opA_ne_zero : e.opA ≠ 0
  /-- The decoded `op_b` immediate is a 64-bit value. -/
  immB_lt : e.immB < 2 ^ 64
  /-- The decoded `op_c` immediate is a 64-bit value. -/
  immC_lt : e.immC < 2 ^ 64
  /-- `rd`'s displaced content is a 64-bit value. -/
  prevA_lt : e.prevA < 2 ^ 64
  /-- `rd`'s previous access is strictly before this row's write of it (at `clk + 4`). -/
  prevTsA_lt : e.prevTsA < e.clk + 4

end JTypeEvent

/-! ## The U-type immediate

`JTypeEvent.WellFormed` bounds the two immediates but says nothing about their *shape*, because
the two chips of the family decode them differently. `UType` is the one that needs the shape: its
`ProverAssumptions` carries the decode relation `toBitVec64 op_b_imm = RV64.lui (immOf adapter)`,
which is false for an arbitrary 64-bit `op_b`. The fact that makes it true is a plain-`ℕ`
statement about the executor's own decoder, so it is stated here rather than assumed in the
circuit layer. -/

/-- The 64-bit value SP1's decoder puts in a U-type row's `op_b`: the 20-bit U-immediate shifted
left by 12 and **sign-extended** to 64 bits. This is what `Instruction::encode` re-derives and
checks on the way back out (`OPCODE_AUIPC | OPCODE_LUI`: `sign_extended_imm = op_b >> 12`, plus
the `u64::MAX - 2^52 + 1` correction when `op_b ≥ 2^32`, then
`validate_sign_extension(sign_extended_imm, 20)`), so a U-type `op_b` that is *not* of this shape
does not round-trip through the encoder and cannot come from a decoded program. -/
def luiImmNat (imm : ℕ) : ℕ :=
  if imm < 2 ^ 19 then imm * 4096 else imm * 4096 + (2 ^ 64 - 2 ^ 32)

/-- **The U-type row's decode shape.** The event's `op_b` immediate is `luiImmNat` of a genuine
20-bit U-immediate. Separate from `WellFormed` because it is *not* a J-type fact: `Jal` shares the
adapter and its `op_b` is a jump offset, not a shifted U-immediate. -/
def JTypeEvent.UTypeImm (e : JTypeEvent) : Prop :=
  ∃ imm < 2 ^ 20, e.immB = luiImmNat imm

/-! ## The memory family

The nine memory chips (`Load{Byte,Half,Word,Double}`, `LoadX0`, `Store{Byte,Half,Word,Double}`)
read the very same `Extracted.ITypeReader` adapter as `Addi` — `op_a`, `op_b` a register, `op_c` a
decoded immediate — and make **one access no register-adapter row makes**: an access to a RAM word
at the effective address `rs1 + imm`, timestamped at `MemoryAccessPosition::Memory = 1`.

That extra access is why the family gets its own record rather than two more fields on
`ITypeEvent`. An `Addi` row makes no RAM access, so a RAM cell's prior value and prior access
timestamp would be fields with no execution meaning on the record's existing user, and the address
conjuncts below are *false* for it (an `Addi` sum is an arbitrary 64-bit value, not a mapped
48-bit address). `MemoryEvent` therefore **extends** `ITypeEvent`: the adapter half is literally
the same record, built by the same `iTypeReaderCols`, and only the RAM half is new. -/

/--
One executed **memory instruction** (an `ITypeRecord` plus its RAM `MemoryRecordEnum`): the I-type
half verbatim, plus the 64-bit word the addressed RAM cell held before this row and the timestamp
of that cell's previous access.

The word is the full 8-byte cell even for a sub-word load: SP1's memory bus is word-granular, and
the sub-word behaviour (`offset_bit` selection and sign extension) is in-circuit, computed from
this cell and the address. `Inputs.lean` and the per-chip builders perform that selection, so the
record carries no `selected_*` field — those are *derived*, exactly like an ALU row's result.
-/
structure MemoryEvent extends ITypeEvent where
  /-- The 64-bit word the addressed (8-byte-aligned) RAM cell held before this row's access
  (`MemoryRecordEnum::previous_record().value`). -/
  prevMem : ℕ
  /-- The timestamp of the previous access to that RAM cell
  (`MemoryRecordEnum::previous_record().timestamp`). -/
  prevTsMem : ℕ

namespace MemoryEvent

/-- The effective address: `rs1 + signExtend(imm)`, truncated to 64 bits — what SP1's executor
forms before it looks the cell up (`b.wrapping_add(c)`). The chips see it through the
`AddressOperation` gadget as `(Word.toNat op_b_val + Word.toNat op_c_imm) % 2 ^ 64`, which
`TraceGen.addr_eq` identifies with this. -/
def addr (e : MemoryEvent) : ℕ := (e.b + e.imm) % 2 ^ 64

/--
**What makes an event a real memory trace event.** The I-type conjuncts verbatim, plus five facts
about the RAM access. Every one is a fact about SP1's *execution*; none is a fact about a circuit.

* `toITypeWellFormed` — the I-type half (`ITypeEvent.WellFormed`): the `CLK_INC = 8` clock
  discipline, the pc and register-index bounds, `rd ≠ x0`, the 64-bit operand bounds, and the two
  register timestamp orderings.
* `clk_lt` — the execution clock is a 48-bit value. Two `populate` narrowings depend on this and
  on nothing else: `CPUState::populate` commits `(clk >> 24) as u32`, and — the one this family
  needs — `MemoryAccessTimestamp::populate_timestamp` commits the **cross-window** gap
  `current_high - prev_high - 1` as a 16-bit + `u8` limb pair, which is non-truncating exactly
  while `clk >> 24` is a 24-bit quantity. The register adapters owe no such conjunct because
  `RegisterAccessTimestamp::populate_timestamp` never compares high limbs: it zeroes `prev_low`
  across a window boundary instead. At `CLK_INC = 8` the bound is `2 ^ 45` executed instructions.
* `addr_lt` — the effective address is a 48-bit address: SP1's guest address space is 48-bit and
  the Memory bus keys on three u16 limbs.
* `addr_ge` — the address is above the reserved low 64 KiB. SP1's loader never maps that region
  and an access into it traps rather than producing a memory event, so a real row's address is
  `≥ 2 ^ 16`. (This is the fact `AddressOperation`'s `top_two_limb_inv` gate records: the inverse
  of `value[1] + value[2]` exists exactly when the address is not in the first page.)
* `prevMem_lt` — a RAM cell holds a 64-bit value.
* `prevTsMem_lt` — timestamps strictly increase, so the cell's previous access is strictly earlier
  than this row's, which happens at `MemoryAccessPosition::Memory = 1`, i.e. at `clk + 1`. SP1's
  own `populate_timestamp` asserts exactly this (`assert!(prev_timestamp < current_timestamp)`).

Not present, deliberately: nothing about limbs, timestamp differences, `compare_low`, the selected
sub-word, or the sign bit. All of those are computed by the builder — `Readers.lean` derives the
`MemoryAccess` contract from the five facts above, and each chip's `Complete.lean` derives its own
width's selection from the address and the cell. Nor is width **alignment** here: it is per-chip
(`Aligned` below), not per-family.
-/
structure WellFormed (e : MemoryEvent) : Prop where
  /-- The I-type half of the event is well-formed. -/
  toITypeWellFormed : e.toITypeEvent.WellFormed
  /-- The execution clock is a 48-bit value. -/
  clk_lt : e.clk < 2 ^ 48
  /-- The effective address is a 48-bit address. -/
  addr_lt : e.addr < 2 ^ 48
  /-- The address is above the reserved low 64 KiB. -/
  addr_ge : 2 ^ 16 ≤ e.addr
  /-- The addressed cell holds a 64-bit value. -/
  prevMem_lt : e.prevMem < 2 ^ 64
  /-- The cell's previous access is strictly before this row's, at `clk + 1`. -/
  prevTsMem_lt : e.prevTsMem < e.clk + 1

/--
**The `x0`-destination form.** SP1 routes a load whose destination register is `x0` to the separate
`LoadX0` chip, whose row sets `op_a_0 = 1` and *discards* the loaded value. The event is the same
record; exactly two facts change, and both are the routing condition itself:

* the destination **is** `x0` (`MemoryEvent.WellFormed` demands it is not), and
* the value that register held is `0` — RISC-V's `x0` reads as zero, which is precisely what the
  immutable adapter's four `op_a_0 · prev_value_i = 0` gates record.

Everything else — the clock discipline, the pc and `rs1` bounds, the immediate and operand bounds,
the two register timestamps, and all five RAM facts — is repeated from `WellFormed` rather than
gated on a flag the record does not carry.
-/
structure WellFormedX0 (e : MemoryEvent) : Prop where
  /-- The clock is `≡ 1 (mod 8)`: the executor's `CLK_INC = 8` discipline, starting at 1. -/
  clk_mod : e.clk % 8 = 1
  /-- The program counter is a 48-bit address. -/
  pc_lt : e.pc < 2 ^ 48
  /-- `rd` **is** `x0` — the routing condition that puts the event on this chip. -/
  opA_eq_zero : e.opA = 0
  /-- `rs1` is an architectural register index. -/
  opB_lt : e.opB < 32
  /-- The decoded immediate is a 64-bit value. -/
  imm_lt : e.imm < 2 ^ 64
  /-- `rs1`'s content is a 64-bit value. -/
  b_lt : e.b < 2 ^ 64
  /-- `x0` reads as zero. -/
  prevA_eq_zero : e.prevA = 0
  /-- `x0`'s previous access is strictly before this row's read of it (at `clk + 4`). -/
  prevTsA_lt : e.prevTsA < e.clk + 4
  /-- `rs1`'s previous access is strictly before this row's read of it (at `clk + 3`). -/
  prevTsB_lt : e.prevTsB < e.clk + 3
  /-- The execution clock is a 48-bit value. -/
  clk_lt : e.clk < 2 ^ 48
  /-- The effective address is a 48-bit address. -/
  addr_lt : e.addr < 2 ^ 48
  /-- The address is above the reserved low 64 KiB. -/
  addr_ge : 2 ^ 16 ≤ e.addr
  /-- The addressed cell holds a 64-bit value. -/
  prevMem_lt : e.prevMem < 2 ^ 64
  /-- The cell's previous access is strictly before this row's, at `clk + 1`. -/
  prevTsMem_lt : e.prevTsMem < e.clk + 1

/--
**Which load, and the alignment it requires.** The `LoadX0` chip serves all seven load opcodes at
once (`Opcode::{LB,LH,LW,LD,LBU,LHU,LWU}` = `29,30,31,35,32,33,34`), committing one selector per
variant, and its AIR gates the address's low bits per variant: `LD` forces all three offset bits to
zero, `LW`/`LWU` the low two, `LH`/`LHU` the lowest, and `LB`/`LBU` none. So the event needs both
halves of that fact — *which* of the seven it is, and the alignment RISC-V requires of it — and
they are naturally one predicate. (The single-variant chips take the alignment alone, as
`Aligned`; there the opcode is fixed by the chip.) -/
def IsLoad (e : MemoryEvent) : Prop :=
  (e.opcode = 29 ∨ e.opcode = 32)
    ∨ ((e.opcode = 30 ∨ e.opcode = 33) ∧ e.addr % 2 = 0)
    ∨ ((e.opcode = 31 ∨ e.opcode = 34) ∧ e.addr % 4 = 0)
    ∨ (e.opcode = 35 ∧ e.addr % 8 = 0)

/-- **The row's width alignment.** `LW`/`LWU` are 4-byte aligned, `LH`/`LHU` 2-byte, `LD` 8-byte,
`LB`/`LBU` not at all — so this is a fact about the *instruction*, not about the family, and is
stated separately for the same reason `JTypeEvent.UTypeImm` is: `MemoryEvent.WellFormed` is shared
by chips for which it is false. RISC-V requires naturally-aligned accesses and SP1's executor traps
a misaligned one instead of emitting a row, so a real row of a given width satisfies it. -/
def Aligned (e : MemoryEvent) (width : ℕ) : Prop := e.addr % width = 0

end MemoryEvent

end SP1Clean.TraceGen
