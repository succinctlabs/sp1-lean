import SP1Clean.Math.Word

/-! # Trace generation — the semantic event of the R-type ALU family

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
read. That is the shape of the **R-type ALU chips** (`Add`, `Sub`, `Mul`, `Bitwise`, `Lt`,
`DivRem`, `ShiftLeft`, `ShiftRight`, and the `W`-variants that read the R-type adapter), which is
why the record — and every lemma stated over the blocks built from it — is shared, and only the
final three-line assembly into a particular chip's `Inputs` is per-chip. The sibling adapters
(`ITypeReader`, `ALUTypeReader`, `JTypeReader`) get sibling records as their chips are rolled out;
they differ only in the `op_c` slot (an immediate rather than a register read) and in how many
register accesses the row makes.

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

end SP1Clean.TraceGen
