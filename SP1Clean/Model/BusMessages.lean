import SP1Clean.Math.Word
import Clean.Circuit.Basic
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Bus message types (the low layer below both the channels and the semantic predicates)

The `ProvableStruct` message tuples of SP1's dynamic buses — State, Memory, Program — plus the
**structural** (program-independent, execution-independent) per-row predicates over them
(`Spec`/`isU64`/`RowSpec`). Extracted from `Model/Channels.lean` so this layer sits *below* the
semantic-execution predicates (`Model/Semantics/Truth.lean` — `StateTruth`/`MemTruth`/`ProgTruth`),
which need these message types: with the messages here, `Truth` imports this file (not `Channels`), and
`Channels` can then wire the semantic predicates into the channel `Guarantees` without an import cycle.

Namespace is `SP1Clean.Channels` (unchanged), so every `Channels.StateMsg`/`.MemoryMsg.isU64`/… name
resolves exactly as before — this is a pure relocation. The channel *definitions* stay in
`Model/Channels.lean`; the byte bus's `ByteRow`/`ByteRowSpec` stay in `Model/ByteTable.lean`. -/

namespace SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The State-bus message — `(clk_high, clk_low, pc0, pc1, pc2)`, arity 5, matching SP1's
`AirInteraction.state` (`crates/hypercube/src/lookup/interaction.rs`) and the `.state` interaction in
`Extracted/CPUState.lean`. Each CPU/ALU row receives the current `(clk, pc)` and sends the next. -/
structure StateMsg (F : Type) where
  clk_high : F
  clk_low : F
  pc0 : F
  pc1 : F
  pc2 : F
deriving ProvableStruct

/-- Per-row well-formedness of a State message: **`True`**. SP1's `CPUState::eval`
(`crates/core/machine/src/adapter/state.rs:90-98`) range-checks *only* the clock (`clk_0_16` 13-bit Range
+ `clk_16_24` U8Range) — **it does not range-check `pc`** (the `receive_state`/`send_state` pass `cols.pc`/
`next_pc` un-bounded). So the State *send* proves no local guarantee; the pc-limb bounds are *received*
facts (the previous row's send / the verifier-committed initial pc via the PC chain, and the program ROM),
exactly like the register-index bounds. The cross-row PC chain stays the trace level
(`Soundness/StateConsistency.lean`). -/
def StateMsg.Spec (_ : StateMsg (ZMod p)) : Prop := True

/-- The Memory-bus message — `(clk_high, clk_low, addr0, addr1, addr2, value)`, where `value : Word` is
the 4-limb little-endian word; `ProvableStruct` flattens it to the same arity-9 element tuple, matching
SP1's `AirInteraction.memory` (`crates/hypercube/src/lookup/interaction.rs`) and the `.memory`
interaction in `Extracted/RTypeReader.lean`. Registers use `addr0` = register index, `addr1 = addr2 = 0`.
Each register access sends the prior value at the previous timestamp and receives the new value at the
current timestamp. -/
structure MemoryMsg (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F
deriving ProvableStruct

/-- Per-row register-access address shape (`addr1 = addr2 = 0`). Kept as a small structural predicate (e.g.
for trace use); it is **not** the memory channel's `Guarantees` — see `memoryChannel`. -/
def MemoryMsg.Spec (msg : MemoryMsg (ZMod p)) : Prop :=
  msg.addr1 = 0 ∧ msg.addr2 = 0

/-- **The Memory message's value well-formedness** — the 4-limb `value` word is a `U64` (each limb
`< 2^16`), literally `Word.isU64`. This is the per-message `Guarantees` the memory **provider proves on
push** (a writer's range-check) and the chips **pull-and-derive** (W11 polarity flip), exactly analogous
to `ProgramMsg.RowSpec` / the byte bus. Because the message carries the whole `Word`, the pull guarantee
and the chips' operand facts are the *same* proposition — no per-limb bridging. -/
def MemoryMsg.isU64 (msg : MemoryMsg (ZMod p)) : Prop :=
  Word.isU64 msg.value

/-- The Program-bus message — the arity-16 instruction-fetch tuple `(pc0, pc1, pc2, opcode, op_a,
op_b0..3, op_c0..3, op_a_0, imm_b, imm_c)`, matching SP1's `AirInteraction.program`
(`crates/hypercube/src/lookup/interaction.rs`, `InteractionKind::Program => 16`) and the `.send
(.program …)` in `Extracted/RTypeReader.lean`. `op_b`/`op_c` are the two operands as 4-limb words; for an
R-type row only the register-index limb is non-zero (`op_b1..3 = op_c1..3 = imm_b = imm_c = 0`). -/
structure ProgramMsg (F : Type) where
  pc0 : F
  pc1 : F
  pc2 : F
  opcode : F
  op_a : F
  op_b0 : F
  op_b1 : F
  op_b2 : F
  op_b3 : F
  op_c0 : F
  op_c1 : F
  op_c2 : F
  op_c3 : F
  op_a_0 : F
  imm_b : F
  imm_c : F
deriving ProvableStruct

/-- Per-row well-formedness of a Program message — the part a CPU row can **send-prove locally** for *any*
adapter type. The only genuinely send-local fact is that `op_a_0` is boolean (from the reader's
unconditional `op_a_0 * (op_a_0 - 1) = 0` gate). Everything else is a **decode** fact that belongs on the
**receive** side (`ProgramChip.ProgramRowSpec`), not the send-side channel `Guarantees`. -/
def ProgramMsg.Spec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a_0 = 0 ∨ msg.op_a_0 = 1

/-- **The Program message's per-row well-formedness** — the decode facts that hold for a validly-decoded
ROM row of *any* instruction type: the destination register index `op_a < 32`, the pc limbs `< 2^16`, and
`op_a_0` boolean. This is the per-message `Guarantees` the **ROM provider proves on push** and the chips
**pull-and-derive** (W11 polarity flip) — program-INDEPENDENT, exactly analogous to
`byteChannel.Guarantees = ByteRowSpec`. The *program-specific* membership (`inROM` — the fetch is in
*this* committed program) is the finished-channel **balance** fact, not a per-message guarantee (see
`Soundness/ProgramConsistency.lean`). -/
def ProgramMsg.RowSpec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a.val < 32 ∧
  msg.pc0.val < 2 ^ 16 ∧ msg.pc1.val < 2 ^ 16 ∧ msg.pc2.val < 2 ^ 16 ∧
  (msg.op_a_0 = 0 ∨ msg.op_a_0 = 1)

end SP1Clean.Channels
