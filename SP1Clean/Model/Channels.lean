import SP1Clean.Model.ByteTable
import SP1Clean.Math.Word
import Clean.Circuit.Basic
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Cross-chip interaction channels (the bus, as the circuit actually emits it)

The shared Clean `Channel`s that the readers/chips `push`/`pull` to model SP1's cross-chip
interaction buses (`builder.send`/`receive`). Each `Channel` here is the Lean analog of one SP1
`InteractionKind`; emitting on it is the *real* in-circuit bus (vs. the hand-written trace-level
`*Lookups` shadows in `Soundness/`), so that `Soundness/*Consistency.lean` can eventually be
re-pointed at `Operations.interactionsWith <channel>` and the projections become theorems
(`interactionsWith_eq_of_mem_exposedChannels`). See `docs/bus-model.md`.

This module carries the **State** bus and the **Byte** bus (SP1's preprocessed `ByteChip`,
`Foundations/ByteTable.lean`), plus the **Program** and **Memory** channels. -/

namespace SP1Clean.Channels

open Circuit

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
exactly like the register-index bounds. The earlier `pc < 2^16` conjuncts here were discharged by divergent
`pc` byte checks in `Readers/CPUState.lean` that SP1 has no analog of; removed in the byte faithfulness
cleanup. The cross-row PC chain stays the trace level (`Soundness/StateConsistency.lean`). -/
def StateMsg.Spec (_ : StateMsg (ZMod p)) : Prop := True

/-- The State channel (SP1 `InteractionKind.State`). `Guarantees := StateMsg.Spec = True`: SP1's State
send proves no local well-formedness (it range-checks no pc; the clk checks are separate byte sends).
Emitted via `Channel.emit` so the `is_real` multiplicity (`+is_real` send / `-is_real`
receive / `0` padding) is preserved; padding owes nothing (post-#398 gated `toRaw`). The cross-row PC
chain stays the trace level (`Soundness/StateConsistency.lean`). -/
def stateChannel : Channel (ZMod p) StateMsg where
  name := "SP1State"
  Guarantees msg _ := StateMsg.Spec msg

/-- The Memory-bus message — `(clk_high, clk_low, addr0, addr1, addr2, v0, v1, v2, v3)`, arity 9,
matching SP1's `AirInteraction.memory` (`crates/hypercube/src/lookup/interaction.rs`) and the `.memory`
interaction in `Extracted/RTypeReader.lean`. Registers use `addr0` = register index, `addr1 = addr2 = 0`;
`(v0, v1, v2, v3)` is the 4-limb little-endian word. Each register access sends the prior value at the
previous timestamp and receives the new value at the current timestamp. -/
structure MemoryMsg (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  v0 : F
  v1 : F
  v2 : F
  v3 : F
deriving ProvableStruct

/-- Per-row register-access address shape (`addr1 = addr2 = 0`). Kept as a small structural predicate (e.g.
for trace use); it is **not** the memory channel's `Guarantees` — see `memoryChannel`. -/
def MemoryMsg.Spec (msg : MemoryMsg (ZMod p)) : Prop :=
  msg.addr1 = 0 ∧ msg.addr2 = 0

/-- The Memory channel (SP1 `InteractionKind.Memory`). `Guarantees := True`: the memory bus is **just the
balance** — the chip *emits* the per-row register interactions (`±is_real`) and the value's well-formedness
(`isU64`) is **not** a per-row channel fact. Operand `isU64` for a consuming ALU chip is a chip-level
**`Assumptions`** precondition (discharged at the machine/trace level from the offline-memory balance + the
writer), not forced into the channel — the idiomatic split (see `docs/bus-model.md` §7). The cross-row
offline-memory meaning stays trace-level (`Soundness/MemoryConsistency.lean`'s `TraceMemoryLink`). The `name`
matches the `"SP1Memory"` key in `memoryLookups`. -/
def memoryChannel : Channel (ZMod p) MemoryMsg where
  name := "SP1Memory"
  Guarantees _ _ := True

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
**receive** side (`ProgramChip.ProgramRowSpec`), not the send-side channel `Guarantees`:
the register-index **bounds** (`op_a < 32`, `op_b0`/`op_c0 < 2^16`), the opcode `trusted_instr` decode, the
`op_a_0 = 1 ↔ op_a = 0` decode, pc bounds/alignment, **and the R-type/I-type operand shape** (`op_b1..3 = 0`,
and for register-`c` ops `op_c1..3 = imm_c = 0`). The last point is why this is *not* `op_c1..3 = imm_c = 0`:
an immediate-`c` op (the `ALUTypeReader` adapter — `Addw`, `Lt`, `Bitwise`, shifts) legitimately sends a
non-zero `op_c` word with `imm_c = 1`, so the R/I-type shape cannot be a send guarantee; it is decoded on
receive. (`RTypeReader` still emits literal `0`s in those slots, so it proves the same — strictly weaker —
guarantee; nothing downstream consumes the dropped facts. ROM-membership stays trace-level,
`Soundness/ProgramConsistency.lean`.) -/
def ProgramMsg.Spec (msg : ProgramMsg (ZMod p)) : Prop :=
  msg.op_a_0 = 0 ∨ msg.op_a_0 = 1

/-- The Program channel (SP1 `InteractionKind.Program`). `Guarantees := ProgramMsg.Spec` (R-type shape +
`op_a_0` boolean). Emitted via `Channel.emit` (default `toRaw`, gated by `is_trusted` = `is_real` on Add):
the shape slots are literal `0` and `op_a_0` boolean comes from the reader's unconditional gate, so the send
proves the guarantee on every row. The index bounds + opcode decode are *received* from the decode/ProgramChip
(not a local send). The `name` matches the `"SP1Program"` key in `programLookups`. -/
def programChannel : Channel (ZMod p) ProgramMsg where
  name := "SP1Program"
  Guarantees msg _ := ProgramMsg.Spec msg

/-- The Byte channel (SP1 `InteractionKind.Byte`), lookups into the preprocessed `ByteChip`/`RangeChip`.
Its `Guarantees` is `ByteRowSpec`, the byte-table membership predicate — and **Byte is the root of
well-formedness** (`docs/bus-model.md` §7): unlike State/Memory/Program (dynamic buses → emit,
`Guarantees := True`), the byte receiver is a *preprocessed static table* whose rows satisfy `ByteRowSpec`
by construction, so it is the one bus where a consumer can soundly **pull** and obtain the fact locally.
A range check that *needs* its fact (`BitwiseOperation`'s `result = b op c`, `AddOperation`'s result range)
pulls `(op, value, w, 0)` and gets `ByteRowSpec`; a reader that only emits the check pulls-and-discards.
Gating is **multiplicity-gated** (`Channel.pullIf`, mult `-is_real`), faithful to SP1's
`send_byte(op, value, w, 0, is_real)`: the value is passed **raw** (no `is_real * value` fold) and padding
(`mult = 0`) drops out of the LogUp sum entirely (`mult / fingerprint(values)` with `mult = 0`), owing
nothing — post-#398 a receive owes no `Requirements` at all (`docs/bus-model.md` §7). The provider side is
`Chips/ByteChip.lean` (pushes the table, proves each row); until it lands the pull's justification is
threaded as `Soundness/ByteConsistency.lean`'s `TraceByteLink`. Pulled by
`Readers/{CPUState,RegisterAccessTimestamp,RegisterAccessCols,RTypeReader}.lean`. -/
def byteChannel : Channel (ZMod p) ByteRow where
  name := "SP1Byte"
  Guarantees msg _ := ByteRowSpec msg

open Classical in
/-- **Subcircuit interactions, kept in `interactionsWith` form.** Combines Clean's
`Operations.interactionsWith_subcircuit` (which exposes the raw `FlatOperation.interactions … |>.filter`)
with `FormalCircuit.toSubcircuit_interactions` (which rewrites that flat list back to the child `main`'s
operations). Keeping the result as `interactionsWith channel ((circuit.main input).operations n)` — rather
than the unfolded `.interactions.filter` — is what lets a child's bottom-up `interactionsWith_<chan>_eq`
rfl-lemma fire when a parent composes it (the readers' Memory/Program recovery, `docs/bus-model.md` §5/§7).
Tagged `circuit_norm` at **high priority** so it fires before Clean's more-general
`Operations.interactionsWith_subcircuit` (which would expose the raw `FlatOperation` form and lose the
fold). -/
@[circuit_norm high]
lemma interactionsWith_subcircuit_formal {F : Type} [Field F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (channel : RawChannel F) (circuit : FormalCircuit F Input Output)
    (input : Var Input F) (n : ℕ) (ops : Operations F) :
    Operations.interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      Operations.interactionsWith channel ((circuit.main input).operations n) ++
        Operations.interactionsWith channel ops := by
  rw [Operations.interactionsWith_subcircuit, FormalCircuit.toSubcircuit_interactions]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- Two channels with distinct `name`s have distinct `toRaw`s — as a `simp`-shaped `= False` so the
`interactionsWith` per-op `if i.channel = channel` conditions for a *different* bus reduce to the `else`
branch **without expanding the channel record** (which would break a child's bottom-up
`interactionsWith_<chan>_eq` rfl-lemma matching). (`omit`s the `2^17` fact so it applies wherever
`channelsLawful` does, e.g. under `Fact p.Prime` only.) -/
private lemma toRaw_eq_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRaw = c2.toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [← Channel.toRaw_name c1, ← Channel.toRaw_name c2, he])

-- Per-pair `= False` instances (`@[circuit_norm]`) for every ordered pair of distinct buses a channel
-- list or `interactionsWith` filter can compare — kept as pre-instantiated simp rules so the
-- `if i.channel = channel` conditions reduce without record expansion.
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_stateChannel_false :
    ((byteChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [byteChannel, stateChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma stateChannel_eq_byteChannel_false :
    ((stateChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [stateChannel, byteChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_memoryChannel_false :
    ((byteChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [byteChannel, memoryChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_programChannel_false :
    ((byteChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [byteChannel, programChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_memoryChannel_false :
    ((programChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [programChannel, memoryChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma memoryChannel_eq_programChannel_false :
    ((memoryChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [memoryChannel, programChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma memoryChannel_eq_byteChannel_false :
    ((memoryChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [memoryChannel, byteChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_byteChannel_false :
    ((programChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [programChannel, byteChannel])

-- These belong with Clean's `channels_lawful` default (`Clean/Circuit/Basic.lean`, which runs
-- `simp only [circuit_norm, seval]; try trivial`) — a pinned dep we don't edit — so we tag them here
-- instead. With them in `circuit_norm`, that default tactic closes every chip's channel-subset/membership
-- goal automatically, so a chip just **omits** `channelsLawful` (no hand-written override). See
-- `docs/agents/proof-patterns.md`. The mechanism: each circuit exposes its channel lists as `@[circuit_norm]`
-- rfl-lemmas right after its `elaborated` instance; `cons_subset`/`mem_cons`/`cons_ne_nil`/`not_mem_nil`/
-- `Subset.refl` then reduce the residual `⊆`/`∈` goals and `or_false`/`and_self` clean up the leftover
-- propositional skeleton (simp's built-in `rfl` closes the `chan = chan` leaves).
attribute [circuit_norm]
  List.cons_subset List.mem_cons List.cons_ne_nil List.not_mem_nil List.Subset.refl or_false and_self

end SP1Clean.Channels

namespace SP1Clean
open Circuit

/-- The `i`-th element of `toElements` of the eval of a `ProvableStruct`'s `varFromOffset` is just the
env value at `off + i` — via `eval_varFromOffset` (`= fromElements (mapRange (env.get ·))`) +
`toElements_fromElements` + `getElem_mapRange`, sidestepping the per-field `toElements` concatenation.

`ProvableType.witness` emits its output column var as `ProvableStruct.varFromOffset α off`, so this
matches a `populate`-witnessed column struct after `circuit_norm` normalisation: in a chip completeness
proof, `ext_iff` reduces `<witnessed cols> = populate …` to per-cell equalities, each of which this lemma
turns into `env.get (off + i)`, which the witness hint (`UsesLocalWitnessesCompleteness`) pins to
`(toElements (populate …))[i]`. Used by `BitwiseChip`; reusable for `MulChip`/`DivRemChip`. -/
lemma getElem_toElements_eval_varFromOffset {F : Type} [Field F] {α : TypeMap} [ProvableStruct α]
    (e : Environment F) (off i : ℕ) (hi : i < size α) :
    (toElements (Eval.eval e (ProvableStruct.varFromOffset α off : α (Expression F))))[i]
      = e.get (off + i) := by
  rw [← ProvableStruct.varFromOffset_eq_varFromOffset, ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]

end SP1Clean
