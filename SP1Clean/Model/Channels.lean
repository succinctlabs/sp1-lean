import SP1Clean.Model.BusMessages
import SP1Clean.Model.ByteTable
import SP1Clean.Math.Word
import SP1Clean.Math.Gate
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

/-- The structural State interaction channel (SP1 `InteractionKind.State`).  Its local predicate is
`True`: a row may emit its current/next `(clock, pc)` records, but reachability is not a fact that either
side can prove row-locally.  Global balance, schedule ordering, and per-chip transition lemmas are
combined by the timed grounding engine to derive execution semantics. -/
def stateChannel : Channel (ZMod p) StateMsg where
  name := "SP1State"
  Guarantees _ _ := True

/-- The Memory channel (SP1 `InteractionKind.Memory`). `Guarantees := MemoryMsg.isU64` — the value's
well-formedness (each limb `< 2^16`). **W11 polarity flip:** the memory access's *read-back/write* now
`pushIf`-pushes (proving `isU64` — a writer's ALU-result range-check for `op_a`; the just-pulled read-prior
guarantee for an `op_b`/`op_c` read-back), and the *read-prior* `pullIf`-pulls (deriving `isU64`), so the
operand `isU64` is *derived* by the consuming chip rather than carried as a chip-level `Assumptions`
precondition — the byte/program-bus model. SP1's Rust *sends* the read-prior (`+is_real`); our pull emits
`−is_real`, so our Memory interactions match SP1's extracted oracle **up to per-channel multiplicity
negation** (a sound LogUp sign symmetry, bridged in the `Faithful/*` Memory anchors). The cross-row
offline-memory *value-correctness* (read = last write) stays trace-level (`Soundness/MemoryConsistency.lean`);
this channel carries only the value's `isU64`. The `name` matches the `"SP1Memory"` key in `memoryLookups`. -/
def memoryChannel : Channel (ZMod p) MemoryMsg where
  name := "SP1Memory"
  Guarantees msg _ := MemoryMsg.isU64 msg

/-- The Program channel (SP1 `InteractionKind.Program`). `Guarantees := ProgramMsg.RowSpec` — the rich
decode well-formedness (indices `< 32`, pc `< 2^16`, `op_a_0` boolean). **W11 polarity flip:** the ROM
provider now `pushIf`-pushes valid program rows (proving `ProgramMsg.RowSpec`) and the CPU readers
`pullIf`-pull (deriving it), so the decode bounds are *derived* by consumers — the byte-bus model. SP1's
Rust genuinely *sends* program (`+1`); our pull emits `−1`, so our Program interactions match SP1's
extracted oracle **up to per-channel multiplicity negation** (a sound LogUp sign symmetry — the balance is
invariant under negating one channel's multiplicities; the divergence is bridged, FV-checked, in the
`Faithful/*` Program anchors). The `name` matches the `"SP1Program"` key in `programLookups`.

The channel carries only the structural `RowSpec`.  Agreement with the committed ROM (`ProgTruth`) is
derived globally from the provider table, program commitment, and interaction balance; it is not a
local channel assumption. -/
def programChannel : Channel (ZMod p) ProgramMsg where
  name := "SP1Program"
  Guarantees msg _ := ProgramMsg.RowSpec msg

/-- The Byte channel (SP1 `InteractionKind.Byte`), lookups into the preprocessed `ByteChip`/`RangeChip`.
Its `Guarantees` is `ByteRowSpec`, the byte-table membership predicate — and **Byte is the root of
arithmetic lookup facts** (`docs/bus-model.md` §7). The byte receiver is a *preprocessed static table*
whose rows satisfy `ByteRowSpec` by construction, so a consumer can soundly **pull** and obtain the
lookup fact locally. Memory and Program likewise expose only row-local hygiene (`isU64` and `RowSpec`);
State is the sole structural channel with `Guarantees := True`.
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
lemma interactionsWith_subcircuit_formal {F : Type} [FiniteField F] {Input Output : TypeMap}
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

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Name-distinctness at the `RawChannel` layer. -/
private lemma rawChannel_eq_false_of_name_ne {rc1 rc2 : RawChannel (ZMod p)}
    (h : rc1.name ≠ rc2.name) : (rc1 = rc2) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  exact h (by rw [he])

-- Per-pair `= False` instances (`@[circuit_norm]`) for every ordered pair of distinct buses a channel
-- list or `interactionsWith` filter can compare — kept as pre-instantiated simp rules so the
-- `if i.channel = channel` conditions reduce without record expansion.
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_stateChannel_false :
    ((byteChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, stateChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma stateChannel_eq_byteChannel_false :
    ((stateChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, stateChannel]; decide)
-- State vs Memory / Program — needed wherever a chip's `exposedChannels` filter must drop the
-- memory/program interactions.
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma stateChannel_eq_memoryChannel_false :
    ((stateChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, memoryChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma memoryChannel_eq_stateChannel_false :
    ((memoryChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, memoryChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma stateChannel_eq_programChannel_false :
    ((stateChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, programChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_stateChannel_false :
    ((programChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, programChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_memoryChannel_false :
    ((byteChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [byteChannel, memoryChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma byteChannel_eq_programChannel_false :
    ((byteChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, programChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_memoryChannel_false :
    ((programChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, memoryChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma memoryChannel_eq_programChannel_false :
    ((memoryChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, memoryChannel, programChannel]; decide)
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma memoryChannel_eq_byteChannel_false :
    ((memoryChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [memoryChannel, byteChannel])
omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_byteChannel_false :
    ((programChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, byteChannel]; decide)

-- Reusable disequalities for the State exposure proofs.  Keeping these once at the channel boundary
-- avoids every chip reopening the `RawChannel` record merely to filter its non-State interactions.
omit [Fact (2 ^ 17 < p)] in
lemma byteChannel_toRaw_ne_stateChannel :
    (byteChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
  intro h
  have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
  simp only [Channel.toRaw_name, byteChannel, stateChannel] at hn
  exact (by decide : ("SP1Byte" : String) ≠ "SP1State") hn

omit [Fact (2 ^ 17 < p)] in
lemma programChannel_toRaw_ne_stateChannel :
    (programChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
  intro h
  have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
  simp only [Channel.toRaw_name, programChannel, stateChannel] at hn
  exact (by decide : ("SP1Program" : String) ≠ "SP1State") hn

omit [Fact (2 ^ 17 < p)] in
lemma memoryChannel_toRaw_ne_stateChannel :
    (memoryChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw := by
  intro h
  have hn := congrArg (fun c : RawChannel (ZMod p) => c.name) h
  simp only [Channel.toRaw_name, memoryChannel, stateChannel] at hn
  exact (by decide : ("SP1Memory" : String) ≠ "SP1State") hn

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
lemma getElem_toElements_eval_varFromOffset {F : Type} [FiniteField F] {α : TypeMap} [ProvableStruct α]
    (e : Environment F) (off i : ℕ) (hi : i < size α) :
    (toElements (Eval.eval e (ProvableStruct.varFromOffset α off : α (Expression F))))[i]
      = e.get (off + i) := by
  rw [← ProvableStruct.varFromOffset_eq_varFromOffset, ProvableType.eval_varFromOffset,
    ProvableType.toElements_fromElements, Vector.getElem_mapRange]

end SP1Clean
