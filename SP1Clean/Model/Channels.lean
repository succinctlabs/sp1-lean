module

public import SP1Clean.Model.BusMessages
public import SP1Clean.Model.ByteTable
public import SP1Clean.Math.Word
public import SP1Clean.Math.Gate
public import Clean.Circuit.Basic
public import Clean.Circuit.Channel
public import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Cross-chip interaction channels (the bus, as the circuit actually emits it)

The shared Clean `Channel`s that the readers/chips `push`/`pull` to model SP1's cross-chip
interaction buses (`builder.send`/`receive`). Each `Channel` here is the Lean analog of one SP1
`InteractionKind`; emitting on it is the real in-circuit bus consumed directly by the typed
grounding layer. See `docs/architecture.md`.

This module carries the **State** bus and the **Byte** bus (SP1's preprocessed `ByteChip`,
`Model/ByteTable.lean`), plus the **Program** and **Memory** channels, the **Exit** channel, and
the **Syscall** and **PublicValues** channels.

Not every channel here corresponds to an SP1 `InteractionKind`. `Syscall` does (its upstream
consumer is `SyscallCore`); `Exit` and `PublicValues` do **not** — SP1 states those bindings as
direct chip-level `public_values` access, which Clean's flat AIR reserves to the verifier row, so
they are factored through channels instead (upstream Clean's `Air/Vm.lean` requires the same shape
of its own verifier). `docs/assurance.md` discloses that as a native-only bus.

The last two are **declared but not yet ensemble members**. `kindOf` classifies both, so adding
either to `sp1Ensemble` no longer risks folding it into State balance — but it does now owe
`Soundness.EnsembleChannels.channel_eq_of_kindOf_eq` a case, which is where the obligation belongs. -/

@[expose] public section

namespace SP1Clean.Channels

open Circuit
variable {p : ℕ} [Fact p.Prime]

/-- The structural State interaction channel (SP1 `InteractionKind.State`).  Its local predicate is
`True`: a row may emit its current/next `(clock, pc)` records, but reachability is not a fact that either
side can prove row-locally.  Global balance, schedule ordering, and per-chip transition lemmas are
combined by the timed grounding engine to derive execution semantics. -/
def stateChannel : Channel (ZMod p) StateMsg where
  name := "SP1State"
  Guarantees _ _ := True

/-- The Memory channel (SP1 `InteractionKind.Memory`). `Guarantees := MemoryMsg.isU64 ∧
MemoryMsg.ClkBound` — the value's well-formedness (each limb `< 2^16`) **and** the access clock's
24-bit bound. The clock conjunct is the one fact SP1's timestamp comparison needs but no accessing row
can prove: `eval_memory_access_timestamp` bounds only `clk_target − prev_low − 1`, so the *prior*
record's clock bound must be received from whoever pushed it (see `MemoryMsg.ClkBound`). Pushers prove
it from their `Readers.CPUState` clock byte bounds via `MemoryMsg.clkBound_of_cpuState_bounds`; the
memory-init provider proves it by constraining its pushed clock to `0` (SP1 hardcodes `Expr::zero()`
there, `crates/core/machine/src/memory/global.rs`). **W11 polarity flip:** the memory access's *read-back/write* now
`pushIf`-pushes (proving `isU64` — a writer's ALU-result range-check for `op_a`; the just-pulled read-prior
guarantee for an `op_b`/`op_c` read-back), and the *read-prior* `pullIf`-pulls (deriving `isU64`), so the
operand `isU64` is *derived* by the consuming chip rather than carried as a chip-level `Assumptions`
precondition — the byte/program-bus model. SP1's Rust *sends* the read-prior (`+is_real`); our pull emits
`−is_real`, so our Memory interactions match SP1's extracted oracle **up to per-channel multiplicity
negation** (a sound LogUp sign symmetry, bridged in the `Faithful/*` Memory anchors). The cross-row
offline-memory *value-correctness* (read = last write) is derived globally by the timed typed-memory
grounding layer (`Soundness/TypedMemory.lean`); this channel carries only the local `isU64` and clock
facts. The `name` matches the `"SP1Memory"` interaction key. -/
def memoryChannel : Channel (ZMod p) MemoryMsg where
  name := "SP1Memory"
  Guarantees msg _ := MemoryMsg.isU64 msg ∧ MemoryMsg.ClkBound msg

/-- The Program channel (SP1 `InteractionKind.Program`). `Guarantees := ProgramMsg.RowSpec` — the rich
decode well-formedness (indices `< 32`, pc `< 2^16`, `op_a_0` boolean). **W11 polarity flip:** the ROM
provider now `pushIf`-pushes valid program rows (proving `ProgramMsg.RowSpec`) and the CPU readers
`pullIf`-pull (deriving it), so the decode bounds are *derived* by consumers — the byte-bus model. SP1's
Rust genuinely *sends* program (`+1`); our pull emits `−1`, so our Program interactions match SP1's
extracted oracle **up to per-channel multiplicity negation** (a sound LogUp sign symmetry — the balance is
invariant under negating one channel's multiplicities; the divergence is bridged, FV-checked, in the
`Faithful/*` Program anchors). The channel name is the upstream table identity `"SP1Program"`.

The channel carries only the structural `RowSpec`.  Agreement with the committed ROM (`ProgTruth`) is
derived globally from the provider table, program commitment, and interaction balance; it is not a
local channel assumption. -/
def programChannel : Channel (ZMod p) ProgramMsg where
  name := "SP1Program"
  Guarantees msg _ := ProgramMsg.RowSpec msg

/-- The Byte channel (SP1 `InteractionKind.Byte`), lookups into the preprocessed `ByteChip`/`RangeChip`.
Its `Guarantees` is `ByteRowSpec`, the byte-table membership predicate — and **Byte is the root of
arithmetic lookup facts**. The byte receiver is a *preprocessed static table*
whose rows satisfy `ByteRowSpec` by construction, so a consumer can soundly **pull** and obtain the
lookup fact locally. Memory and Program likewise expose only row-local hygiene (`isU64` and `RowSpec`);
State is the sole structural channel with `Guarantees := True`.
A range check that *needs* its fact (`BitwiseOperation`'s `result = b op c`, `AddOperation`'s result range)
pulls `(op, value, w, 0)` and gets `ByteRowSpec`; a reader that only emits the check pulls-and-discards.
Gating is **multiplicity-gated** (`Channel.pullIf`, mult `-is_real`), faithful to SP1's
`send_byte(op, value, w, 0, is_real)`: the value is passed **raw** (no `is_real * value` fold) and padding
(`mult = 0`) drops out of the LogUp sum entirely (`mult / fingerprint(values)` with `mult = 0`), owing
nothing — post-#398 a receive owes no `Requirements` at all. The provider side is
`Proofs/Chips/ByteChip/` (pushes the table, proves each row); with it landed, the pull's justification
is closed by the native Byte/Range providers and ensemble balance; the exact/native artifact recounts
their demand in `Composition/PreprocessedProviders.lean`. Pulled by
`Readers/{CPUState,RegisterAccessTimestamp,RegisterAccessCols,RTypeReader}.lean`. -/
def byteChannel : Channel (ZMod p) ByteRow where
  name := "SP1Byte"
  Guarantees msg _ := ByteRowSpec msg

/-- The Exit channel — the native halt table's exit-code bus. It has no SP1 `InteractionKind`
counterpart: SP1's syscall chip constrains `public_values.exit_code` by direct chip-level
public-values access, which Clean's flat-AIR reserves to the designated verifier — so the native
ensemble factors that binding through one channel. The verifier pulls `⟨exit_code⟩` **ungated**
(its row is exactly the public input and can witness no gate cell); a real halt row pushes its
reduced `x10` word, a padding halt row pushes `⟨0⟩`, and balance alone forces the exit semantics
(see `ExitMsg`). `Guarantees := True` — like the State bus, the channel is purely structural: the
binding is a multiset fact, not a per-message predicate. -/
def exitChannel : Channel (ZMod p) ExitMsg where
  name := "SP1Exit"
  Guarantees _ _ := True

/-- The **halt hand-off** channel — native-only, and the mechanism that makes the exit code honest.

The verifier's `⟨exit_code⟩` pull is ungated, so its counterparty must be a one-row table; that is
`HaltChip` today, and its trick is a *gated pair* — a real row pushes the reduced `x10`, a padding
row pushes `⟨0⟩` — which forces `exit_code = 0` on every halt-free shard. **SP1 makes no such
restriction.** Upstream leaves `exit_code` free on a non-halting execution shard whose previous code
is zero; it is sticky once set and chained across shards by the verifier, never pinned within one
(`record.rs:1172-1193`, `prover/src/verify.rs:269-293`).

So the exit accounting is refactored across two tables and this channel. The successor table keeps
the ungated `⟨code⟩` push — so the one-row count is still forced — but the `code` it pushes is a
**witness cell**, constrained only by a gated pull on this channel. The `SyscallInstrs` table's
`is_halt` rows push here with their reduced `op_b`. Balance then says exactly what SP1 says: on a
halting shard the committed exit code is `a0`, and on a halt-free shard nothing constrains it.

Like `exitChannel`, `Guarantees := True`: the binding is a multiset fact, not a per-message
predicate. -/
def haltHandoffChannel : Channel (ZMod p) ExitMsg where
  name := "SP1HaltHandoff"
  Guarantees _ _ := True

/-- The Syscall channel — SP1's own syscall bus (`InteractionKind::Syscall`), the one new channel
here that is *not* native-only. Its payload is the existing `SyscallMsg`, the same carrier the
exact v6.4.0 lists project, so both models name this bus with one type.

Its consumer upstream is `SyscallCore`, which the supported profile excludes, so the native
ensemble declares the channel with **no provider**: balance then forces every send's multiplicity —
byte 1 of the syscall id, SP1's "this handler has its own table" flag — to zero, which is exactly
the statement that a supported shard uses only the syscalls `SyscallInstrs` handles inline.
`Guarantees := True`: as with State and Exit, the content is the multiset fact, not a per-message
predicate.

Both sides of a faithfulness anchor agree on this bus by name *and* by kind:
`Extracted.Interaction.toAccess` gives the generated `.raw .syscall` send the same `"SP1Syscall"`
name, and `kindOf` classifies it `InteractionKind.Syscall`. A whole-chip anchor compares exactly
that pair, so the agreement has to be deliberate rather than incidental. -/
def syscallChannel : Channel (ZMod p) SyscallMsg where
  name := "SP1Syscall"
  Guarantees _ _ := True

/-- The public-values channel — the second native-only bus, and the general form of what
`exitChannel` does for one cell. A chip-level assertion about `public_values` cannot be a row
constraint in Clean's flat AIR (a `Table` carries no `PublicIO`, and `Ensemble.tables` cannot
depend on one), so each such assertion is factored into one addressed-cell message; upstream
Clean's `Air/Vm.lean` `VmTables` requires the same shape of its verifier.

Declared with no provider for now, so balance forces the commit selectors to zero. `Guarantees :=
True` for the same reason as `exitChannel`: the binding is established by balance against the
verifier (or, once COMMIT is modelled, against a `PublicValues` provider), not row-locally. -/
def publicValuesChannel : Channel (ZMod p) PublicValueMsg where
  name := "SP1PublicValues"
  Guarantees _ _ := True

open Classical in
/-- **Subcircuit interactions, kept in `interactionsWith` form.** Combines Clean's
`Operations.interactionsWith_subcircuit` (which exposes the raw `FlatOperation.interactions … |>.filter`)
with `FormalCircuit.toSubcircuit_interactions` (which rewrites that flat list back to the child `main`'s
operations). Keeping the result as `interactionsWith channel ((circuit.main input).operations n)` — rather
than the unfolded `.interactions.filter` — is what lets a child's bottom-up `interactionsWith_<chan>_eq`
rfl-lemma fire when a parent composes it (the readers' Memory/Program recovery described in
`ToClean/Circuit/InteractionRecovery.lean`).
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

/-- Two channels with distinct `name`s have distinct `toRaw`s — as a `simp`-shaped `= False` so the
`interactionsWith` per-op `if i.channel = channel` conditions for a *different* bus reduce to the `else`
branch **without expanding the channel record** (which would break a child's bottom-up
`interactionsWith_<chan>_eq` rfl-lemma matching). (Carries no `2^17` magnitude fact — that variable is
not in scope in this file — so it applies wherever `channelsLawful` does, e.g. under `Fact p.Prime`
only.) -/
private lemma toRaw_eq_false_of_name_ne {M1 M2 : TypeMap} [ProvableType M1] [ProvableType M2]
    {c1 : Channel (ZMod p) M1} {c2 : Channel (ZMod p) M2} (h : c1.name ≠ c2.name) :
    (c1.toRaw = c2.toRaw) = False :=
  eq_false fun he => h (by rw [← Channel.toRaw_name c1, ← Channel.toRaw_name c2, he])

omit [Fact p.Prime] in
/-- Name-distinctness at the `RawChannel` layer. -/
private lemma rawChannel_eq_false_of_name_ne {rc1 rc2 : RawChannel (ZMod p)}
    (h : rc1.name ≠ rc2.name) : (rc1 = rc2) = False :=
  eq_false fun he => h (by rw [he])

-- Per-pair `= False` instances (`@[circuit_norm]`) for every ordered pair of distinct buses a channel
-- list or `interactionsWith` filter can compare — kept as pre-instantiated simp rules so the
-- `if i.channel = channel` conditions reduce without record expansion.
@[circuit_norm] lemma byteChannel_eq_stateChannel_false :
    ((byteChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, stateChannel]; decide)
@[circuit_norm] lemma stateChannel_eq_byteChannel_false :
    ((stateChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, stateChannel]; decide)
-- State vs Memory / Program — needed wherever a chip's `exposedChannels` filter must drop the
-- memory/program interactions.
@[circuit_norm] lemma stateChannel_eq_memoryChannel_false :
    ((stateChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, memoryChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_stateChannel_false :
    ((memoryChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, memoryChannel]; decide)
@[circuit_norm] lemma stateChannel_eq_programChannel_false :
    ((stateChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, programChannel]; decide)
@[circuit_norm] lemma programChannel_eq_stateChannel_false :
    ((programChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, programChannel]; decide)
@[circuit_norm] lemma byteChannel_eq_memoryChannel_false :
    ((byteChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [byteChannel, memoryChannel])
@[circuit_norm] lemma byteChannel_eq_programChannel_false :
    ((byteChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, programChannel]; decide)
@[circuit_norm] lemma programChannel_eq_memoryChannel_false :
    ((programChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, memoryChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_programChannel_false :
    ((memoryChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, memoryChannel, programChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_byteChannel_false :
    ((memoryChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  toRaw_eq_false_of_name_ne (by simp [memoryChannel, byteChannel])
@[circuit_norm] lemma programChannel_eq_byteChannel_false :
    ((programChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, byteChannel]; decide)
-- Exit vs the four established buses — both orders, for the halt table's filter conditions.
@[circuit_norm] lemma exitChannel_eq_byteChannel_false :
    ((exitChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, byteChannel]; decide)
@[circuit_norm] lemma byteChannel_eq_exitChannel_false :
    ((byteChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, exitChannel]; decide)
@[circuit_norm] lemma exitChannel_eq_stateChannel_false :
    ((exitChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, stateChannel]; decide)
@[circuit_norm] lemma stateChannel_eq_exitChannel_false :
    ((stateChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, exitChannel]; decide)
@[circuit_norm] lemma exitChannel_eq_programChannel_false :
    ((exitChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, programChannel]; decide)
@[circuit_norm] lemma programChannel_eq_exitChannel_false :
    ((programChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, exitChannel]; decide)
@[circuit_norm] lemma exitChannel_eq_memoryChannel_false :
    ((exitChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, memoryChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_exitChannel_false :
    ((memoryChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, memoryChannel, exitChannel]; decide)

-- The two native-only buses and SP1's syscall bus against every other channel: the same
-- pre-instantiated shape, so a whole-chip `interactionsWith` filter reduces without
-- reopening any channel record.
@[circuit_norm] lemma syscallChannel_eq_byteChannel_false :
    ((syscallChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, byteChannel]; decide)
@[circuit_norm] lemma byteChannel_eq_syscallChannel_false :
    ((byteChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, syscallChannel]; decide)
@[circuit_norm] lemma syscallChannel_eq_stateChannel_false :
    ((syscallChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, stateChannel]; decide)
@[circuit_norm] lemma stateChannel_eq_syscallChannel_false :
    ((stateChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, syscallChannel]; decide)
@[circuit_norm] lemma syscallChannel_eq_memoryChannel_false :
    ((syscallChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, memoryChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_syscallChannel_false :
    ((memoryChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, memoryChannel, syscallChannel]; decide)
@[circuit_norm] lemma syscallChannel_eq_programChannel_false :
    ((syscallChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, programChannel]; decide)
@[circuit_norm] lemma programChannel_eq_syscallChannel_false :
    ((programChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, syscallChannel]; decide)
@[circuit_norm] lemma syscallChannel_eq_exitChannel_false :
    ((syscallChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, exitChannel]; decide)
@[circuit_norm] lemma exitChannel_eq_syscallChannel_false :
    ((exitChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, syscallChannel]; decide)
@[circuit_norm] lemma syscallChannel_eq_publicValuesChannel_false :
    ((syscallChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, syscallChannel, publicValuesChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_syscallChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (syscallChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, syscallChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_byteChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (byteChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, byteChannel]; decide)
@[circuit_norm] lemma byteChannel_eq_publicValuesChannel_false :
    ((byteChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, byteChannel, publicValuesChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_stateChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, stateChannel]; decide)
@[circuit_norm] lemma stateChannel_eq_publicValuesChannel_false :
    ((stateChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, stateChannel, publicValuesChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_memoryChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (memoryChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, memoryChannel]; decide)
@[circuit_norm] lemma memoryChannel_eq_publicValuesChannel_false :
    ((memoryChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, memoryChannel, publicValuesChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_programChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, programChannel]; decide)
@[circuit_norm] lemma programChannel_eq_publicValuesChannel_false :
    ((programChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, programChannel, publicValuesChannel]; decide)
@[circuit_norm] lemma publicValuesChannel_eq_exitChannel_false :
    ((publicValuesChannel (p := p)).toRaw = (exitChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, publicValuesChannel, exitChannel]; decide)
@[circuit_norm] lemma exitChannel_eq_publicValuesChannel_false :
    ((exitChannel (p := p)).toRaw = (publicValuesChannel (p := p)).toRaw) = False :=
  rawChannel_eq_false_of_name_ne (by
    simp only [Channel.toRaw_name, exitChannel, publicValuesChannel]; decide)

-- Reusable disequalities for the State exposure proofs.  Keeping these once at the channel boundary
-- avoids every chip reopening the `RawChannel` record merely to filter its non-State interactions.
lemma byteChannel_toRaw_ne_stateChannel :
    (byteChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw :=
  of_eq_false byteChannel_eq_stateChannel_false

lemma programChannel_toRaw_ne_stateChannel :
    (programChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw :=
  of_eq_false programChannel_eq_stateChannel_false

lemma memoryChannel_toRaw_ne_stateChannel :
    (memoryChannel (p := p)).toRaw ≠ (stateChannel (p := p)).toRaw :=
  of_eq_false memoryChannel_eq_stateChannel_false

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
