# Bus model

This doc describes how `sp1-clean-native` models SP1's cross-chip **interaction ("bus")
arithmetic**, relates it to the upstream SP1 Rust source (the `sp1` checkout at `$SP1_DIR`, default
`../sp1`), and documents how it is built on the public Clean DSL's first-class `Channel`/`Table` machinery.

## 0. Current status

This section is the authoritative current state; the design-narrative below (§5) records the rationale
for how the model is structured.

- **Receiver chips + cross-chip closure (axiom-clean).** The three "secondary divergences" of
  §1 are addressed:
  - **Byte/Program receivers as predicate models.** `Chips/ByteChip.lean` (`ByteProvider`, every entry at
    a valid `ByteRowSpec` key; `byteRow_eq_of_key` — the key determines the row) and `Chips/ProgramChip.lean`
    (`ProgramProvider inROM`, `ProgramRowSpec` = register indices `< 32` + pc bounds + `op_a_0` binary — the
    *received* decode facts). `Soundness/{Byte,Program}Consistency.lean`'s `byteAccessValid_of_balance` /
    `programConsistent_of_balance` discharge `Trace{Byte,Program}Link` from *(provider + `isConsistentBalanced`)*
    via `InteractionBus.provider_touches_pos_send` (a positive real send must be cancelled by the provider).
  - **`RangeChip` split** (`Chips/ByteChip.lean`): SP1 receives the Byte bus with *two* preprocessed chips
    (`ByteChip` non-`Range` ⊕ `RangeChip` opcode-6), both via `receive_byte` — there is **no** separate
    `Range` `InteractionKind`. Modeled as `ByteOpRowSpec`/`RangeRowSpec` + `byteProvider_of_split`.
  - **Machine closure** (bespoke `Soundness/MachineConsistency.lean`'s `traceLinks_of_machineBalance` —
    discharging `TraceByteLink ∧ TraceProgramLink` from a single `TraceMachineBalancedWith` via
    `InteractionKind`-disjointness — was **retired 2026-06-05** with the bespoke `TraceValid` capstone; the
    gated capstone `Soundness/GatedVm/` derives the execution trail from the State-bus balance alone). The
    lone residual is `isConsistentBalanced` (the LogUp/GKR fact Clean can't model). Memory stays threaded
    (`TraceMemoryLink`, order-sensitive offline-memory) and State (`TraceStateLink`, whole-trace clock
    injectivity) — both genuinely not balance-derivable (= the §6 deferred math).
- **"emitted = projection".** State (the worked example), **Program** (`programLookups_eq_emitted`), **Memory**
  (`memoryLookups_eq_emitted`) are **done, axiom-clean** — the `*Lookups` are now *theorems* equal to the
  `toAccess`-image of the actual reader emissions, recovered through the composed `RTypeReader` by the
  toolkit in `Foundations/InteractionRecovery.lean` (`interactionsWith_main_eq_nil` drops the byte-only
  `RegisterAccessCols` subcircuits; `filter_interactions_formalAssertion_eq_nil` drops the `op_a_0` `===`
  gates; channel distinctness drops the other bus's emits). `toAccess` kernels in
  `Foundations/InteractionProjection.lean` are stated on `_root_.emitted` (the form `circuit_norm` leaves).
  Only the **Byte** `eq_emitted` remains — it needs a *recovery through* (not drop of) the byte-carrying
  `RAC ⊃ RAT` subcircuits + a `gatedReceive` kernel (the nested-recovery direction).
  - **Real 48-bit addresses (memory chips, done, axiom-clean).** The register memory bus above is
    `addr1 = addr2 = 0`. The `LoadDouble`/`StoreDouble` chips exercise the Memory bus at a **real 3-limb
    address** (`AddressOperation.value`) via the `Readers/MemoryAccess` block; `Soundness/MemoryConsistency.lean`
    projects it with `memAccessLookups` (send prior `+is_real` / receive new `−is_real`) + `memAccessEvent`
    (the offline event at the recombined `addr0+addr1·2^16+addr2·2^32`, read for a load / write for a store),
    with `memAccessLookups_padding` and `memAccessLookups_eq_emitted` (same `heq`/channel-distinctness recovery
    over `MemoryAccess.main`). It feeds the *same* `multiplicitySum` bus and `MemEvent`/`memoryConsistent`
    model — no data-model change; `TraceMemoryLink` (the offline-memory permutation) stays threaded.
- **Byte faithfulness.** SP1 source review (`adapter/state.rs:90-98`, `air/memory.rs:122-166`
  + `:332-360`) showed the readers emitted byte checks SP1 has no analog of. Removed: CPUState's 4 `pc`
  byte checks (SP1's CPUState range-checks only the clock) and `RegisterAccessCols`'s 4 `prev_value` checks
  (SP1's register-access read range-checks no value). Consequently **`StateMsg.Spec → True`** (pc bounds are
  received via the PC chain / program ROM) and **`RegisterAccessCols.Spec → True`** (operand `isU64` received
  from the writer). The readers now emit *exactly* SP1's 8 byte checks per Add row (CPUState 2 clk + 3×RAT 2
  timestamps) = `ByteConsistency.byteRows`. So the "ungated `byteChannel.pull` Range checks on pc /
  prev_value" described in §5 are **not divergences** (they were the same class as the deleted index range-checks).
- **Channel `Guarantees`:** byte/range = `ByteRowSpec` (load-bearing, `gatedReceive`); State/Memory =
  `True`; Program = `ProgramMsg.Spec` (the locally-send-provable R-type shape + `op_a_0` binary; the richer
  decode facts are *received*, on `ProgramChip.ProgramRowSpec`). So the `<Msg>.Spec` enrichment
  is settled: rich facts live on the **receive** side (the provider predicates), not forced onto sends.

## 1. The current model is two *disconnected* representations

> **Note:** §1 describes the *pre-channel baseline* this design record started from, retained for context.
> The State `Channel` (in `Readers/CPUState.lean` + `Chips/AddChip.lean`) and the static byte table
> (`Foundations/ByteTable.lean` + `byteChannel`) are in place — see §5. So (a) below is no longer literally
> true: `CPUState` now `push`/`pull`s `stateChannel`, and `RegisterAccessTimestamp`'s timestamp checks
> are `ByteTable` lookups rather than `Gadgets.ToBits.rangeCheck`. The `byteChannel` (in both
> readers) and `memoryChannel` + `programChannel` (both `emit`ted by `Readers/RTypeReader.lean`)
> are likewise in place, so **all four buses now emit in-circuit**. The remaining *gap* §1 identifies — the
> "emitted = projection" link (in-circuit emission vs. trace-level `*Lookups`) — is the only remaining
> disconnect.

**(a) In-circuit — what actually constrains the prover.** The readers
(`Readers/CPUState.lean`, `Readers/RTypeReader.lean`) emit only `is_real`-gated
`Gadgets.ToBits.rangeCheck`s and `assertZero`s; `Chips/AddChip.lean` composes them as
`subcircuit`s plus the `is_real` binary gate. There are **zero** Clean `Channel`/`interact`
operations anywhere under `SP1Clean/` — the circuit does not emit any bus interaction.

**(b) Trace-level — the multiset/LogUp argument.** `Foundations/InteractionBus.lean` is an
axiom-clean signed-multiset core: `InteractionKind` (State/Byte/Program/Memory), `LookupAccess =
InteractionKind × String × List ℕ × ℤ`, `multiplicitySum`, `isConsistentBalanced ⇔ Online`
(permutation-invariant). Per-bus modules `Soundness/{State,Program,Memory}Consistency.lean` each
define a **hand-written** projection `*Lookups : Trace.Row → LookupAccessList`, a proven
`*_padding` lemma (padding row ⇒ 0 multiplicity on every key), and a *threaded* hypothesis
`Trace*Link` (balance ⟹ pcChain / ROM membership / offline-memory).

**The gap.** Nothing connects (a) to (b). The `*Lookups` projections are hand-authored shadows,
tied to the circuit only by a code comment ("matches `Extracted/RTypeReader.lean:82` send
(.program …)"). In SP1's Rust, by contrast, `builder.send(...)`/`receive(...)` **are** the bus —
the `Interaction { values, multiplicity, kind, scope }` structs that LogUp consumes are literally
what each chip's `eval` emits; there is no shadow. The missing theorem, per bus `B` / reader `C`,
is **"emitted = projection":**

```
Operations.interactionsWith (busChannel B) ((C.main input).operations i₀)  =  ⟦ C's <B>Lookups row ⟧
```

Three secondary divergences all follow from this one root:

- **Static byte table not modeled.** SP1 chips do **not** range-check in-circuit; they
  `send_byte(op, a, b, c, mult)` into the Byte bus, whose receiver is the **preprocessed** ByteChip
  (256×256 = 65536 rows; ops AND/OR/XOR/U8Range/LTU/MSB), which receives with **count**
  multiplicities (`sp1/crates/core/machine/src/bytes/{air.rs,trace.rs,mod.rs}`). Our direct
  `rangeCheck` is an acknowledged divergence (`Operations/AddOperation.lean` range-checks the four
  result limbs directly instead of sending Byte interactions).
- **No `MachineAir` analog.** SP1's machine collects every chip's `sends()`/`receives()` and runs
  one batched LogUp/GKR permutation argument so that, per bus, Σsends = Σreceives
  (`sp1/crates/hypercube/src/air/machine.rs:18`, `logup_gkr/cpu.rs`). We have no object bundling
  (chip, sends, receives, included), so the cross-chip balance statement *cannot even be expressed*;
  each `Trace*Link` is threaded with the *other side absent* (e.g. the ProgramChip that receives the
  fetch).
- **Multiplicity is only ±`is_real` (binary).** Genuine counts (the byte-table receive side) and
  `InteractionScope` (Local vs Global / cross-shard) are unmodeled. `LookupAccess` already carries
  an `ℤ` multiplicity, so the core is ready — nothing exercises it.

## 2. The upstream model (the faithfulness target)

- **`MachineAir<F>`** (`sp1/crates/hypercube/src/air/machine.rs:18`) is implemented by ~63 chips.
  Relevant surface: `name`, `generate_trace`, `included`, `preprocessed_*` (the static-table hook),
  and the per-chip `Air::eval` that emits interactions.
- **`Interaction<F> { values: Vec<VirtualPairCol>, multiplicity: VirtualPairCol, kind, scope }`**
  (`lookup/interaction.rs:13`). Multiplicity is an affine column expression, not necessarily binary.
  `InteractionKind` has 18 variants (Memory=1, Program=2, Byte=5, State=7, Syscall=8, …);
  `InteractionScope ∈ {Local, Global}` distinguishes intra-shard LogUp from cross-shard digest
  accumulation.
- **`send`/`receive`** (`air/builder.rs`) push an `AirInteraction` onto the chip's `sends`/`receives`.
  The machine batches all buses into a single LogUp argument: per bus, Σ (m_i / fingerprint_i) over
  sends = Σ over receives. The ADD instruction's interactions: Program fetch (send), three Memory
  register accesses (op_a write, op_b/op_c read), and Byte range-checks (sent as `ByteLookupEvent`s);
  CPU State is a receive(pc)/send(next_pc) pair.
- **ByteChip is preprocessed/static.** `byte_table()` lists the 6 ops; the table's 65536 rows are
  generated once, independent of the program; other chips look up into it via Byte interactions and
  the ByteChip receives each with a **count** multiplicity column.

## 3. What Clean gives us to build on

Clean already provides first-class machinery that maps almost 1:1 to the upstream model
(`.lake/packages/Clean/Clean/Circuit/`):

- **`Channel F Message { name, Guarantees }`** + the Circuit-monad combinators
  `Channel.push` (mult `1`), `Channel.pull` (mult `-1`, `assumeGuarantees := true`),
  `Channel.emit mult msg` (`Basic.lean:131-146`). A `RawChannel` carries `Guarantees`/`Requirements`
  (the pull-vs-push soundness duality). These are SP1's `send`/`receive` + multiplicity + kind.
- **`Table` / `StaticTable { length, row, index, Spec, contains_iff }` + `Table.fromStatic`**
  (`Lookup.lean:18,125,151`), and the `Circuit.lookup table entry` combinator (`Basic.lean:124`).
  This is SP1's preprocessed ByteChip. **Already exercised in this repo:** `BitwiseU16Operation`
  does byte ops via Clean's proven `ByteXorTable` + `lookup` (`Operations/BitwiseU16Operation.lean`).
- **Recover-emitted API:** `Operations.interactionsWith (channel)` (`Operations.lean:434`,
  `noncomputable`) and `ElaboratedCircuit.interactionsWith_eq_of_mem_exposedChannels`
  (`Basic.lean:561`) — the kernel of an "emitted = projection" proof: a circuit that declares a
  channel in `exposedChannels` gets a theorem that its emitted interactions equal the declared list.

### Cost of the channel approach

A channel-emitting reader (a copy of `Readers/CPUState.lean` that emits a State `Channel.push` +
`Channel.pull`) builds with **zero diagnostics**, is **axiom-clean**
(`lean_verify` = `[propext, Classical.choice, Quot.sound]` on `soundness`/`completeness`/`circuit`,
no `sorryAx`), and closes at the **existing `2000000` heartbeat floor** (no bump). So the `Channel`
path is viable. The cost is **light per-circuit boilerplate**, not invisible: `interact` ops do touch the
proofs:

- A channel-emitting circuit must declare the channel in `channelsWithGuarantees` (if `pull`ed)
  and/or `channelsWithRequirements` (if `push`ed), optionally `exposedChannels` (for "emitted =
  projection"), and prove `channelsLawful`. The default `channelsLawful` tactic does **not** discharge
  when the `main` also contains `rangeCheck` (`assertion`) subcircuits — unfold the gadget chain so
  `simp` sees the subcircuits carry no channels. The working line:
  `simp only [main, Gadgets.ToBits.rangeCheck, Gadgets.toBits, circuit_norm]` (the
  `Clean/Examples/FemtoCairo` pattern; add `Boolean.circuit, seval, instLawfulCircuitChannel` for
  heavier gadgets).
- `circuit_proof_start` must be passed the channel def (`circuit_proof_start [<channel>]`) so it
  unfolds the channel `Guarantees`/`Requirements`. The `push`/`pull` add an `Operations.Requirements`
  tail to **soundness** — with `Guarantees := True` it closes with
  `exact ⟨Or.inl rfl, Or.inl rfl⟩` (the `rangeCheck` subcircuits expose no channels, so each
  conjunct's `… = [] ∨ …` left disjunct is `rfl`; the channel reqs are `1 ≠ -1 → True`).
  **Completeness is unchanged** from the channel-free reader — its witness proof is verbatim
  `Readers/CPUState.lean`. Channels that carry the bus's semantic content in `Guarantees` make
  the soundness Requirements tail load-bearing instead of `rfl`.
- `Operations.interactionsWith` is `noncomputable` — keep any def derived from it out of `decide`.

The canonical worked example for the whole pattern (channels + a `StaticLookupChannel` byte channel +
an end-to-end multiset `SoundEnsemble`) is `Clean/Examples/FibonacciWithChannels.lean`; for
`channelsLawful` with `assertion` subcircuits see `Clean/Examples/FemtoCairo/FemtoCairo.lean`. These
are the reference templates for the channel layer.

## 4. Recommended end-state

The circuit literally emits the bus, exactly as SP1 does:

1. Buses (State/Program/Memory) are Clean `Channel`s; byte ops go through a `StaticTable` ByteChip
   reached by a Byte `Channel`. Readers/operations `push`/`pull` with `mult = is_real` (or a count).
2. The hand-written `*Lookups` become **theorems** — derived from `interactionsWith` via
   `interactionsWith_eq_of_mem_exposedChannels` — so the trace-level multiset argument is about what
   the circuit *actually emits*, not a shadow.
3. A `MachineAir`-like record bundles each chip's circuit + sends + receives + `included`, making the
   cross-chip Σsends = Σreceives statement expressible (and the `Trace*Link`s dischargeable rather
   than merely threaded).

## 5. Channel-layer components

The components below build up the in-circuit bus, each axiom-clean
(`#print axioms` = `{propext, Classical.choice, Quot.sound}`, no `sorryAx`).

- **Channel feasibility.** A channel-emitting copy of `Readers/CPUState.lean` established that a
  `Channel.push`/`pull` closes axiom-clean at the existing heartbeat floor inside the reader recipe.
  *(Outcome recorded in §3 above.)*
- **State channel in the reader + chip.** `Foundations/Channels.lean` holds
  the shared `stateChannel`; `Readers/CPUState.lean` now emits the State `push`/`pull` (declaring
  `channelsWith{Guarantees,Requirements} := [stateChannel.toRaw]`, soundness Requirements tail closed
  by `Or.inl rfl`); `Chips/AddChip.lean` composes that channel-emitting subcircuit — its
  soundness/completeness proofs are **unchanged**, only `channelsLawful` + the chip's channel
  declarations were added. The `channelsLawful` recipe when one of several subcircuits emits a
  channel: `simp only [main, circuit_norm, <emitting-sub>.circuit, <emitting-sub>.elaborated]` (do
  **not** unfold the heavy non-emitting subcircuits — e.g. `RTypeReader.elaborated`, whose `main` now
  composes three `RegisterAccessCols` sub-circuits; cracking those open blows the whnf budget), then
  `exact ⟨List.Subset.refl _, List.Subset.refl _⟩` for the residual
  subset goals (the non-emitting subs' channel lists are the class-default `[]`). Both files
  axiom-clean.
- **Static byte table.** `Foundations/ByteTable.lean`: `ByteTable : Table` whose
  membership is the **defining predicate** `ByteRowSpec` (some `ByteOpcode` whose `idx` matches the
  opcode column and whose `constrain` semantics hold) — *not* an enumeration of the `7 * 2^16` rows
  (the `decide`-blowup is sidestepped exactly as Clean's own `ByteXorTable` sidesteps it: `Contains`
  is a predicate, `Soundness`/`Completeness` the class defaults). `Foundations/Channels.lean` gains
  `byteChannel` whose **`Guarantees` is load-bearing** — it *is* `ByteRowSpec`, so a `pull` yields
  byte-op correctness. A consumer demonstrator is included: `byteRangeCheck`, a `FormalAssertion`
  drop-in for `Gadgets.ToBits.rangeCheck 8` that asserts `x.val < 256` via `lookup ByteTable
  ⟨U8Range, x, 0, 0⟩` (SP1's `send_byte(U8Range, …)`), with `byteRowSpec_u8range` the membership
  characterization (`cast_eq_three` pins the opcode via `0..6` distinct mod `p`). All axiom-clean.
- **Byte channel in the readers.** Both readers reach the byte table through
  `byteChannel` instead of a `ByteTable` lookup: `Readers/CPUState.lean` (2 clock checks) and
  `Readers/RegisterAccessTimestamp.lean` (2 timestamp checks/operand, composed ×3 through
  `RTypeReader`) `byteChannel.pull ⟨op, is_real·value, width, 0⟩`, propagated through
  `Chips/AddChip.lean`; `Soundness/ByteConsistency.lean` is the trace-level projection
  (`byteLookups` + `byteAccessValid` + threaded `TraceByteLink` + `byteLookups_padding`), parallel to
  `StateConsistency`. The dead `byteRangeCheck`/`byteRangeCheckBits` `FormalAssertion` lookup wrappers
  were removed; `ByteTable`/`ByteRowSpec` + the membership lemmas stay (the channel's `Guarantees` *is*
  `ByteRowSpec`). **The send/receive direction:** the *consumer* **pulls** (`mult = -1`, gets
  the `ByteRowSpec` guarantee), and the provider side **pushes** — the coherent endpoint is a native
  `Chips/ByteChip.lean` that `push`es the table with count multiplicities and proves each row valid.
  **Impedance mismatch:** Clean fires `Guarantees` only at `mult = -1`, so a pull can't carry
  the gated `is_real` multiplicity — gating stays in the message (`is_real·value`), and byte-op
  correctness becomes *assumed from the bus* (discharged by the `ByteChip` + balance, threaded as
  `TraceByteLink`) rather than concluded by a lookup — parallel to State.
  **Open:** the `< 256` U8Range vs 13-/16-bit `Range` split (SP1's `Range` is a separate `RangeChip`, not the byte
  table — `ByteTable` currently conflates them via opcode 6); and the `U8Range` `a`-vs-`b` value-slot
  faithfulness (SP1 puts the value in `b`; the readers use `a` — pre-existing, flagged in
  `agents/proof-patterns.md`). `AddOperation`'s own limb range-checks are *not* yet on the byte bus.
- **Memory + Program channels; "emitted = projection".**
  **All four buses emit in-circuit.** `Foundations/Channels.lean` gains `memoryChannel` (`MemoryMsg`
  = the arity-9 tuple `(clk_high, clk_low, addr0, addr1, addr2, v0, v1, v2, v3)`) and `programChannel`
  (`ProgramMsg` = the arity-16 instruction-fetch tuple `(pc0..2, opcode, op_a, op_b0..3, op_c0..3,
  op_a_0, imm_b, imm_c)`), both with `Guarantees := True` (the cross-row meaning — offline-memory
  / ROM-membership — is the trace level: `Soundness/{Memory,Program}Consistency.lean`'s
  `Trace{Memory,Program}Link`). (The `<Msg>.Spec` enrichment of those guarantees is discussed below.)
  `Readers/RTypeReader.lean` `emit`s the six per-row
  register interactions (op_a `rd` write, op_b/op_c `rs1`/`rs2` reads; send prior-state / receive
  new-state) **and** the one instruction-fetch send, threading new inputs from the chip's `state` block
  (`clk_high`, `pc`) plus the `is_trusted`/`opcode` selectors.
  **Multiplicity is SP1-faithful and gated** (via `Channel.emit`, not `push`/`pull`): Memory uses
  `±is_real`, Program uses `is_trusted` (= `is_real` on Add) — matching `Extracted/RTypeReader.lean:84,
  92-103` literally and the trace-level `memoryLookups`/`programLookups` exactly, so padding rows emit
  `mult 0` (aligning with the proven `*_padding` lemmas) and the eventual "emitted = projection" theorem
  becomes a near-syntactic match. The `emit`s are `assumeGuarantees = false` ⇒ `memoryChannel`/
  `programChannel` land only in `channelsWithRequirements` (`RTypeReader`, propagated to
  `Chips/AddChip.lean`); with `Guarantees := True` every soundness/`channelsLawful` obligation is
  trivial, axiom-clean, no heartbeat bump.
  **"emitted = projection".** State, Program, and Memory are recovered (axiom-clean) via the
  `Foundations/InteractionRecovery.lean` toolkit; only Byte remains (see §0 for the current state). The
  per-channel recoveries:
  - **State:** `Soundness/StateConsistency.lean`'s `stateLookups_eq_emitted` proves
    `stateLookups r = (interactionsWith stateChannel.toRaw (CPUState's ops)).map (AbstractInteraction.toAccess
    env)` — so `stateLookups` is now a *derived* projection of the actual emission, recovered from
    `CPUState`'s `exposedChannels` via `ElaboratedCircuit.interactionsWith_eq_of_mem_exposedChannels`, not a
    hand-written shadow. The bridge is `Foundations/InteractionProjection.lean` (`AbstractInteraction.toAccess`
    + `signedVal` centered-representative + the `toAccess_emitted_state` kernel). Parameterised by an `env` +
    honest per-column row-realises-circuit hypotheses. Full recipe in `agents/proof-patterns.md`.
  - **Memory/Program (composition):** unlike `CPUState` (no subcircuits),
    `RTypeReader` composes three `RegisterAccessCols` (+ `Gadgets.Equality` `===` gadgets), so the recovery
    must flatten subcircuits. The supporting infrastructure (axiom-clean): `Foundations/Channels.lean`'s `interactionsWith_subcircuit_formal`
    (keeps the `interactionsWith` fold through a `FormalCircuit` subcircuit) + channel-distinctness
    `*_eq_*_false` lemmas + `Register{AccessTimestamp,AccessCols}` `interactionsWith_{memory,program}_eq`
    bottom-up lemmas (in `circuit.main` form). The remaining recovery threads these through the
    `Gadgets.Equality` subcircuits' own bottom-up lemmas, then the 9/16-field `toAccess` kernels +
    `RTypeReader` offset bookkeeping. The Mem/Prog/Byte `*Lookups` stay hand-written shadows for now.
- **Load-bearing per-row channel `Guarantees`.** Per the settled send/receive model (§7), the
  State/Memory/Program `Guarantees` are `True`: the model settled on
  "dynamic buses emit, `Guarantees := True`; only the static byte/range table carries `ByteRowSpec`" (the
  faithful-to-SP1 endpoint). The `<Msg>.Spec` *definitions* are kept in `Channels.lean` as enrichment
  targets. Enriching them re-tunes a
  heartbeat-sensitive soundness proof (`RTypeReader` 1M / `AddChip` 400k / `CPUState`) — the emit-requirement
  tail must discharge the `<Msg>.Spec` of the *evaluated emitted message* via `ProvableStruct` eval, where the
  existing tails are tuned for the trivial `Guarantees = True`. (Enriching `memoryChannel` to the
  literal-`0` register-shape `addr1 = addr2 = 0` breaks `RTypeReader.soundness`'s `and_intros` tail.) The
  enrichment mechanism is as follows.

  The State/Memory/Program channels'
  `Guarantees` carried a named `<Msg>.Spec` predicate (`Foundations/
  Channels.lean`), mirroring `byteChannel`'s `ByteRowSpec`.
  - `MemoryMsg.Spec` = `addr1 = 0 ∧ addr2 = 0 ∧ Word.isU64 value` (register-access shape + valid u64).
  - `ProgramMsg.Spec` = R-type shape (the operand high-limbs + `imm_b`/`imm_c` are `0`) ∧ `op_a < 32` ∧
    `op_b0, op_c0 < 2^16` ∧ `op_a_0 ∈ {0,1}`.
  - `StateMsg.Spec` = `pc0, pc1, pc2 < 2^16`.

  **The discharge mechanism (the load-bearing crux).** The readers *emit* these channels (`emit`, so
  `assumeGuarantees = false`), so **soundness must prove** each emit's `Requirements = (eval mult ≠ -1 →
  Guarantees msg)`. For the gated emits `mult = ±is_real`/`is_trusted` is never provably `-1`, and
  `is_real` is *not* assumable-binary inside a reader — so the obligation fires on **every row, padding
  included**, ⇒ each `<Msg>.Spec` must hold **unconditionally**. We establish it by adding **ungated**
  `byteChannel.pull` Range checks on the witnessed payload columns (prev_value limbs in
  `RegisterAccessCols`; `op_a`/`op_b`/`op_c` + an `op_a_0` binary gate in `RTypeReader`; pc limbs in
  `CPUState`). Ungated, **not** `is_real`-gated, is the right (and faithful) choice: SP1's program lookup
  that proves these is itself unconditional `mult = 1`, and the witnessed-`0` padding satisfies every
  bound. The op_a **write** value's `isU64` can't come from a pull (it's the `wv` *input*), so
  `RTypeReader.Assumptions := isU64 wv`, discharged by `Chips/AddChip.lean` from `AddOperation.Spec.1`
  (its result is already range-checked — no redundant re-check, faithful to SP1's "the ALU op owns its
  write-value range").

  **Why these specs and not more — the channel's semantic ceiling.** A channel `Guarantees msg data`
  sees exactly one `msg` and a **stateless** `data` (`ProverData = String → (n:ℕ) → Array (Vector F n)`,
  no machine state). Two consequences fix the ceiling:
  1. sp1-lean's *state-relative* `toStateProp` (the register/PC/memory cells match the Sail state) is
     **not expressible** as a channel guarantee — it stays trace/bridge-level.
  2. Any *cross-message* fact is out of reach. In particular the RV64 execution relation
     `write_value = RV64.add b_value c_value` is **not** a candidate for `ProgramMsg.Spec`: the program
     message is the *instruction* (pc, opcode, register **indices** `op_a`/`op_b0`/`op_c0`, immediates,
     flags), not the runtime **values** — `write_value` and the register-read `b_value`/`c_value` live on
     the **memory** bus as three *separate* messages, keyed by the program opcode. That relation is
     inherently cross-bus/cross-message; it lives at the **chip Spec** (`AddChip.Spec`'s `toBitVec64
     cols.add_operation.value = toBitVec64 op_b_val + toBitVec64 op_c_val`) + the **bridge to Sail**
     (`Chips/AddBridge.lean`'s `correct_add_native`), and is glued to the buses only at the trace/ensemble
     level (LogUp balance + offline-memory + per-chip arithmetic specs). That is the correct altitude.

  So the program channel's *natural* enrichment ceiling is **static instruction-decode well-formedness**
  (sp1-lean's `Opcode.trusted_instr` + the `op_a_0 = 1 ↔ op_a = 0` decode) — the items deferred below, not
  the dynamic computation.

  **Deferred enrichments:** `ProgramMsg.Spec` — pc-limb bounds (thread `pc` into
  `RTypeReader` as an Assumption discharged in `AddChip` from `CPUState.Spec`; currently proved on the
  *State* channel where `pc` is witnessed), pc0 alignment `% 4 = 0`, the `op_a_0 = 1 ↔ op_a = 0` reverse
  decode (needs real `op_a` + an IsZero gadget — the current `op_a = 0`/`op_a_0 = 0` padding *violates* the
  reverse direction), and the `Opcode.trusted_instr` decode (needs the real `opcode`). `Memory`/`State`
  clk well-formedness (`clk_high` is currently unconstrained — add ungated clk pulls first). All of these
  unblock once the **real-value threading** slice lands (connecting a memory message's `prev_value` to the
  chip's `op_b_val`/`op_c_val` columns, and threading real `pc`/`opcode`/`op_a` instead of padding `0`).

  **Proof gotchas (for the next channel/spec):** (a) the lean-lsp MCP serves **stale** goals
  after a `Channels.lean` edit until a rebuild — it reported the emit requirements as `→ True` (the old
  `Guarantees`); use `lake env lean` + `trace_state` for authoritative goals (same staleness causes false
  `sorryAx`). (b) `circuit_norm` normalizes a Range width column to the numeral `16`, but
  `byteRowSpec_range` is stated with `((16:ℕ):ZMod p)` = `↑16`; bridge with `c16 : ((16:ℕ):ZMod p) =
  (16:ZMod p) := by norm_cast` then `rw [← c16]` (never inside a `simp [circuit_norm, …]` — it fights
  `Nat.cast_ofNat` → max recursion). (c) a sub-circuit's `isU64 (Vector.map eval pv)` vs a message's
  `isU64 #v[eval pv[0..3]]`: bridge per-limb with `Word.lt_cases_of_isU64` + `rw [Vector.getElem_map]` +
  `Word.isU64_of_cases` (prefer the targeted `getElem_map` rewrite over `simpa`, which is whnf-expensive —
  it blew `AddChip` soundness's 200k budget; it now carries `set_option maxHeartbeats 400000`).
- **`MachineAir` record (axiom-clean).** `Foundations/ChipAir.lean`:
  `structure ChipAir {name, perRow : Row → LookupAccessList, included}`, `Machine := List (ChipAir Row)`,
  `Machine.busAggregate` (flatMap included chips' `aggregateChipRows`), `Machine.busBalance` (the aggregate
  `isConsistentBalanced` — SP1's cross-chip Σsends = Σreceives, *expressed* not derived), with
  `busAggregate_cons`/`_nil` + `multiplicitySum_busAggregate_cons` (per-chip key-sum decomposition). Built on
  the computable `InteractionBus` core (`aggregateChipRows`/`multiplicitySum`/`isConsistentBalanced`), never
  the `noncomputable interactionsWith`. (The bespoke `Soundness/MachineConsistency.lean`, which defined the
  four per-bus `ChipAir`s for the Add slice, the `addBuses` `Machine`, `TraceMachineBalanced`, and
  `multiplicitySum_addBuses`, was retired 2026-06-05 with the bespoke `TraceValid` capstone; the `ChipAir`
  foundation in `Foundations/ChipAir.lean` remains.) Receiver chips
  (`ByteChip` provider, ROM, memory argument) append to the `Machine`. `InteractionScope`
  (multi-shard) is deferred. **Gotcha:** `Machine` is an `abbrev` for `List`, so `m.busAggregate` dot-notation
  resolves to `List.busAggregate` (error) — call `Machine.busAggregate m` explicitly.
- **Anchoring the projection to the generated artifact.** Add `Interaction.toAccess : Interaction →
  LookupAccessList` (do **not** mutate `Interaction.toProp`, to protect the existing `Faithful/*`
  anchors) and prove each `*Lookups` equals the generated `interactions` list (the `.send`/`.receive`
  half of `SP1Constraints`) — tying the model to SP1's generated artifact in addition to the circuit.

## 6. Deferred

- Native discharge of `balance ⟹ chain` (`TraceStateLink` etc.) from chip `Spec`s + whole-trace
  clock-injectivity — the genuinely hard math, deferred exactly as `../sp1-lean` defers it.
- Cross-shard `Global` scope and the GKR/LogUp soundness proof itself (Clean does not model the
  permutation argument; it stays a trace-level multiset claim).
- Growing `InteractionKind` toward all 18 upstream variants — add lazily, one per ported chip that
  needs it; adding them all now is dead code.

## 7. The channel-guarantee model — the send/receive duality

`channel.Guarantees` is a **single per-row predicate** that the multiplicity sign turns into a *contract*:

- **receive** (mult evaluates to `-1`, `assumeGuarantees := true`): you *get* `Guarantees msg` as a
  soundness hypothesis;
- **send** (mult `≠ -1`): you must *prove* `Guarantees msg`.

The same predicate sits on both sides, so the consistency the channel needs — "the guarantee a receiver
assumes is exactly what some sender proved for the matched message" — is automatic; the LogUp balance
pairs the messages. `pull`/`push`/`emit` are thin wrappers over `⟨mult, msg, assumeGuarantees⟩`
(`Clean/Circuit/Channel.lean`) — you may build any combination, not just the three.

### Who pulls vs. who pushes is decided by who can *prove* the predicate

A circuit can only **send** (prove) a fact it can establish from its own constraints:

- The party that establishes the fact **pushes** (proves it). For Byte/Range that is the **preprocessed
  `ByteChip`/`RangeChip`** — their fixed rows satisfy `ByteRowSpec` by construction. For a register value
  it is the **writing chip** (it range-checked its output).
- A party that *wants* the fact but cannot prove it locally **pulls** (assumes it). A range check's
  validity is global, so every reader/operation that range-checks **pulls** `ByteRowSpec` — it cannot
  prove "my limb is in range" on its own; that *is* the global argument.

So **byte consumers pull**, even though SP1's chip *sends* the byte event: Clean fires the guarantee at
mult `-1`, so the consumer must sit on the `-1` side and the provider (`ByteChip`) on `+`. The balance
`Σ = 0` is identical to SP1's "consumer sends `+is_real` / table receives" — a global **sign convention**,
documented, not a soundness gap. The one thing that cannot be matched is SP1's *positive* consumer
multiplicity: taking a fact *in* requires the `-1` side.

### Gating: the genuine `is_real`-gated receive (`Channel.gatedReceive`)

A receive *can* be genuinely `is_real`-gated — **`Channel.gatedReceive channel is_real msg`**
(`Foundations/Channels.lean`) has multiplicity `-is_real`: `-1` on real rows (fires the guarantee), `0` on
padding (no bus contribution, exactly matching SP1's `send_byte` multiplicity). The subtlety is that
Clean's `Requirements` clause fires whenever mult `≠ -1`, so on padding's mult `0` you must *prove*
`Guarantees msg` — which SP1's pure balance never asks. Two ingredients discharge it:

1. **fold the value** (`is_real * value`) so the padding message is the always-valid `(op, 0, w, 0)` row;
2. the reader **assumes `is_real ∈ {0,1}`** (`Assumptions := is_real = 0 ∨ is_real = 1`), provided by the
   composing chip's binary gate — so `mult ≠ -1` means exactly `is_real = 0`, and the helper
   `gate_zero_of_ne` turns the padding requirement into `ByteRowSpec (op, 0, w, 0)`.

So `byteChannel` lands in **both** `channelsWithGuarantees` and `channelsWithRequirements`; the chip
discharges each reader's `is_real ∈ {0,1}` from `bool_of_mul_pred h_gate`. (The earlier mult-`-1`
value-fold — a *pure* receive with no padding obligation and so no binary assumption — also works and is
simpler, but its padding rows look up the `0`-row instead of contributing nothing; the gated receive is
the faithful choice and is what's implemented.) A **send** multiplicity-gates directly (`±is_real`): it
always *proves* its guarantee and the sender controls the range-checked value, so the obligation holds on
every row — that's what State/Memory/Program emits do.

### Per-row vs. cross-row, and byte-as-root

`Guarantees : Message F → ProverData F → Prop` sees **one message, no history**:

- **Per-row well-formedness fits**, and is useful: `ByteRowSpec` (byte); `isU64` on a memory value (a
  reader assumes its read value is a valid word *because the writer proved it*); R-type decode; pc bounds.
- **Cross-row / dynamic facts do not fit** — PC chain, offline-memory (read = most-recent write), ROM
  membership — they live in the balance (value-matching, plus sortedness for memory) and stay **threaded**
  (`Trace*Link`).

Every per-row well-formedness fact bottoms out in a byte/range check (the writer proves `isU64`/bounds
*from byte*, then relays it along its bus). So **Byte/Range are the root of well-formedness** — the only
buses whose headline fact is a per-row static-table membership, provable directly by a preprocessed chip;
the others relay byte-derived facts row-to-row and reserve their distinctive (cross-row) meaning for the
threaded balance.

### The rule

| Bus | receiver | in-circuit | `Guarantees` |
|---|---|---|---|
| **Byte / Range** | preprocessed static table | consumers **`gatedReceive`** (mult `-is_real`, value-folded; needs `is_real ∈ {0,1}`), `ByteChip` pushes | **`ByteRowSpec`** (Bitwise/Add consume it) |
| **State / Memory / Program** | dynamic chip / argument | **emit** (multiplicity-gated `±is_real`) | **`True`** now; per-row well-formedness (e.g. memory `isU64`) added when value-threading lands |

Cross-row meaning (`Trace*Link`) is threaded for all four; the lone machine-level assumption is
`isConsistentBalanced` (the LogUp/GKR fact, dischargeable once the receiver chips land). The discharge is
the send/receive duality above. An all-emit model (`Guarantees := True` everywhere) is correct for
State/Memory/Program but wrong for Byte — it cannot express Bitwise's semantics, where the byte lookup
*is* the operation.
