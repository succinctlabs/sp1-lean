# ByteChip provider — design notes & scope (W11 prerequisite)

> **Balance-reuse note (2026-07-21).** This is our closest read of Clean's `Air/Balance.lean` /
> `Air/OrderedChannel.lean` / `Air/Vm.lean`, and the natural home for the "reuse Clean's reversal, don't
> re-derive it" action from `docs/architecture.md` §"Relationship to Clean's `Air` layer". For *finished*
> channels (byte/program), prefer invoking Clean's `Balance.lean` "guarantees-to-requirements-reversal" /
> `PartialBalancedChannels` (per Clean's `Clean/Air/README.md`) directly; only the *timed* memory/state
> axes keep our bespoke walk. Verify against current Clean source before relying on the pin-`2c20f7f0` line
> numbers below.

**Goal (user-chosen 2026-06-26):** make `byteChannel` a *finished* channel in Clean's `SoundEnsemble`,
so the byte-bus soundness moves to upstream Clean (`addVm_soundVmChannel_of_soundChannels`) instead of
our `Soundness/ByteConsistency.lean` `TraceByteLink` assumption. This is the first concrete unblock for
re-basing `Soundness/GatedVm/` onto upstream `VmTables` (roadmap W11).

## What Clean requires of a "finished" channel (verified against the pin `2c20f7f0`)

`SoundEnsemble.addFinishedChannel channel [channel.Consistent]` (`Air/OrderedChannel.lean:755`) marks a
channel finished. To then use `addVm_soundVmChannel_of_soundChannels` (`Air/Vm.lean:703`), the base
ensemble must satisfy `Ensemble.SoundChannels finished` (`Air/OrderedChannel.lean:460`):

```
SoundChannels tables finished :=
  (∀ table ∈ tables, table.circuit.channelsWithGuarantees ⊆ finished) ∧   -- (1)
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧                  -- (2)
  (∀ channel ∈ finished, channel.Consistent)                              -- (3)
```

- **(3) is free.** Typed `Channel`s are `Normal` by definition (`Air/Balance.lean:211`), and
  `Normal → Consistent` (`:244`). So `byteChannel.toRaw.Consistent` is an instance — no work.
- **(1)** holds for the chips: their `channelsWithGuarantees = [byteChannel.toRaw]`, so listing
  `byteChannel` in `finished` discharges it.
- **(2) `OrderedChannel byteChannel tables`** is the real structural obligation, and it forces a
  **provider Component**: per the `Normal` instance (`:204-218`), a typed channel's *push* owes
  `Requirements = Guarantees`, i.e. **every byte row pushed onto the bus must prove `ByteRowSpec`**, and
  the pushes must *balance* the chips' pulls (`PartialBalancedChannel`, a hypothesis threaded by the
  witness). A channel with pulls but no pushes is never balanced, so the chips never get their
  `ByteRowSpec` — the provider is what supplies the pushes.

## The provider Component

A `ByteChip` provider is a Clean `Component` whose `main` **pushes every valid byte-table row** onto
`byteChannel` (with a witnessed multiplicity = the lookup count) and whose soundness proves
`ByteRowSpec` for each pushed row. `ByteRowSpec` = the table-membership predicate (`Model/ByteTable.lean`:
`ByteTable.Contains _ row := ByteRowSpec row`), so "every pushed row is valid" is true by construction —
but it must be *materialized as a circuit*. SP1's byte table spans:
- opcode 3 (U8Range, `a < 2^8`), opcode 6 (Range, `a < 2^n`, n=0..16), opcode 5 (MSB),
- AND/OR/XOR byte-ops (`256×256` each).

i.e. a preprocessed table over ~200k+ rows. Clean models preprocessed byte tables (e.g.
`Gadgets/Xor/ByteXorTable.lean`) as **`Table` lookups** (`Circuit.lookup`), NOT as channel providers —
there is no generic `Table → provider Component` helper. So the provider is a bespoke fixed-domain
"push every row" circuit + its per-row `ByteRowSpec` soundness + the `OrderedChannel` discharge.

## The design fork (must be resolved before building)

**(A) Channel-provider Component** — faithful to SP1's interaction bus (`send_byte`): build the
row-materializing provider above. Largest single roadmap item; LogUp multiplicity/balance accounting.

**(B) Switch chips to Clean `Table` lookups** — replace each `byteChannel.pullIf` with
`Circuit.lookup ByteTable …`, which is sound *by construction* upstream (no provider needed) — the
idiomatic Clean approach and a genuine trust-move. BUT: it changes the bus model away from SP1's
interaction `send_byte` (faithfulness anchors compare against the *interaction* list), and re-works the
byte half of the just-completed channel migration + every byte faithfulness anchor + `ByteConsistency`.

Both are large. (A) preserves the current faithful interaction model; (B) is more idiomatic/upstreamable
but rewrites the byte bus.

## Decision (2026-06-26): path (A), range opcodes first.

## Faithfulness check against SP1 (`../sp1`, read 2026-06-26) — and a corrected bug

Grounding the provider against SP1's real source (`crates/core/machine/src/bytes/`, `…/range/`,
`crates/core/executor/src/{opcode.rs,events/byte.rs}`):

**SP1 splits the byte bus across TWO preprocessed provider chips, both on the same `byteChannel`:**
- **`ByteChip`** (`bytes/`) — a preprocessed table over **all `(b,c) ∈ [0,256)²`** (65536 rows;
  `BytePreprocessedCols { b, c, and, or, xor, ltu, msb }`). Its AIR (`bytes/air.rs`) `receive_byte`s six
  lookups per row, one per `ByteOpcode` in `byte_table() = [AND,OR,XOR,U8Range,LTU,MSB]` (= 0..5):
  - `AND(0)`→`(0, and, b, c)`, `OR(1)`→`(1, or, b, c)`, `XOR(2)`→`(2, xor, b, c)`,
  - **`U8Range(3)`→`(3, 0, b, c)`** ← note `a = 0`, the two checked bytes in `b,c`,
  - `LTU(4)`→`(4, ltu, b, c)`, `MSB(5)`→`(5, msb, b, 0)`.
- **`RangeChip`** (`range/`) — a preprocessed table over all `(a, bits)` with `a < 2^bits`, `bits ≤ 16`
  (`RangePreprocessedCols { a, bits }`). Its AIR (`range/air.rs`) is a single
  `receive_byte(Range(6), a, bits, 0, mult)` — opcode **6**, form `(6, a, bits, 0)`.

**Bug found & fixed:** the first worker's `U8RangeProvider` pushed `⟨3, a, 0, 0⟩` — a row SP1 never
emits (and that no consumer pulls; CPUState/RegisterAccessTimestamp/Add all pull `(6, x, n, 0)` Range
and `(3, 0, b, c)` U8Range). It was **deleted**. Our `Model/ByteTable.lean` lemmas are already faithful:
`byteRowSpec_u8range_pair ⟨3, 0, b, c⟩` (the real U8Range form), `byteRowSpec_range ⟨6, x, n, 0⟩`,
`byteRowSpec_byteOp`, `byteRowSpec_msb`.

**Key modeling tension (important for the trust story):** SP1's `ByteChip`/`RangeChip` AIRs are
**trivial** — they just `receive_byte` *preprocessed* columns; validity (`a<2^bits`, `and = b&c`, …) is
**definitional** (the table generator only emits valid rows), not an in-circuit constraint. Clean has no
"trusted preprocessed table" primitive *for channels*, so a finished-channel **provider must re-prove
each pushed row valid in-circuit**. That is strictly MORE work than SP1's preprocessing, but it
**removes** our current `TraceByteLink` *assumption* (`Soundness/ByteConsistency.lean`) — replacing a
trusted balance/validity axiom with a Lean proof. Semantically faithful (same valid rows on the bus),
mechanically heavier. (The preprocessed model maps cleanly only to Clean's `Table`/`Circuit.lookup`,
which is the *lookup* form, not a channel provider — that was fork (B).)

## Directory (reorganized 2026-06-26, per request — no top-level `ByteChip.lean`)
`SP1Clean/Proofs/Chips/ByteChip/`:
- `Provider.lean` — the abstract trace-level `ByteProvider`/`RangeProvider`/`ByteOpProvider` predicates
  (moved from the old top-level `ByteChip.lean`; consumed by `Soundness/ByteConsistency.lean`).
- *(to build)* `ByteChip.lean` — the in-circuit `ByteChip` provider Component (ops 0..5 over `(b,c)`).
- *(to build)* `RangeChip.lean` — the in-circuit `RangeChip` provider Component (op 6, `a < 2^bits`).
  Use Rust-faithful names (`ByteChip`, `RangeChip`, `BytePreprocessedCols`-style fields, `multiplicity`).

## Build status (2026-06-26)

**Built, green + axiom-clean, wired into `SP1Clean.lean`:**
- `ByteChip/ByteChip.lean` — `ByteChip` provider, **5 of 6 byte-ops** as independent
  `GeneralFormalCircuit`s (sub-namespaces `U8Range`/`MSB`/`AndByte`/`OrByte`/`XorByte`). Each
  `rangeCheck 8`s its operands in-circuit, pushes the faithful row, discharges `ByteRowSpec` via the
  `Model/ByteTable.lean` lemma. Reuses Clean's upstream `And8`/`Or8`/`ByteXorTable`. Axioms:
  U8Range/MSB/XorByte are `[propext, Classical.choice, Quot.sound]`; AndByte/OrByte additionally carry
  `ofReduceBool`/`trustCompiler` from `And8`/`Or8`'s `bv_decide` (same accepted set as Mul/Bitwise).
- `ByteChip/RangeChip.lean` — `RangeChip` provider, **fixed-width family** `circuit n hn` instantiated at
  `circuit8`/`circuit13`/`circuit16` (every width SP1 consumers pull). Faithful row `⟨6, a, n, 0⟩`,
  fully `[propext, Classical.choice, Quot.sound]`.

**Remaining (the hard tails):**
- **LTU (op 4)** byte-op (`⟨4, ltu, b, c⟩`) — a comparison gadget; not yet built.
- **Variable-`bits` `RangeChip`** (`bits` a runtime column) — the genuine difficulty SP1 sidesteps by
  preprocessing; needs a one-hot `bits`-selector over a 16-bit decomposition with per-position masking
  (~200 lines, field-to-Nat algebra). The fixed-width family already covers every width the machine pulls.
- **Ensemble wiring** — `addTable` the providers + `addFinishedChannel byteChannel.toRaw` into a
  `SoundEnsemble`, discharge `OrderedChannel`/`SoundChannels`, then `addVm_soundVmChannel_of_soundChannels`
  to re-base `Soundness/GatedVm/`. This is where the `TraceByteLink` assumption finally retires.

## Construction — corrected (the provider is a per-row gadget, NOT an enumeration)

Clean's `StaticLookupChannel` + `Channel.fromStatic` (`Circuit/Channel.lean:75-86`) only fit *tiny*
enumerable tables — the Fibonacci `pushBytes` literally `mapFinRange 256` pushes (and is self-described
as "probably shouldn't be a circuit at all"). SP1's range table (op 6 `a < 2^n`, n≤16 → ~2^17 rows)
cannot be enumerated. The right shape is the one SP1's real RangeChip uses: a **per-row range-check
provider Component** whose `main`, for one row, witnesses `(a, n)` (or `a` for op 3), proves the range
bound by bit-decomposition, and `byteChannel.pushIf`-pushes the row with a witnessed multiplicity. The
`Component`/table machinery replicates the row over the table height (= the number of distinct pulls);
nothing enumerates `2^n`. Soundness proves `ByteRowSpec` for the one pushed row (its push-`Requirements`,
since `byteChannel` is a typed/`Normal` channel). Balance (pushes ↔ pulls) is the `PartialBalancedChannel`
hypothesis threaded by the witness, not an in-circuit obligation.

## W11 ensemble re-base — feasibility gates VALIDATED (2026-06-26)

The plan (`~/.claude/plans/…`) re-bases onto canonical Clean `SoundEnsemble`/`VmTables` with
`StaticLookupChannel` providers + full `GatedVm` replacement. Its two load-bearing risks both resolve
favorably:
- **Faithfulness of the `channelsWithRequirements` reconciliation (Phase 0a):** SP1's CPU adapter
  (`../sp1/crates/core/machine/src/adapter/state.rs:81`) does `builder.assert_bool(is_real)` immediately
  before its `receive_state` + `send_byte(Range,…)` + `slice_range_check_u8`; `air/memory.rs:32/83/134/184`
  does `assert_bool(do_check)` before every memory/timestamp interaction. So SP1 constrains the
  byte-send gate boolean **locally**, at the send site — adding a local binary gate to our gated-pull
  readers (CPUState/RegisterAccessTimestamp) is *more* faithful (they currently lack it) and unblocks
  dropping `byteChannel` from `channelsWithRequirements` so the channel can be finished.
- **Provider scale (Phase 0b):** a `pushBytes`-style `mapFinRange N` provider elaborates in constant
  ~1.8s for N ∈ {4096, 16384, 65536} (imports-only baseline 1.55s → +0.26s, independent of N). Clean
  reasons about `mapFinRange` symbolically (one `forAllNoOffset`/`∀ i` argument, not an N-fold unroll),
  so the provider soundness is generic over the domain — SP1's 65536-row byte table does **not** blow up.

## Phase 0c — the `channelsWithRequirements` reconciliation: VALIDATED + faithful (2026-06-26)

To finish `byteChannel`, every reader/chip/op must drop it from `channelsWithRequirements` (Clean's
`addVm`/`addTable` need `byteChannel ∉ table.channelsWithRequirements`). The `cedc171b` off-gate
pull-`Requirements` is instead discharged by a **local binary gate**, faithful to SP1:
- **Faithfulness (definitive):** SP1 constrains the byte-send selector boolean *locally, at the send
  site*, EVERYWHERE — adapter (`adapter/state.rs:81` `assert_bool(is_real)`), operations
  (`operations/add.rs:52` `assert_bool(is_real)`, doc "Constrains that is_real is boolean";
  `operations/field/range.rs:92`), memory (`air/memory.rs:32/83/134/184`). Adding the gate is more
  faithful, not an invention.
- **Validated template (CPUState, builds standalone green + axiom-clean):**
  1. `main`: add the gate as the **inline** `assertZero (input.is_real * (input.is_real - 1))` — NOT
     `… === 0`, which composes the Equality *subcircuit* that `ConstraintsHold.Shallow` cannot see
     (Clean's fib8 has the same caveat in-source). For CPUState this gate is exactly `Extracted.CPUState`
     assert `E3`, so the reader gains a constraint it was previously (unfaithfully) missing.
  2. `circuit`: drop `byteChannel` from `channelsWithRequirements`; update the `…_eq` rfl-lemma RHS.
  3. supply `requirementsChannelsLawful input_var i₀ := by simp only [circuit_norm, main, byteChannel,
     stateChannel]; grind` (the gate, now shallow, gives `is_real ∈ {0,1}`; `grind` kills the off-gate
     byte `Requirements`). `main` must be in the simp set (it's a named `def`, unlike fib8's inline one).
  4. soundness: the gate becomes `h_holds.1`, shift byte indices (`h_holds.1→.2.1`, `.2→.2.2`); the
     `off_gate_vacuous h_assumptions` tail is unchanged. completeness: add a leading gate bullet
     `rcases h_assumptions with h | h <;> simp [h]`.
- **Sweep classification:** leaf readers (CPUState/RegisterAccessTimestamp/MemoryAccess) need the gate
  ADDED; operations (Add/Sub/…/U16…) ALREADY have it (just drop the channel + supply
  `requirementsChannelsLawful`); composed circuits (RegisterAccessCols/RTypeReader/type-readers/chips/
  whole chips) just drop `byteChannel` (their subs handle the byte `Requirements`). ~50 files, one
  coordinated red-period sweep (mirror the migration sweep). Faithfulness anchors (`Faithful/*`) may need
  the new `E3`-style gate reflected.

### Build units (each lands green + axiom-clean independently)
1. **op 3 (U8Range) provider** — `main` witnesses `a`, proves `a.val < 2^8`, pushes `(3, a, 0, 0)`;
   soundness = `byteRowSpec_u8range`. Simplest; mirror an existing range gadget (`U16toU8`/`ShiftBounds`).
2. **op 6 (Range) provider** — witness `(a, n)`, prove `a.val < 2^n`, push `(6, a, n, 0)`; soundness =
   `byteRowSpec_range`. (n is itself a small Range column.)
3. **Wire into the ensemble** — `addTable ⟨rangeProvider⟩` + `addFinishedChannel byteChannel.toRaw`
   (`Consistent` is free); discharge `OrderedChannel` / `channelsWithGuarantees ⊆ finished`.
4. **Later:** MSB (op 5) + AND/OR/XOR byte-ops (the `256×256` product — the hard remainder), then the
   `addVm_soundVmChannel_of_soundChannels` re-base of `Soundness/GatedVm/`.

Existing infra to build on: `Model/ByteTable.lean` (`ByteRowSpec`, `byteRowSpec_range`,
`byteRowSpec_u8range_*`), `Proofs/Chips/ByteChip.lean` (`ByteProvider`/`RangeProvider` trace-level
predicates + `byteRowSpec_of_provider`), and the range gadgets in `Native/Operations/`.
