# Clean architecture review

## Verdict

The project uses Clean well at the circuit layer and should continue to build on its low-level
`FormalCircuit`, `GeneralFormalCircuit`, `RawChannel`, `Component`, and `Ensemble` abstractions. A direct
rewrite onto Clean's stock `VmTables` would be unnatural for SP1. The main architectural problem is not
failure to use enough Clean; it is assigning global execution truth to a local channel wrapper before an
engine exists to establish that truth.

## What is idiomatic and worth preserving

### Real subcircuit composition

Chip `main` definitions invoke witnessed operation/readers as Clean `subcircuit`s. Soundness and completeness
reuse their semantic specs instead of restating field constraints. This is the right abstraction boundary
for both formal review and possible future execution of the Lean implementation.

The one-main/one-spec organization, field-generic definitions, explicit `ElaboratedCircuit`, and use of
`circuit_norm` lemmas for generated obligations all fit Clean's intended proof workflow. The recent effort to
remove hand-written `localLength_eq`/channel-law proofs in favor of normalizer lemmas is especially good.

### Separation of native, extracted, and formal model layers

The five-pillar layout is an improvement over mirroring source directories alone:

- `Extracted` is the Rust oracle;
- `FormalModel/Contracts` is a readable semantic audit surface;
- `Native` is executable circuit construction;
- `Proofs` establishes native correctness and Sail bridges;
- `Faithful` connects native and extracted artifacts.

Moving execution semantics below channel definitions was necessary once channel types referenced truth.
Keeping namespaces stable across the filesystem refactor avoided gratuitous theorem churn. The separate test
library is also the right way to quarantine `native_decide`.

### One chip registry and one `advance` relation

The registry gives a credible route to generated machine coverage, and the branch's single `advance`
contract is much better than maintaining independent chip semantics and target-step relations. This should
be the spine of the final architecture.

## The `VmChannel` veneer

Clean's typed `Channel` has one message predicate. `Channel.toRaw` derives pull guarantees and push
requirements from that same predicate. The underlying `RawChannel`, however, already exposes separate
`Guarantees` and `Requirements` fields.

`SP1Clean/Model/VmChannel.lean` is a 384-line local typed wrapper around that split, with `Guarantees` for
pulls and `Owed` for pushes. The wrapper solves a real ergonomics problem, and its existence is understandable
during exploration. It has two costs:

1. it forks a substantial portion of Clean's channel interaction API and normalization infrastructure;
2. its stronger type vocabulary suggests that an `Owed` fact will establish the matching guarantee globally,
   but no current engine proves that relation for the semantic State channel.

There are two coherent end states:

- **Preferred for this project:** keep local circuit channels structural, prove semantic truth in the timed
  engine, and delete `VmChannel` plus semantic `ProverAssumptions` once the migration completes.
- **If the typed split remains broadly useful:** upstream a small `BiChannel`/typed-`RawChannel` abstraction
  to Clean, with a generic ensemble theorem that formally transfers requirements to guarantees. Avoid
  maintaining an SP1-specific parallel copy of the channel API.

What should not remain is a proof-only semantic annotation whose global discharge is informal.

## Why stock `VmTables` is not the right engine

Clean's `Air.Flat.VmTables` contains:

- one typed VM message channel;
- one enabled pull and one enabled push for each table;
- a verifier boundary pull and push;
- a timeless multiset balance theorem whose spec is the verifier spec.

SP1 needs multiple dynamic buses, multiple register/memory accesses in one instruction row, ordered
intra-row timestamps, clock rollover, and a proof that a balanced multiset has one exhaustive chronological
walk. Encoding all of that as one giant message or one synthetic access per row would move complexity into
adapters without removing the SP1-specific theorem.

Therefore the existing decision to use a plain Clean `Ensemble` plus an SP1-specific timed theorem is sound.
Reuse Clean's balance and channel primitives; do not force the execution model into `VmTables` merely for
API uniformity.

## Assessment of the spike

`SP1Clean/Spike` is useful design evidence. It proves, for two Add rows, that state and register-memory
balance plus per-row step/frame facts can ground final `StateTruth`. It discovered an important missing
ingredient: a step relation alone does not show that untouched registers persist, so the engine needs frame
facts.

It is not a production engine:

- register locations only;
- straight-line execution;
- fixed eight-clock epochs;
- one row shape;
- pairwise-distinct touched locations;
- balance-to-multiset translation remains a seam;
- decode, row spec, readiness, boundary truths, and several timing facts are assumptions;
- the concrete theorem covers two Add rows.

Promote the ideas, not the spike API. In particular, use a generic ordered event record and derive row frame
facts uniformly from the decoded instruction's write set.

## Recommended architecture

### 1. Explicit statement and boot layer

Define a public `StatementFor program publicValues` and `ProgramWellFormed program`. Build one canonical
`SP1Boot` state and prove its existence. This layer owns ROM/image uniqueness and disjointness, initial PC and
clock, zero registers, platform configuration, and public commitment binding.

### 2. Local chip layer

Keep the current semantic operation specs and true Clean subcircuits. Each chip exports:

```text
Spec row
Ready row decoded globalInvariant
advance decoded pre post
advance_of_spec : Spec row → Ready ... → advance ...
frame_of_spec   : Spec row → Ready ... → Frame ...
```

The `Ready` structure should be small and typed. Facts like ROM disjointness belong to the global invariant,
not an individual StoreByte row.

### 3. Syntactic extraction layer

For every operation/reader/chip, generate a theorem connecting extracted assertions and polarity-normalized
access lists to the native circuit. This is the only layer allowed to say "faithful to SP1 constraints."

### 4. Timed ensemble grounding

From the actual Clean channel balance and decoded rows, derive an ordered, exhaustive event sequence. The
engine should support:

- variable instruction clock increments;
- register and ordinary memory keys;
- repeated same-location accesses within a row;
- branch/jump control flow;
- state-clock high/low rollover and StateBump;
- exact row consumption, ruling out disconnected cycles;
- frame/persistence properties;
- boundary program and final halt/public-value facts.

This engine, rather than a channel type, establishes `StateTruth`, fetch truth, and memory currency.

### 5. Target Sail theorem

Feed the engine's ordered result into the existing `sp1_target_execution` walk induction. The final theorem
then has no arbitrary `TargetObligations` argument.

## Preparing for direct zkVM adoption

The native Lean circuits are already closer to adoptable implementation code than proof-only translations.
To keep that path viable:

- keep circuit construction independent of Sail imports; Sail belongs in specs/bridges;
- make witness population executable and total on a typed decoded instruction;
- avoid semantic behavior hidden in `ProverData` or proof-only channel predicates;
- keep column layouts and access-list generation derived from one typed source;
- make refinements relative to upstream SP1 explicit rather than silently strengthening extracted circuits;
- benchmark elaboration and witness execution separately—proof convenience should not dictate runtime data
  structures.

The likely reusable core is `Math` + native operations/readers/chips + structural channels. The timed
grounding theorem and Sail bridge remain verifier-side proof infrastructure.

## Dependency hygiene

Local path dependencies were appropriate for the Lean 4.30 migration, but dirty sibling trees make the
meaning of an axiom census and reproducible build ambiguous. Before merge:

1. land or vendor the Sail/RISC-V/toolchain patches at immutable commits;
2. restore declarative git dependencies;
3. make the audit report the resolved active graph, not stale `.lake/packages` clones;
4. record the exact generated Sail model revision and platform-assumption delta.
