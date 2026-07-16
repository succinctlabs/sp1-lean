# Simplification and remediation plan

This is a design plan, not an instruction to weaken proofs or restate circuits structurally. The project has
already completed a useful proof-golf pass; the largest remaining simplifications come from changing
interfaces and generating repeated evidence, not shaving tactics line by line.

## Priority 0 — Make the current claim honest

These changes should precede new chip work.

1. Rename the current ensemble spec/result to `BalancedStateTrail` / `balanced_state_trail_soundness`, or
   equivalently change its documentation everywhere. Reserve `sp1_machine_soundness` for the theorem that
   concludes a Sail execution.
2. Update `release-audit.md`, the axiom ledger, chip-registry comments, completeness comments, and opcode
   coverage comments from generated data at the current revision.
3. Make the main build warning-free and `lake lint` clean.
4. Close Mul completeness, all DivRem soundness/completeness stops, and `sp1_witness_decode` before merging
   the 4.30 cutover.
5. Freeze clean, immutable dependency revisions.

Acceptance criterion: no project document says "all 25 sound/complete," "one sorry," "exact extraction," or
"machine soundness" unless a command in the same revision mechanically substantiates it.

## Priority 1 — Make generation and audit fail closed

### One source of registry truth

The same 25 chip names are manually repeated across the registry, ensemble table list, coverage code,
advance dispatch, completeness checks, audit probes, and docs. This already produced stale comments and a
probe blind spot.

Define one typed `ChipDescriptor` registry carrying:

```text
name, kind, component, opcode domain, Spec, soundness, completeness,
advance, advance bridge, extracted anchor, optional test battery
```

Generate the derived tables, dispatch cases, coverage propositions, theorem probe list, and documentation
matrix. Lean metaprogramming is optional; a small fail-closed source generator is sufficient if its output is
checked in and compared in CI.

### Extraction manifest

Replace exception-swallowing regeneration with a manifest-driven command that builds into an empty tree and
fails on every mismatch. Add Mul to the circuit registry, restore all witness/trace emitters at the frozen
SP1 pin, and decide the Bitwise selector contract explicitly.

### Axiom audit

Generate probes from environment declarations referenced by the registry, recursively including nested
modules. Require:

- emitted probe count = parsed result count;
- no unapproved `sorryAx`;
- exact allowed axiom sets per theorem class;
- active resolved dependency revisions, including dirty-patch rejection;
- successful build, tests, lint, source guards, and extraction reproduction.

This replaces several pages of manually maintained release state.

## Priority 2 — Generate syntactic faithfulness

The four complete Add/Sub family anchors are hundreds of lines of nearly identical per-channel filtering,
evaluation, sign conversion, and `List.Perm` plumbing. The repetition is both expensive and the reason most
chips have not received equivalent coverage.

Define one projection framework with:

- a canonical `NormalizedAccess` and documented polarity convention;
- compositional lemmas for a Clean `subcircuit`;
- leaf lemmas for `pulledIf`/`pushedIf` on each typed message;
- automatic splitting/filtering by interaction kind;
- a generated theorem over each circuit's exposed interactions and extracted oracle.

Then a chip anchor should consist mainly of field-to-column evaluation equalities and invocations of its
reader/operation subanchors. This should make all 25 chip anchors tractable and eliminate `Interaction.toProp`
from headline claims.

For Mul's 26 byte interactions, avoid asking the kernel to normalize one giant concrete list proof. Prove a
generic map/append theorem over an indexed list of carry/product accesses, and instantiate it. A short
inductive proof produces a smaller proof term than `rfl`/`simp` over a deeply expanded literal.

## Priority 3 — Simplify semantic truth before building the engine

### Use an explicit execution context

Current truth predicates repeatedly quantify over every state satisfying `IsInitialState`, then add
`ZeroRegs`, recover a step number, and compare a fixed-clock trajectory. Define instead:

```lean
structure ExecutionCtx where
  program : GuestProgram
  initial : SailState
  boot : SP1Boot program initial
  publicBinding : StatementFor program publicValues
```

Determinism gives one trajectory from `ExecutionCtx`. `StateAt`, `RegisterAt`, and `MemoryAt` become direct
relations to that trajectory. This simultaneously removes vacuity, repeated loader hypotheses, and much of
the platform-axiom pollution in unrelated circuit types.

### Replace fixed `MicroTime` arithmetic with a schedule

Define a decoded `StepSchedule` containing instruction start, ordered access events, and next clock. Ordinary
instructions instantiate it with eight; syscalls and StateBump use their actual rules. Prove generic
monotonicity and epoch lemmas once. Avoid embedding `/ 8` and `% 8` throughout proofs.

### Make frames first-class and generated

The spike correctly discovered that `advance` alone cannot prove persistence of untouched locations. Derive a
row's write set from its decoded opcode/access descriptors and prove a generic frame theorem. Chips should
provide only their actual writes; they should not each restate universal unchanged-register facts.

## Priority 4 — Production grounding engine

Build the engine in independently reviewable lemmas:

1. field multiplicities plus Clean balance imply an integer/multiset balance for each channel;
2. state timestamps and boundaries induce one exhaustive chronological row ordering;
3. per-location memory accesses form ordered chains, including repeated intra-row touches;
4. decode and the row spec derive `Ready`, `advance`, and `Frame`;
5. induction produces `StateAt`/memory currency at every pull and the final boundary;
6. all real rows are consumed, ruling out disconnected cycles;
7. final decode is the halting instruction and public values agree.

Keep the existing target walk induction as the final consumer. Delete the old balance-only capstone after the
new theorem subsumes its useful structural lemmas.

## High-value proof refactors

### Mul: generic carry-chain theorem

`MulOperation/RawSpec.lean` and its formal proof manually expose a 16-position convolution/carry system.
Package the limbs, partial products, and carries as indexed sequences and prove one generic base-`2^16`
carry-chain theorem. Specialize to 64-bit Mul/Mulh/Mulhu/Mulhsu and 32-bit Mulw. This should reduce both
source size and the kernel term responsible for the deferred syntactic anchor.

### DivRem: one width/signedness semantic core

The 4.30 regression left top-level and eight variant soundness files plus completeness driver holes. The
variants share Euclidean quotient/remainder normalization, absolute-value handling, sign restoration, and
word-width truncation. Define a parameter record for width and signedness, prove the arithmetic theorem once,
and make DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW thin specializations. Keep population lemmas separate from
semantic arithmetic so completeness does not replay soundness normalization.

### Shifts: abstract `BitVec n` lemmas

The shift files remain among the largest in the tree. Continue the successful pattern already documented:
prove kernel-friendly helpers over abstract `BitVec n` variables, then apply them symbolically to limb
reassembly. Parameterize logical/arithmetic and 32/64-bit variants where their only difference is width/sign
extension. Do not unfold `2^64` inside every circuit proof.

### Load/store bridges: width descriptors

Load/store contracts and bridges repeat address calculation, byte assembly, sign/zero extension, access
timing, and Sail update scaffolding. Introduce a `MemOpDesc` carrying width, signedness, load/store direction,
and destination behavior. Prove generic address and byte-lane lemmas, retaining named per-chip corollaries for
auditability.

### Sail advance plumbing

`Proofs/Sail/Advance.lean` is the largest hand-written file at roughly 3,400 lines. Separate stable generic
lemmas about register writes, PC updates, memory accesses, and exception-free platform behavior from
opcode-specific theorems. Generate repetitive opcode decoding cases from the decode table. The semantic
statement for each opcode should remain readable even if its plumbing is generated.

## What not to simplify

- Do not replace semantic specs with restated constraint lists.
- Do not inline subcircuits to make a proof close.
- Do not use `native_decide` or kernel-check bypasses in the main library.
- Do not collapse extracted and native pillars; independent definitions are what make faithfulness meaningful.
- Do not hide global invariants inside `ProverAssumptions` merely to shorten chip theorems.
- Do not force the machine into Clean `VmTables` if that requires erasing time or packing all buses into an
  opaque mega-message.
- Do not golf long arithmetic proofs until their shared semantic lemma is identified; proof-term structure
  matters more than source-line count.

## Suggested implementation sequence

| Stage | Deliverable | Gate |
| --- | --- | --- |
| A | Honest names/docs, clean dependency pins, all current holes closed | Build/test/lint/audit all clean |
| B | Fail-closed extractor + complete manifest | Empty-tree regeneration exact at frozen SP1 pin |
| C | Generated syntactic anchors for readers, then all 25 chips | No headline use of `Interaction.toProp` |
| D | `ProgramWellFormed`, `StatementFor`, canonical `SP1Boot` | Initial-state existence and public binding proved |
| E | Typed `Ready`/`Frame` and schedule-based time | Every chip bridge consumes only derived fields |
| F | Production timed grounding engine | Exhaustive ordered row/memory theorem, no caller obligations |
| G | Direct target capstone | Sail execution + halt/public values from verifier acceptance |
| H | Expand upstream scope | Syscalls, StateBump, fetch/decode/providers, then remaining SP1 AIRs |

This ordering keeps each public claim honest while preserving the useful work already landed on the branch.
