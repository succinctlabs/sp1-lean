# Architecture

## Design rule

The stable verification boundary is a complete SP1 chip.

Rust operations and Lean gadgets may use different intermediate structures. A native Lean chip is
proved against a semantic contract, connected to Sail, and then compared with the complete upstream
chip assertion and interaction systems. Operation-level extraction remains an implementation aid while
the migration is completed; it is not part of the public correctness claim.

This produces four distinct objects:

1. a proof-oriented native Clean circuit;
2. a semantic chip contract;
3. a complete extracted Rust AIR oracle; and
4. a Sail instruction-step theorem.

No one of these objects is silently treated as another.

## Repository layers

| Layer | Responsibility |
|---|---|
| `Math/` | field-generic words, carries, bit operations, and arithmetic lemmas |
| `Model/` | SP1 messages, channels, Sail state/execution, schedules, and syscall interfaces |
| `Extracted/` | generated Rust rows, assertion lists, interaction lists, manifest, and provenance |
| `FormalModel/` | semantic contracts and public witness relations |
| `Native/` | independent Clean circuits and witness-producing gadgets |
| `Proofs/` | circuit soundness/completeness and Sail bridges |
| `Faithful/` | native-row ↔ Rust-row whole-chip comparisons |
| `Soundness/` | machine registry, typed decoding, grounding, and capstones |
| `SP1CleanTest/` | compiler-trusted executable conformance tests, isolated from the main library |

`SP1Clean.lean` imports the complete main proof library. The test library imports it in the opposite
direction and is never part of the main theorem graph.

## One instruction chip

For each supported chip, the verification chain is:

```text
native Clean main
  ├─ circuit soundness ──→ semantic chip Spec
  ├─ circuit completeness
  ├─ Sail bridge ────────→ one official try_step transition
  └─ row codec
       └─ ChipFaithful ──→ complete Rust assertions + active interactions
```

### Native circuit and contract

`Native/Chips/<Chip>/Defs.lean` owns one native row type and one `main`. It composes readers and
arithmetic gadgets as true Clean subcircuits. Public semantic meaning lives under
`FormalModel/Contracts/`; it is not a restatement of the generated constraint list.

`Proofs/Chips/<Chip>/Formal.lean`, or a focused submodule for a large chip, proves:

- soundness: satisfying the circuit entails the semantic contract; and
- completeness: the honest witness closures satisfy the circuit under the stated prover inputs.

All 25 registered instruction circuits now have closed soundness and completeness proofs.

### Sail bridge

`Proofs/Chips/<Chip>/Bridge.lean` turns the semantic contract into the corresponding behavior of the
generated LeanRV64D Sail model. `ChipKind.advance` packages the result in the uniform interface used by
the machine proof.

The bridge is conditional on concrete decoded operands and the live machine state. Those facts are
derived by the grounding engine, not assumed by the chip's row-local channel predicates.

### Whole-chip Rust faithfulness

The extractor emits:

- the exact upstream Rust row type;
- every `assertZero` expression in order; and
- every interaction expression in order.

`Faithful/ChipOracle.lean` defines an explicit bijective row-layout codec. `ChipFaithful` proves:

```text
upstream assertions hold
  ↔ native Clean component constraints hold
```

and, on accepted rows:

```text
active upstream interactions
  = active native interactions, as a multiset
```

Zero-multiplicity entries are observationally absent from both LogUp and Clean balance. Native
interactions on an unexpected fifth channel are retained in the comparison, so a proof cannot make one
disappear by checking only the four expected buses.

`Faithful/SupportedMachine.lean` contains one proof-bearing entry for every descriptor and proves that
its table tags are exactly the 25 upstream instruction tables. This is the coverage tripwire for future
pin or registry changes.

## The native supported machine

`Soundness/SupportedMachine.lean` is the single instruction registry. Each of its 25 entries carries:

- the verified Clean circuit;
- its semantic `ChipKind`;
- the routed SP1 opcodes; and
- the `rd = x0` routing guard.

The registry drives the Clean table list, typed row decoder, opcode coverage, Sail dispatch, and
faithfulness coverage. Its order is a witness-format decision.

`SP1Ensemble.lean` adds 11 proof-oriented provider/boundary tables to form a 36-table Clean ensemble.
These provider circuits are not asserted to be the exact upstream Core system tables. They are the
small native interface used to prove the instruction execution theorem.

## Structural buses and semantic grounding

The four Clean channels communicate only the algebra SP1 actually constrains:

- State: timestamp and PC edges;
- Program: decoded instruction rows;
- Memory: location, timestamp, and word limbs;
- Byte: byte/range lookup messages.

Local guarantees are structural. In particular, State does not claim reachability and Program does not
claim commitment merely because a message appears.

The whole-machine proof derives meaning in this order:

1. `WitnessDecode.lean` deterministically recovers typed rows from all 25 physical circuit tables.
2. State balance and strict timestamp rank produce an exhaustive order of exactly the active rows.
3. Program balance and the bound provider prove that each ordered row decodes the committed program.
4. Per-location Memory balance, provider uniqueness, and timestamp ordering recover the live value for
   each register or RAM access.
5. `ChipGroundingContracts` derive each exact row's assumptions, semantic `Spec`, routing, and readiness.
6. `LocalExecution.lean` applies `ChipKind.advance` in order to construct an actual Sail chain.

The generic timed engine and every one of the 25 registry contracts are proved. The result is packaged
by `supported_core_witness_grounding` and consumed by `supported_core_native_sound`.

The source relation keeps non-algebraic facts visible:

- the program and initial state are bound to provider rows;
- memory-provider rows are unique per location;
- code memory is compatible with the Sail execution model; and
- pulled high timestamps satisfy the physical range bound.

These are not Lean axioms. They are explicit relation conjuncts that the exact upstream system-table
proof must eventually derive.

## Exact upstream Core AIR

The native ensemble is a proof architecture; it is not the upstream verifier relation.

`FormalModel/CoreProfile.lean` defines the audited table enum and exact clusters. Generated
`CoreAIRManifest.lean` independently records the runtime Rust names and widths. Kernel-checked
permutation theorems connect the readable profile to that manifest.

The baseline clusters are:

- execution: 3 preprocessed tables + 25 instruction tables + 6 system tables = 34;
- memory boundary: 3 preprocessed tables + 2 memory-global tables + Global = 6.

`Faithful/CoreAIR.lean` assigns every table its exact row type and generated lists. Its relation checks:

- exact active-cluster shape;
- all row assertions;
- public-value assertions;
- exact natural interaction balance; and
- the verifying key's preprocessed commitment.

This relation is suitable as the deterministic target of a knowledge extractor. It is stronger than
the verifier's raw field equations where necessary to express an execution multiset without modular
wraparound.

## Exact AIR refinement boundary

`Soundness/CoreAIR.lean` does not pretend that listing the upstream equations proves their execution
meaning. `CoreAIRRefinementObligations` names the missing proofs, including the system-table grounding
and syscall-event cases.

Today the file exports only:

- `sp1_air_refinement_of_obligations`; and
- `sp1_air_sound_of_obligations`.

They assemble a supplied bundle into the public relation, and they are useful for fixing the intended
API. They are not the final capstone. The unqualified names remain unavailable until the bundle is
constructed from the exact relation.

The intended implementation route is:

```text
exact instruction rows
  ── 25 ChipFaithful proofs ──→ native instruction constraints/interactions

exact system rows
  ── system grounding ────────→ native provider, boundary, timestamp, and syscall facts

both
  ── supported_core_native_sound + event assembly
  ──→ SP1CoreShardExecutionRelation
```

This structure reuses the closed native proof and avoids a second whole-machine execution engine.

## Syscalls and schedules

Ordinary supported instructions occupy 8 SP1 ticks. A raw Core ECALL event occupies 264 ticks.
Sail specifies the instruction but not SP1's host handler, so the eventful target is parameterized by
an explicit `SyscallHandler`.

A concrete theorem must prove the claimed handler behavior. Precompile clusters are separate verifier
targets and should be added only with their full table and handler refinements.

COMMIT-row correctness and row existence are separate:

- AIR proves the digest operand of every canonical row that occurs;
- the standard halt wrapper is a property of the verification-key-bound program and supplies
  all-eight-row coverage across the full execution.

This wrapper property is absent from the base shard and execution relations.

## Shard execution and verifier layers

`FormalModel/Execution.lean` defines an authenticated full-execution target. It includes the
public-values ledger, full-state shard stitching, global balance, deferred-proof authentication, boot,
and final HALT conditions. It is deliberately downstream of shard AIR soundness.

`FormalModel/Verifier.lean` provides relation-level composition machinery for the later ArkLib layer.
ArkLib must supply probabilistic knowledge soundness for transcript processing, LogUp/GKR, zero-check,
PCS openings, commitments, and Fiat--Shamir. The error term must survive post-composition with the
deterministic AIR refinement.

## Completeness

Clean circuit completeness is local: honest witness closures satisfy one circuit. Whole-machine
completeness is a different theorem:

```text
supported semantic execution
  → generated native and upstream traces
  → balanced AIR witness
  → accepting cryptographic proof
```

The source must be restricted to supported, trace-generatable executions. Clean's exportable witness
generation is the intended implementation vehicle. No placeholder whole-machine completeness theorem
is declared today.

## Performance discipline

Large extracted lists and circuit specifications must remain folded. Whole-chip proofs cross different
spellings through explicit rewrite lemmas rather than asking unification to unfold both sides.
`circuit_proof_start_core` is used for completeness proofs near the kernel-size cliff. The main library
forbids `skipKernelTC` and `native_decide`.

Per-declaration elaboration-budget overrides are ratcheted, not managed: `scripts/check_heartbeats.sh`
fails the audit on any increase over `scripts/heartbeats_baseline.txt`. The current baseline is 215 sites
in `SP1Clean/` and 16 in `SP1CleanTest/` — and **all 231 are in auto-generated files**. The hand-written
surface carries **zero** elaboration-budget overrides, matching upstream Clean, which has none in 44,603
lines. Every remaining site is emitted by `update_extracted.py`, three lines of which apply a blanket
unmeasured bump to each generated definition; that is the next target, not a proof-engineering problem.
A raised ceiling is normally a masked `whnf` blowup, so the required fix is to fold the blowup. The measured record — which surviving overrides are term-intrinsic and what their
measured floors are — is [`agents/perf-findings.md`](agents/perf-findings.md).

The project-specific patterns are in [`agents/proof-patterns.md`](agents/proof-patterns.md); Clean's own
`doc/performance-problems.md`, `doc/proving-guide.md`, `AGENTS.md`, and `Clean/Air/README.md` remain the
upstream authority.
