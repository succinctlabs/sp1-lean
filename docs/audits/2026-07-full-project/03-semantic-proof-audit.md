# Semantic proof audit

## The proof chain as implemented

The repository contains two machine-level routes that currently meet only through assumptions:

```text
Clean ensemble constraints + bus balance
                │
                ▼
       balance-derived StateKey trail        per-chip Spec + decode + Ready
                │                                      │
                │                                      ▼
                │                              per-chip advance relation
                │                                      │
                └──────── supplied TargetObligations ──┘
                                                       │
                                                       ▼
                                              SailChain walk induction
```

The lower-right induction is real. The missing theorem is the diagonal connection: deriving exhaustive,
well-timed `TargetObligations` from the actual Clean ensemble and its public-bound program.

## Current capstone theorem strength

### `GatedExecution` is only a graph path

`Soundness/GatedVm/Capstone.lean` defines `GatedExecution` with a trail through state-bus keys. It does not
contain:

- the corresponding `ChipRow` at each edge;
- the chip's semantic `Spec`;
- a decoded instruction;
- an `advance` proof;
- a Sail `try_step` relation;
- an exhaustiveness statement saying every real row appears exactly once.

The constructor `gatedExecution_of_specs_and_balance` receives a hypothesis named `_h_spec` and never uses
it. It derives the trail entirely from interaction balance. This is the single highest-risk modeling blind
spot in the repository: a proof can be perfectly valid while per-row semantics are irrelevant to its
conclusion.

The graph theorem also need not consume disconnected balanced cycles. If initial and final keys coincide,
the data type permits an empty trail. Those are natural properties for an Eulerian-path existence lemma, but
not for an execution theorem unless a timed ordering argument rules them out.

### `SP1Ensemble.Spec` preserves the weakness

The ensemble spec asks only for rows and a `GatedExecution`. Its public I/O has ten initial/final state
fields; it does not include the guest program, verification key, exit code, upstream public-value digests,
range/shard metadata, or a halt-PC commitment. `sp1_witness_decode`, which is supposed to recover rows from
table witnesses, is itself a `sorry`.

Therefore `sp1_machine_soundness` should currently be read as:

> Assuming the sorry-backed witness decoder and Clean ensemble obligations, there exists a balance-derived
> state-key trail between the selected boundary keys.

It should not be read as "the proof represents an SP1 execution" or "the Rust RISC-V implementation is
sound."

## Semantic channels do not yet close the gap

The branch's semantic-channel direction is conceptually promising. The State pull guarantee is now
`StateTruth`, and all 25 chips thread it through their general circuits. This makes chip-local contracts
state what the row is supposed to mean in a deterministic Sail execution.

However, no production theorem grounds those guarantees globally:

- the State channel's push-side obligation is `True`;
- circuit completeness may assume the pull guarantee as honest prover input;
- balance proves equality of access multisets, not truth of a proposition stored in a channel type;
- the capstone's `_h_spec` is ignored;
- the timed grounding machinery exists only as a restricted spike.

This is an ownership problem. A semantic proposition in a channel annotation is not established merely
because interactions carrying the annotation balance. Either a channel engine must prove the guarantee from
the producer and boundary rules, or the guarantee remains an assumption.

The current type-level use also causes a secondary trust-reporting effect: many otherwise ordinary chip
soundness/completeness declarations inherit the Sail platform axioms because `StateTruth` appears in their
types. That makes the axiom surface broader without yet strengthening the final conclusion.

## Program commitment and vacuity

`progOf : ProverData → GuestProgram` is private-prover-derived. The comments refer to a future
`StatementFor`, but no such public-binding definition exists in the tree.

Several details make non-vacuity an explicit proof obligation:

- `sanitizeRom` drops malformed addresses and resolves duplicates rather than rejecting the commitment;
- missing ROM words and clocks default to constants;
- the memory image is not canonicalized with the ROM;
- conflicting duplicate image bytes or ROM/image conflicts can make `IsInitialState` unsatisfiable;
- `IsInitialState` requires initialization, PC, ROM/image loading, and platform configuration, but not
  `ZeroRegs` or an exact default value outside the image;
- `StateTruth` and memory `ValueAt` quantify universally over states satisfying the initial-state predicate.

If there is no such state, the universal semantic facts are true. The repository proves that one empty
program can be loaded; it does not prove existence of an initial state for every `progOf pd` admitted to the
theorem. This is a classic specification-level vacuity hazard.

The clean fix is not an extra nonempty hypothesis at every chip. Define one canonical `SP1Boot program s₀`
predicate, one `ProgramWellFormed` check, and prove existence/uniqueness of the relevant initialized state for
every accepted public commitment. Include zero registers and ROM/image coherence in that boundary.

## Timing faithfulness

`MicroTime` and `StateTruth` assume a fixed eight-clock instruction window and use `init + 8 * n` to locate
the architectural state. This matches the ordinary-instruction `CLK_INC = 8` path in the pinned executor.
It does not match the full SP1 machine:

- syscall rows use an additional syscall clock budget;
- unconstrained-exit handling advances by the larger combined amount;
- StateBump exists to handle the split high/low state clock and rollover;
- one instruction row can touch the same register/memory location multiple times in an ordered sequence.

The current ensemble omits syscall and StateBump tables, so the fixed model is coherent only for its narrow
subset. A production engine should take a decoded per-instruction `clk_inc` (or explicit micro-event list),
model intra-row access order, and prove rollover behavior rather than baking eight into semantic truth.

## The `advance` cutover

The branch has made a strong improvement: every registered chip now owns one native Sail-facing `advance`
relation, and the retired `sailEquiv`/`reaches_sail` route is gone. This removes a major opportunity for two
semantic contracts to drift.

The generic dispatch theorem is still conditional on five hypothesis families:

1. binary/range facts;
2. the chip `Spec`;
3. migration/row-view facts;
4. decode facts;
5. chip-specific `AdvanceReady`.

`targetObligations_via_advance` additionally receives boundary, halt, and non-emptiness assumptions. Some
readiness predicates own facts at the wrong layer: StoreByte asks for ROM disjointness, which is a global
program invariant, and AluX0 encodes a large opcode/immediate disjunction.

This is a good intermediate API, not a finished theorem. The next step is to make `Ready` a small typed
record whose fields are derived once from decode, row spec, and global boot/program invariants, then have the
timed engine produce it.

## Target theorem

`TargetVm.lean` contains a substantive induction showing that a trail plus `TargetObligations` yields a Sail
chain and the desired final state. That proof is one of the strongest machine-level assets in the project.
It is frozen legacy glue, however, and its file comments are stale: they refer to the retired `sailEquiv`
route and describe the platform configuration surface as empty.

The wrapper `sp1_target_soundness` still accepts `∀ rows, TargetObligations ...` and an entry tie from its
caller. The target public-input structure adds an exit value and then `.toLegacy` drops it before invoking
the ensemble. Thus the theorem does not currently derive or publicly bind exit behavior.

Keep the induction, replace its premises with the output of the new grounding engine, and delete the legacy
wrapper once the direct theorem exists.

## Coverage and completeness claims

Two definitions are weaker than their names and comments imply:

- `InstructionTrace.Emits` relates only the selected route, `is_real`, and opcode. It does not bind the PC,
  operands, immediate, result, reader values, witness columns, or bus accesses to the instruction.
- `sp1_partial_completeness` proves that a routed opcode names a registered chip. It neither constructs a row
  nor invokes circuit completeness, so it is registry coverage rather than VM completeness.

These are useful scaffolds. Rename them to `RoutesToRegisteredChip` / `OpcodeTaggedRow`, or strengthen them
before using them as acceptance/completeness evidence.

## Audit of proof integrity and AI-assisted proofs

### What was not found

- No explicit project axiom declarations.
- No use of `debug.skipKernelTC` in the main library.
- No `native_decide` in the main library.
- No evidence of malformed proof terms or an exploit bypassing the Lean kernel.
- Completed chip proofs generally use genuine Clean soundness/completeness goals and compose actual
  subcircuits.

### What was found

- Fourteen direct `sorry`/`stop` deferrals, including headline Mul/DivRem results and witness decode.
- Generated decision-procedure axioms in Mul-related and helper declarations using `bv_decide`.
- A broad Sail platform trust surface inherited after semantic predicates entered circuit types.
- An ignored semantic hypothesis in the trail constructor.
- Vacuous truth for potentially uninhabited initial-state predicates.
- Interaction interpreters that prove only byte semantics while theorem prose says interactions generally.
- One-way reduced specs that discard extracted suboperation constraints.
- Comments and theorem names that routinely exceed the proposition actually checked.

### Verdict on "cheating"

The completed AI-written proofs do not appear to cheat Lean. The more important issue is that some models
make the desired result too easy: they prove a weaker proposition, take the hard property as a premise, or
allow it to hold vacuously. Those are semantic specification defects and should be treated with the same
severity as a proof bug in a verification project.

## Target theorem shape

An honest final theorem should have approximately this dependency structure:

```text
public StatementFor program publicValues
∧ ProgramWellFormed program
∧ verifier acceptance of the extracted-and-faithful SP1 ensemble
    ⇒ ∃ initial final trace,
         SP1Boot program initial
       ∧ ExhaustiveTimedGrounding trace
       ∧ SailChain program initial final trace.length
       ∧ SP1Halted program final publicValues.exitCode
```

The exact statement can be factored, but none of `ProgramWellFormed`, exhaustive timing, or halt/public-value
binding should be hidden in unconstrained prover data or an arbitrary caller-supplied obligation bundle.
