# Risk register

Severity reflects impact on the project's stated verification claim, not difficulty of the fix. "Critical"
means the current public interpretation can be materially wrong even though Lean accepted the theorem.

## Critical

### C-01 — The machine capstone proves a structural trail, not SP1 execution soundness

**Evidence.** `GatedExecution` contains only a `StateKey` trail. The constructor
`gatedExecution_of_specs_and_balance` accepts `_h_spec` but never uses it. `SP1Ensemble.Spec` asks only for
the existence of rows with that `GatedExecution`. No field relates adjacent trail vertices to Sail
`try_step`.

**Impact.** Balanced state-bus traffic can satisfy the public ensemble specification without demonstrating
that any row implements its chip semantics, that the trail contains all rows, or that it is a complete Sail
execution. Disjoint cycles can be omitted by the selected trail. Calling this theorem
`sp1_machine_soundness` overstates its type.

**Remediation.** Rename the current result to a structural balance/trail theorem. Make the public soundness
theorem conclude a grounded, exhaustive timed execution and require the per-row specifications in its proof.
Do not restore the retired dual `sailEquiv` contract; finish the single `advance`-based route.

### C-02 — Semantic truth can be vacuous and the committed program is not public-bound

**Evidence.** `progOf` is derived from private `ProverData`. `sanitizeRom` silently drops malformed and
duplicate entries, memory-image conflicts are not ruled out, and `StateTruth`/`ValueAt` universally quantify
over initial states. If no state satisfies `IsInitialState`, those predicates are true vacuously. The only
non-vacuity example constructs an empty program, not an initial state for every accepted commitment.
`StatementFor` is mentioned but is not defined. `IsInitialState` also omits `ZeroRegs`, while `StateTruth`
requires it.

**Impact.** Even a future grounding engine could "prove" semantic channel facts about malformed prover data
without an execution. The verified program is not yet bound to public input or a verification key.

**Remediation.** Introduce `ProgramWellFormed` and a canonical `SP1Boot` constructor theorem for every accepted
program. Make ROM/image consistency, uniqueness, zero registers, memory defaults, platform configuration,
and public program commitment explicit. Parameterize the final theorem by that public-bound program rather
than recovering it solely from private prover data.

## High

### H-01 — Direct soundness/completeness holes exist on the audited branch

**Evidence.** Fourteen direct deferrals occur in thirteen files: one Mul completeness hole; twelve DivRem
holes (top-level soundness/completeness, a nested completeness driver, and nine soundness/reader results);
plus `sp1_witness_decode` in the ensemble. The main build succeeds with warnings.

**Impact.** Current documentation claiming one remaining `sorry`, all 25 soundness/completeness proofs, or a
clean capstone is false for this revision. The affected declarations and downstream bundles carry
`sorryAx`.

**Remediation.** Close the 4.30 migration regressions before merge, then regenerate all claim inventories.
Treat warning-free build output as a hard gate.

### H-02 — Extraction and conformance generation are fail-open and not reproducible

**Evidence.** `update_extracted.py` catches per-target exceptions and exits zero. At the pinned SP1 revision,
all 49 flat reader/chip forms reproduced exactly, but eight of thirteen registered circuit forms differed;
five registered witness families and all ten trace families were unsupported by the pinned Rust emitter.
The checked-in Mul circuit is not registered. The Bitwise checked-in circuit adds an `is_real` booleanity
assertion absent upstream.

**Impact.** "Extracted from Rust" currently has three meanings: reproducible flat extraction, generated plus
Python normalization, and checked-in data with no working generator at the declared pin. CI can report
success while artifacts are stale or strengthened relative to SP1.

**Remediation.** Make extraction fail closed, generate into an empty tree, use a manifest containing source
and tool hashes, eliminate reads from existing generated output, and byte-compare every declared artifact.
Restore all emitters at the pinned SP1 revision. Either remove the Bitwise strengthening or prove and clearly
label it as an intentional refinement rather than exact extraction.

### H-03 — SP1 interaction faithfulness is complete only for four chips, and even there is normalized

**Evidence.** Only Add, Sub, Addw, and Subw prove a combined syntactic `LookupAccess`-list relation for all
four buses. Most other chip anchors use `Interaction.toProp`; that interpreter maps all receive, state,
memory, and program interactions to `True`, so only selected byte sends have meaning. Bitwise, Branch, Mul,
ShiftLeft, and ShiftRight have one-way reduced anchors. DivRem has no chip faithfulness file. Mul operation's
large syntactic proof is commented out and there is no assertion-to-`RawSpec` anchor.

**Impact.** For most chips, the formal theorem does not establish that the Clean circuit emits SP1's bus
multiset. It may establish arithmetic assertions while saying nothing about non-byte interaction shape.

**Remediation.** Generate uniform syntactic anchors for every operation, reader, and chip. State explicitly
that existing full anchors compare a polarity-normalized multiset: memory/program multiplicities are
negated on selected sides, so this is not literal raw-direction equality.

### H-04 — The target execution theorem remains conditional and public I/O is too weak

**Evidence.** The walk induction in `TargetVm.lean` is real, but the final theorem still receives arbitrary
`TargetObligations`, an entry tie, decode facts, readiness, boundary facts, and halt/non-emptiness. The legacy
ensemble public input has only initial/final state fields. The target wrapper's exit code is discarded by
`.toLegacy`; the program commitment, verification key, SP1 digests, shard/range metadata, and halt PC are
not public-bound.

**Impact.** The theorem is a useful conditional skeleton, not end-to-end SP1 verification. It cannot yet
support the same public statement as upstream SP1.

**Remediation.** Discharge the obligations from a single timed engine and define an honest target public I/O
contract matching the intended upstream verifier boundary.

### H-05 — The semantic time model hardcodes ordinary-instruction timing

**Evidence.** `MicroTime` and `StateTruth` use an eight-clock window per instruction. Upstream ordinary
instructions use `CLK_INC = 8`, but syscalls and unconstrained-exit paths use larger increments, and SP1 has
a `StateBump` mechanism for clock rollover. The current 25-chip ensemble contains neither syscall execution
nor StateBump.

**Impact.** The current truth predicate cannot be extended faithfully to the full upstream machine by simply
adding chips. Clock rollover and variable-cost execution would invalidate the fixed `init + 8*n` model.

**Remediation.** Put `clk_inc` in the decoded transition rule or model micro-events explicitly. Include state
bump/rollover and syscall timing before calling the engine SP1-complete.

### H-06 — The release audit can pass while auditing the wrong dependencies and missing holes

**Evidence.** `run_audit.sh` reports cached package revisions for Clean and Sail even though the active Lake
configuration uses sibling path dependencies. It does not build, test, lint, or reproduce extraction. Its
probe generator scans only `Proofs/Chips/*/Formal.lean`, missing nested DivRem completeness/subproofs. One of
426 emitted probes was not parsed, but the run still passed.

**Impact.** A green audit is not currently evidence for the stated pins, full theorem inventory, or all
release gates.

**Remediation.** Resolve the active Lake dependency graph, reject or fingerprint dirty dependencies, derive
probes from declarations/registry rather than path globs, require emitted and parsed counts to match, and run
all build/lint/test/extraction gates from the audit driver.

### H-07 — `advanceReady` is still a broad assumption surface

**Evidence.** All 25 chips now expose `advance`, but dispatch requires per-row binary, specification,
migration, decode, and readiness hypotheses. `advanceReady` is heterogeneous and can encode facts not owned
by a chip row; StoreByte includes ROM-disjointness, and AluX0 uses a 29-way opcode/immediate disjunction.

**Impact.** A caller can supply much of the difficult machine semantics as assumptions. This is not proof
cheating, but it is an unfinished ownership boundary that makes the end theorem easy to overstate.

**Remediation.** Replace arbitrary readiness propositions with small typed data derived from decode, the
row spec, and global program/memory invariants. Move ROM disjointness into `ProgramWellFormed`.

## Medium

### M-01 — Completeness and trace-emission claims are materially weaker than their prose

`sp1_partial_completeness` proves routing membership, not construction of a valid chip witness or accepted
row. `InstructionTrace.Emits` binds only route, `is_real`, and opcode; it does not relate PC, operands,
immediate, result, or witness columns. Rename these results or strengthen them before using them as coverage
evidence.

### M-02 — Axiom cleanliness is reported too coarsely

After the semantic-channel migration, many ordinary chip declarations structurally inherit the full Sail
platform axiom surface. Mul and some helpers use generated native decision-procedure axioms. This can be an
acceptable disclosed trust base, but it is no longer accurate to describe every headline theorem as using
only the traditional three Lean axioms.

### M-03 — Upstream scope is narrower than "SP1 VM"

The project models 25 supervisor ordinary-instruction chips. The pinned upstream `RiscvAir` enum has 122
variants, including user-mode variants, program/fetch/decode tables, syscalls/traps, range/global-memory/page
infrastructure, StateBump, and precompiles. Opcode coverage is 50 of 53 modeled opcodes; ECALL, EBREAK, and
UNIMP are outside the routing table. State the verified subset precisely.

### M-04 — Documentation and lint state are stale

`docs/release-audit.md`, the axiom ledger, registry comments, completeness comments, and coverage comments
contain claims invalidated by the current branch. `lake lint` reports two declaration-kind issues. Generated
status pages should replace manually repeated counts and name lists.

### M-05 — Conformance testing is useful but sampled and compiler-trusting

The separate `SP1CleanTest` library is the right containment for `native_decide`, but passing finite vectors
does not prove witness/trace-generator equivalence. The current vector provenance failure further limits the
evidence. Keep tests as regression anchors, not proof substitutes.
