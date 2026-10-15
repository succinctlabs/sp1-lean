# Capstone branch review

Review date: 2026-09-19. Branch `dtumad/core-verification-capstone` at `fdb3383f` (the last commit
before this review's own commits), compared against `main` at `512e944a`. This records an
independent review of the semantic execution model, the capstone statement, the installed proof
stack, documentation consistency, and repository readiness, made before development moved to the
`dtumad/sp1-lean` fork. It is a review record and a finding list for the next campaign phase, not a
certification of the development.

The [consolidation assessment](2026-09-capstone-assessment.md) covers the eight-PR baseline at
`a1efce55`. This review covers the 189 commits after it (471 files, 138,959 additions, 5,056
deletions; 163 of the files are under `SP1Clean/Soundness/`), which refocus the capstone from the
55-table `supported_core_native_sound` to the full-state local shard statement.

## Scope and method

The Lean was read directly for `SP1Clean/FormalModel/Shard.lean`,
`SP1Clean/Soundness/Shard/Contract.lean`, all of `SP1Clean/Model/Core/`, `SP1Clean/Model/Machine/`,
`SP1Clean/Model/Semantics/`, the `SP1Clean/Soundness/HostHintRead*.lean` family,
`SP1Clean/Soundness/AIR.lean`, `SP1Clean/Soundness/GroundingInternal.lean`,
`SP1Clean/Proofs/Completeness/`, and `SP1Clean/Soundness/CoreAIR.lean`. The maintained documents,
the CI workflows, the audit scripts, and the git history were read for consistency with the Lean.

Not done: a line-by-line proof review of the 195 `Soundness/` modules, construction of adversarial
whole-AIR witnesses, a rerun of the Rust extraction or dump regeneration, or a review of the Clean
fork delta. Kernel acceptance is evidence about the stated propositions only.

## Reproduction evidence

| Check | Evidence |
|---|---|
| `lake build` (all three default targets) | 4171 jobs, completed successfully, zero warnings or `info:` notes (2026-09-19, after `fdb3383f`) |
| `lake build SP1Clean` / `lake test` / `lake lint` / `scripts/run_audit.sh` | Local logs at `fdb3383f`: 4167 main jobs, 4215 test jobs, lint passed, `AUDIT PASS` stamped at `fdb3383f` |
| Census currency | `docs/snapshots/axiom-census*.txt` and `docs/snapshots/axiom-ledger.md` stamped at `40ae1c68`; no `SP1Clean/` commit after the stamp |
| Proof hygiene | No `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, or `skipKernelTC` declaration in `SP1Clean/`, `ToClean/`, `ToMathlib/`; the only `sorry` strings are prose in three docstrings |
| Axiom census (main scope) | 2787 probed declarations; axioms are the three standard ones, 74 generated-Sail externs, and 23 `bv_decide` constants; no `sorryAx` |
| Root index | 917 modules on disk, 917 imports in `SP1Clean.lean`; `scripts/check_root_index.sh` passes |
| Provenance | 946 commits, single author, three merge commits; every head of PRs #110, #115, #116, #117, #119, #120, #121, #122 is an ancestor of HEAD |

## The theorems as the Lean states them

**The capstone target.** `SP1Clean/Soundness/Shard/Contract.lean` states the intended single
statement as a conditional lemma over two unfilled targets:

```lean
theorem statement_iff {ensemble : Ensemble (ZMod p) PublicIO} {profile : Profile}
    {image : ProgramImage} {source target : ExecutionSnapshot} {header : PublicIO (ZMod p)}
    (sound : SoundnessTarget ensemble profile image source target header)
    (compiler : CompilerTarget ensemble profile image source target header) :
    ensemble.Statement header ↔
      ∃ events, AdmissibleExecution profile p image source target events
```

Its proof is the generic `CompleteEnsemble.statement_iff` from `ToClean/Air/CompleteEnsemble.lean`
at the chosen interpretation. It fixes the shape of the claim; all content is in the two hypotheses,
neither of which is instantiated anywhere. `ensemble`, `profile`, `image`, `source`, `target`, and
`header` are all free. The file says this itself.

**The semantic spine.** `SP1Clean/FormalModel/Shard.lean`:

```lean
def Executes (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  ∃ valid : ExecutionSourceValid image source,
    ExecutionPath (policy characteristic image) (image.toGuestProgram valid.1.1)
      source.realize events target.realize

abbrev Profile := ℕ → ProgramImage → ExecutionSnapshot → ExecutionSnapshot →
  List ExecutionEvent → Prop
```

`ExecutionPath` (`SP1Clean/Model/Core/ExecutionPath.lean`) is the reflexive-transitive closure of
`ExecutionStep` (`SP1Clean/Model/Core/Execution.lean`) over `ExecutionState := ⟨sail, host, clock⟩`,
where `sail` is the official generated `SailState`. An ordinary step requires a running host, that
the committed program does not hold `ECALL` at the PC, and `SailRetiresNormally`; a syscall step is
the concrete host dispatcher `HostState.step` for the eight-call profile in
`SP1Clean/Model/Core/SyscallCode.lean`. The PolyFun view (`executionSystem`, `ExecutionSegment.iff_reachableIn`)
is a presentational equivalence whose directions carry the step proofs; it introduces no padding.
`ExecutionSnapshot` is the finite boundary with `equivalent_iff` proving executable comparison is
literal equality of complete realized states. Identity, composition, clock, and stopped-source
laws are proved on `Executes`.

**The installed mixed AIR.** `SP1Clean/Soundness/HostHintReadFinalSnapshot.lean`:

```lean
theorem source_execution_with_memory (valid : image.Valid)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events target hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧ …
```

The premises are a decidable loader check, the witness of the 87-table ensemble plus its singleton
verifier (`HostHintQueueBoundary.ensemble`), raw constraints, and raw balance. There is no readiness
bundle, provider-validity premise, semantic boundary binding, syscall-inactivity premise, or grounding
certificate. The conclusion retains the event multiset, final clock and PC, every native register and
aligned RAM value below `2^48`, the empty RAM domain above it, Sail runtime and register frames, all
three bookkeeping slots, the decoded final hint queue, the reconstructed host with the supplied banks
and exit, the public Exit binding for a newly halted endpoint, and the `checkFinal` characterization.

**The retained 55-table theorem.** `supported_core_native_sound` (`SP1Clean/Soundness/AIR.lean`)
remains closed. Its input relation carries fourteen premises once unfolded: public-input agreement,
constraints, balance; program well-formedness, `Commit.StatementFor`, the committed initial clock,
the three-field `ShardStartState`, `SailCodeMemoryCompatible`, and the four-field
`ProviderBindingContracts` (Program provider content, Memory-init content, Memory-init uniqueness,
Memory-finalize uniqueness); and `SyscallTableInactive` (no active syscall rows, a physically present
Halt table). Two of the five conclusion conjuncts (`program.WellFormed`, `ShardStartState`) are
premises re-exported.

**Completeness.** `supported_core_native_shard_correct_of_totality`
(`SP1Clean/Soundness/NativeCompleteness.lean`) is conditional on the unproved
`NativeShardTraceTotal`, and its admissible relation embeds the thirteen-field `NativeTraceReady`
bundle (`SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean`), including `exitZero` and
`syscallFree`. `compileExecution` is total as a function only through `getD emptyCompiledExecution`.
No compiler targets the mixed ensemble.

**Exact upstream.** `sp1_air_refinement_of_obligations` and `sp1_air_sound_of_obligations`
(`SP1Clean/Soundness/CoreAIR.lean`) consume an uninstantiated thirteen-field bundle; `sp1_air_sound`
and `sp1_air_refinement` are correctly absent.

## Findings

Ordered by weight. Each names the location and a recommendation; none is a proof deferral.

### 1. `Profile` is an unconstrained predicate on both sides of the capstone

`Profile` (`SP1Clean/FormalModel/Shard.lean`) is an arbitrary predicate on the characteristic, image,
both snapshots, and the event tape. Both `SoundnessTarget` and `CompilerTarget` are quantified over
the same free `profile`, and `statement_iff` is provable for `profile := fun _ _ _ _ _ => False`
with an unsatisfiable ensemble. The docstrings say what the profile must not contain; no Lean
obligation enforces it, and nothing in the repository instantiates it.

Recommendation: replace the bare predicate by a small semantic resource structure (active-clock
phase and range, store-permission table, finite capacities) whose predicate is derived, so that a
profile cannot mention AIR rows, compiler success, or grounding. Add a non-vacuity fixture that
inhabits `AdmissibleExecution` for the chosen structure before any instance of `SoundnessTarget`
is claimed. This is the roadmap's "semantic resource policy" milestone with an interface constraint.

### 2. `Executes` admits self-modifying code that the AIR forbids

The ordinary arm of `ExecutionStep` (`SP1Clean/Model/Core/Execution.lean`) is raw
`SailRetiresNormally` over mutable Sail memory; only host writes are proved ROM-safe
(`SP1Clean/Model/Core/HostSail.lean`). Both `ECALL` tests, `AboutToExecuteEcall`
(`SP1Clean/Model/Machine/Syscall.lean`) and `HostState.step`, read the committed `program.fetchWord`,
while the interpreter fetches from its own memory. After an ordinary store into the ROM window the
two arms can disagree with the interpreter: the model may dispatch a host call where Sail would
execute a rewritten word, or vice versa. The retained relation carried `SailCodeMemoryCompatible`;
it appears nowhere in `SP1Clean/Model/Core/`, `SP1Clean/FormalModel/Shard.lean`, or the
`HostHintRead*`/`LocalCore*` proofs. Soundness is unaffected because the AIR's store permission
derives ROM preservation, but completeness must exclude these paths, and `Executes` alone is not yet
a faithful guest-execution relation.

Recommendation: add a named ROM-preservation condition either to the ordinary step or to the
profile, with an `ExecutionPath` preservation lemma, so the semantic side states the restriction
that the AIR side proves.

### 3. The installed theorem's shape is not the capstone's shape

`source_execution_with_memory` is existential over `target` and concludes against AIR-internal
objects: the local `memoryFinalFrontier`, the `bankFinal` parameter, and `final.head`. The
`checkFinal` conjunct is a characterization of a Boolean function on every candidate snapshot, not an
installed circuit. `final : HostHintQueue.State` is a caller-supplied queue cursor that indexes the
ensemble (`SP1Clean/Soundness/HostHintQueueBoundary.lean`), and `channels` is an open caller-chosen
channel list. `SoundnessTarget` instead needs a path to the supplied `target.realize` from raw
acceptance of an ensemble indexed only by image, snapshots, and header. The roadmap records this
under "complete outgoing boundary"; the review adds the exact locations.

### 4. The completeness direction is not started for the mixed ensemble

There is no compiler from events to the 87-table witness; per-chip constructors exist under
`SP1Clean/Proofs/Chips/Host*`, the assembler does not. The 55-table compiler's domain contains the
readiness bundle that `SP1Clean/Soundness/Shard/Contract.lean` says the target domain must not
contain, and its unconditional form waits on `NativeShardTraceTotal`.

### 5. Three execution carriers with one per-step bridge

`ExecutionPath` (full state), `EventExecutionTrace`/`CoreShardSemanticWitness` (handler-parameterized,
no host), and `Machine.trajectory`/`sailMachine` (the `Option`-stuttering substrate of
`SP1Clean/Model/Semantics/MicroTime.lean`, `Truth.lean`, and the timed grounding engine) coexist.
The only bridge, `ExecutionStep.sailEvent`, uses `source.host.handler`, a different handler per
step, so it does not lift to paths. Any claim that the new contract subsumes the retained results
needs an explicit adapter; the roadmap requires one and none exists.

### 6. A duplicate carrier structure in one namespace

`NativeCore.ExecutionCarrier` (`SP1Clean/Soundness/CoreRowTransport.lean`) and
`NativeCore.GroundingCarrier` (`SP1Clean/Soundness/NativeCoreTransport.lean`) share eight of nine
fields with near-identical docstrings; the second is live in five `NativeCore*` modules. The Local
and Host layers correctly use `abbrev`s of `ExecutionCarrier`. The roadmap forbids a second
execution carrier; this one should be migrated to the `abbrev` pattern.

### 7. Disclosed profile restrictions that are premises, not consequences

Canonical syscall words test the full 64-bit register (`SP1Clean/Model/Core/SyscallCode.lean`)
while the pinned executor dispatches on the low 32 bits; commitment banks are mutable slots
(`SP1Clean/Model/Core/HostExecution.lean`) while the exact syscall AIR compares each commit to one
fixed public-values vector. Both are documented. Both must be placed in the profile or in an
explicit exact-refinement domain; neither may be assumed silently by a capstone instance.

### 8. Documentation contradicted the roadmap on the headline

Before this review's fixes, `README.md` and `docs/verification-report.md` presented
`supported_core_native_sound` as the headline theorem and `docs/overview.md` called it both
"retained" and "the current headline relation"; the 87-table installed witness was mentioned only in
`docs/roadmap.md`; `docs/release-audit.md` had no status row for the full-state target. The
same-day fixes reword these to "closed and retained", add the current target, and add the row.

### 9. Minor items

- `SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean` module docstring says "53-table"; the
  ensemble has 55. Left for a follow-up because a docstring edit invalidates the census stamp and
  forces a rebuild of every dependent.
- `SchedulePoint.Before` (`SP1Clean/Model/Machine/Schedule.lean`) is unconsumed outside its file.
- `SP1Clean/Model/Semantics/Decode.lean` is 2503 lines, above the repository's own split threshold.
- `sp1clean_stack_report.pdf` was ignored only through the machine-local `.git/info/exclude`; it is
  now in `.gitignore`.
- The four heavy CI jobs pinned succinctlabs' self-hosted runner labels and had no
  `timeout-minutes`; on the fork they could never start. Rewritten in the same consolidation.
- Clean is pinned to the personal fork `dtumad/clean` at `2dad7788`, disclosed in
  `docs/release-audit.md`; the branch must never be force-pushed.

## Repository readiness

| Item | State |
|---|---|
| Tracked size | 1220 files, 27.8 MB; largest file `docs/snapshots/axiom-census.txt` (2.3 MB); no binaries added |
| Leaked paths | None (`git grep` for home-directory paths is empty) |
| Secrets in CI | None referenced |
| Local build cache | `.lake/build` 4.0 GB (`lib` 1.6, `ir` 2.2); non-mathlib package builds about 0.6 GB; mathlib 6.4 GB from `lake exe cache get` |

## Follow-ups outside this consolidation

- Findings 1 and 2: the profile interface and the ROM-preservation condition, with fixtures.
- Finding 3: install `MemorySnapshot.checkFinal` and change coverage as circuits, derive the queue
  cursor internally, and restate the conclusion as equality with the supplied target.
- Finding 4: the mixed event-to-tables compiler.
- Findings 5 and 6: an explicit adapter between carriers, and the `abbrev` migration.
- Finding 9: the docstring count, the dead ordering, and the `Decode.lean` split.
- Marking the eight upstream pull requests superseded once the fork PR is reviewed.
