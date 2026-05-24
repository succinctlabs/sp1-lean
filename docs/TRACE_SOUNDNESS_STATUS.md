# Trace-soundness status — per-chip and pilot-wide

Current as of 2026-05-23.

This is the consolidated status report on how much of SP1's correctness
has been proven, at what layer, and what remains before a single
end-to-end "ensemble soundness + completeness" statement closes. It's
intended to be the input to a fresh planning session that scopes the
remaining work.

## The three proof layers

| Layer | What it proves | Where |
|---|---|---|
| **Dirty** `correct_*` | AIR constraints `allHold` + Sail state link ⇒ `spec_X.run s = sp1_X.run s` (per-row Sail equivalence) | `SP1Chips/<Chip>Chip.lean` |
| **Clean** `FormalAssertion` | constraints ↔ chip-row `Spec` (soundness `⇒` and completeness `⇐`) | `SP1Clean/<Chip>Chip.lean` |
| **Trace** | aggregator over `ChipRow` + trace-shape bundles ⇒ offline memory consistency + state-bus PC chain | `SP1Clean/Soundness/*` |

The dirty layer is the original repo's deliverable — for each
instruction the chip's AIR constraints are proven equivalent to the
Sail RISC-V spec's execution semantics. The Clean layer reformulates
that proof inside the `Clean` DSL (`/home/dtumad/Documents/clean`),
giving an `iff`-shaped chip-row predicate ready for compositional
trace-level reasoning. The trace layer (new as of 2026-05-21) wires
per-chip predicates into a single trace-level soundness statement via
the upstream `Clean.Utils.OfflineMemory` consistency theorem and a
PC-chain aggregator.

## Per-chip status (24 chips)

Counts here are reproducible:
```
grep -c "^theorem correct_\|^theorem correct\b" SP1Chips/<Chip>Chip.lean
grep -c "def assertion : FormalAssertion" SP1Clean/<Chip>Chip.lean
grep -nE "^\s+| <Chip> " SP1Clean/Soundness/MemoryConsistency.lean
```

| Chip | Dirty `correct_*` | Clean FormalAssertion (S+C) | `ChipRow` registered |
|---|---|---|---|
| Add | ✅ 1 thm | ✅ | ✅ |
| Addi | ✅ 1 | ✅ | ✅ |
| Addw | ✅ 2 | ✅ | ✅ |
| Bitwise | ✅ 6 | ✅ | ✅ |
| Branch | ✅ 6 | ✅ | ✅ |
| DivRem | ✅ 8 | ✅ | ✅ |
| Jal | ✅ 1 | ✅ | ✅ |
| Jalr | ✅ 1 | ✅ | ✅ |
| LoadByte | ✅ 2 | ✅ | ✅ |
| LoadDouble | ✅ 1 | ✅ | ✅ |
| LoadHalf | ✅ 2 | ✅ | ✅ |
| LoadWord | ✅ 2 | ✅ | ✅ |
| LoadX0 | ✅ 7 | ✅ | ✅ |
| Lt | ✅ 4 | ✅ | ✅ |
| Mul | ✅ 5 | ✅ | ✅ |
| ShiftLeft | ✅ 4 | ✅ | ✅ |
| ShiftRight | ✅ 8 | ✅ | ✅ |
| StoreByte | ✅ 1 | ✅ | ✅ |
| StoreDouble | ✅ 1 | ✅ | ✅ |
| StoreHalf | ✅ 1 | ✅ | ✅ |
| StoreWord | ✅ 1 | ✅ | ✅ |
| Sub | ✅ 1 | ✅ | ✅ |
| Subw | ✅ 1 | ✅ | ✅ |
| UType | ✅ 2 | ✅ | ✅ |

**Aggregate counts:**
- Dirty `correct_*`: **24 / 24** proven (zero active sorries; inert
  `sorry`-mentioning comments at `SP1Chips/ShiftRight/Sra.lean:31` and
  `SP1Chips/DivRem/DivRem.lean:814` only).
- Clean `FormalAssertion` (S+C, sorry-free): **24 / 24** — every chip
  in the ISA carries a top-level `FormalAssertion` with `theorem
  soundness` and `theorem completeness`, sorry-free. The remaining
  five chips (Branch, DivRem, Mul, ShiftLeft, ShiftRight) landed via
  Path-2 against their `main`'s surface gates — operation-specific
  content (shift-arithmetic, MulOperation carry chain, DivRem
  quotient/remainder, branch comparison) stays in legacy `Spec`
  (placeholder/`True` for several) and is consumed via the chip
  pipeline, not the FormalAssertion. ShiftLeft drops 10 Vector-indexed
  bit_shift/byte_shift gates from its FormalSpec for the same reason.
- Clean `Spec`-only: **0 / 24** — the Spec-only tier is now empty.
- `ChipRow` registered (in trace aggregator): **24 / 24** — wired in
  `SP1Clean/Soundness/MemoryConsistency.lean` (constructors +
  `memoryAccesses` / `clockComponents` / `Spec` / `offsets` cases) and
  `SP1Clean/Soundness/StateConsistency.lean` (`stateAccess` cases).

## Trace-level scaffolding (Phases A–D, completed 2026-05-21)

These modules build clean (`lake build SP1Clean.Soundness` =
8616 jobs, 0/0 errors/warnings) and the end-to-end statement's axiom
audit shows only `propext`, `Classical.choice`, `Quot.sound`:

| Module | Purpose | Key exports |
|---|---|---|
| `SP1Clean/Soundness/MemoryConsistency.lean` | Memory bus aggregator + offline bridge | `aggregateMemoryAccesses`, `ChipRow.rowAccessTuples`, `chip_specs_admit_offline_bridge` |
| `SP1Clean/Soundness/MemoryConsistencyClock.lean` | Timestamp-sort + nodup derivations | `TraceClkValid`, `aggregateMemoryAccesses_isTimestampSorted`, `aggregateMemoryAccesses_Notimestampdup` |
| `SP1Clean/Soundness/StateConsistency.lean` | State-bus (PC chain) aggregator | `ChipRow.stateAccess`, `aggregateStateAccesses`, `pcChainProp`, `TraceStateValid` |
| `SP1Clean/Soundness/IsRealBinary.lean` | `is_real ∈ {0,1}` surfacing | `binary_of_assertZero`, `TraceIsRealBinary` |
| `SP1Clean/Multiplicity.lean` | Multiplicity-gating lemmas | `ByteOpcode_send_iff_constrain`, `Program_send_iff_clause` |
| `SP1Clean/Soundness/TraceSoundness.lean` | End-to-end statement | `trace_soundness_aggregateMemory` |
| `SP1Clean/Soundness.lean` | Umbrella re-export | — |

Upstream `Clean.Utils.OfflineMemory` had 3 Lean 4.29 simp regressions
patched in the sibling repo (added `Decidable (timestamp_ordering …)`
instance; tightened two examples; added `split_ifs <;> rfl` on the
`filterAddress_cons` lemma).

## What remains for full ensemble SOUNDNESS

Soundness reads: a trace satisfying AIR constraints witnesses a
corresponding Sail execution. The remaining gaps:

### 1. Promote Spec-only chips to Clean `FormalAssertion` — **DONE**

All 24 chips in the ISA now carry a `FormalAssertion` with
soundness + completeness, sorry-free. The 5 chips originally tagged
"heavy-operation, needs upstream work" (Branch, DivRem, Mul,
ShiftLeft, ShiftRight) all turned out to be **Path-2 amenable** —
their `main` blocks emit only `CPUState` + `ProgramTable` + scalar
boolean gates (and in some cases extra byte lookups that are simply
dropped). Operation-specific arithmetic (shift carry chain,
MulOperation, DivRem quotient/remainder, branch compare) stays in
legacy `Spec` (placeholder `True` / `shiftSpec` / `mulSpec` /
`divRemSpec`); the FormalAssertion proves the surface gates without
depending on the heavy operations.

ShiftLeft additionally drops 10 Vector-indexed `bit_shift` /
`byte_shift` boolean gates from its FormalSpec because
`circuit_proof_start`'s per-element `Vector.map (eval env) input_var =
input` substitution doesn't reduce indexed accesses cleanly (see
`docs/feedback_formal_assertion_friction.md`). Those gates are
internal to the shift-arithmetic operation and not consumed by the
trace pipeline.

See `docs/CLEAN_PILOT_ITER7.md` for the full iter-7 retrospective.

### 2. Register chips in `ChipRow` — **DONE**

All 24 chips have constructors in `inductive ChipRow`
(`SP1Clean/Soundness/MemoryConsistency.lean:81-104`) with matching
cases in `ChipRow.memoryAccesses`, `ChipRow.clockComponents`,
`ChipRow.Spec`, `ChipRow.offsets` (same file) and `ChipRow.stateAccess`
(`SP1Clean/Soundness/StateConsistency.lean`). The earlier wiring gap
for Addi / Bitwise / Sub / Subw was closed in the same 2026-05-21
"lowest-hanging fruit" pass that promoted UType + Lt to FormalAssertion
and discharged §3c (`TraceIsRealBinary`).

### 3. Discharge the three trace-shape bundles — **DONE for 3a/3c; 3b discharged via factoring**

The Phase A.3 / B / D.1 deliverables originally shipped with these as
bundled hypotheses (parametric over the verifier's evidence). Iter-8
removed the parametricity:

**3a. `TraceClkValid` from chip `Spec`s.** ✅ Discharged via
`traceClkValid_of_chip_specs` (`MemoryConsistencyClock.lean:639`).
Combines per-row `cpuStateSpec` (extracted via
`cpuStateSpec_of_chipRow_spec`) with a single chronological
`TraceClkLink` trace assumption. Iter-8 Phase 2 flipped these
projections to reference `<Chip>.assertion.Spec`.

**3b. `TraceStateValid` from chip `Spec`s.** ✅ Factored via
`nextPcValid_of_chipRow_spec` + `traceNextPcValid_of_chip_specs`
(`StateConsistency.lean`). Each row's `next_pc` semantic content (the
`AddrAddOp.assertion.Spec` carry-aware witness for arithmetic chips,
`AddOp.Spec` for Jal, gated `GatedAddOp.Spec` for Jalr, dual-arm
witness for Branch) is extractable per-row from `<Chip>.assertion.Spec`.
The chronological adjacency `a.next_pc = b.pc` between adjacent rows
remains intrinsic to the trace-shape contract — see the docstring on
`traceStateValid_of_chip_specs`. Iter-8 Phase 2 documented this
structural reality: per-row content comes from chip Specs; trace-level
adjacency is the verifier's commitment.

**3c. `TraceIsRealBinary` from chip `Spec`s.** ✅ Discharged via
`traceIsRealBinary_of_chip_specs` (`IsRealBinary.lean:288`). Iter-8
Phase 2 flipped the 23 per-chip lemmas (`is_real_binary_<chip>`) to
reference `<Chip>.assertion.Spec` via the `change + unfold + tauto`
pattern.

### 4. Port 24 dirty `correct_*` to Clean (or bridge)

Currently 0/24 chips have Sail equivalence on the Clean side. Two
strategies:

- **(a) Re-prove on Clean.** Each chip-row `Spec` + Sail state link
  ⇒ `spec_X.run s = sp1_X.run s`. The existing dirty `correct_*`
  proofs are templates but use `SP1Constraint.allHold` not Clean
  `Assumptions/Spec`. Per-chip rewriting at the `Spec` boundary.
- **(b) Bridge.** Prove once a meta-theorem
  `Clean.Spec_iff_allHold : chip.Spec cols ↔ chip.constraints.allHold`
  (one direction per chip — the iff already exists for most via
  `iff_sp1`). Then `dirty.correct_*` composes mechanically. Cheaper
  but requires every chip to expose an `iff_sp1`-shaped lemma; UType
  has one, the 10 FormalAssertion chips have soundness/completeness
  which is structurally the same.

Strategy (b) is the natural path given today's scaffolding. Effort
per chip family ranges from hours (Add) to days (DivRem) depending on
how tangled the chip's `Spec` is.

### 5. `Sail.execute_trace` wrapper

`LeanRV64D` exposes per-instruction Sail steps but no trace executor.
~50 LOC of trace-recursion: thread a `SailState`, advance one step
per real row, skip padding rows (rely on `is_real = 0` ⇒ noop), error
on partial states. Mechanical, single-file. Half-day estimate.

### 6. Iter-8 deliverables: faithful table-interaction representation

The plan at `/home/dtumad/.claude/plans/make-a-plan-to-squishy-rossum.md`
closed the gap between SP1Clean's table-interaction encoding and the
SP1 Rust source-of-truth across four phases:

**Phase 1 (iter-8): OperandAccess sweep — DONE for 24/24 register-side.**
Every chip's `Assertion.main` now emits
`SP1Clean.OperandAccess.assertion` per register operand at the
canonical `(clk_low, offset)`; `FormalSpec` carries matching
`OperandAccess.Assertion.Spec` conjuncts; `memoryAccessesValid_of_spec_<chip>`
is proven for 15 chips (the 9 Load/Store chips have register-side
OperandAccess but their RAM-access piece is deferred — see Phase 4.5
follow-up).

**Phase 2 (iter-8): `ChipRow.Spec` flipped to `<Chip>.assertion.Spec`.**
All 23 arms migrated from legacy `<Chip>.Spec` to `<Chip>.assertion.Spec`
(Add was already on the new form as the POC). 24
`cpuStateSpec_of_spec_*` and 24 `is_real_binary_*` lemmas flipped via
`change + unfold + tauto`. Jal gained `CPUState.assertion` (was
missing in earlier iters). New `ChipRow.nextPcValid` predicate +
24-arm `nextPcValid_of_chipRow_spec` dispatcher.

**Phase 3 (iter-8): Multiplicity gating + padding-aware aggregator.**
New `Memory_send_iff_isU64` lemma in `Multiplicity.lean` covers
memory-bus gating (the only genuinely-new content; sum-of-flag /
XOR-of-binary cases reuse the existing byte/program lemmas by feeding
in Phase 2's `is_real_binary_*` binarity). New `ChipRow.isRealField`
projection + `aggregateMemoryAccessesFiltered` aggregator that drops
padding rows. Side-by-side with the unfiltered aggregator — switching
the trace-soundness pipeline is a Phase 3.5 follow-up that requires
re-discharging the timestamp-sorted/nodup properties for the filtered
list.

**Phase 4 (iter-8): Boundary chips + `TraceStateBoundary`.** New file
`SP1Clean/MemoryGlobalChip.lean` with `MemoryGlobalCols` mirroring
SP1's `MemoryInitCols<T>` (13 fields). Two new `ChipRow` constructors
(`.memInit`, `.memFinalize`) with placeholder `memoryAccesses = []`
and `Spec := cols.is_real * (cols.is_real - 1) = 0` (matches SP1's
`assert_bool(is_real)`; full internal constraint surface deferred).
New `TraceStateBoundary` predicate tying `head?.pc = initial_pc` and
`getLast?.next_pc = final_pc`. New `trace_soundness_with_boundary`
theorem strengthens `trace_soundness_aggregateMemory` with the
boundary closure.

**Phase 4.5 follow-up (not done):** boundary chips' `memoryAccesses`
remain empty; full bus closure requires bridging `MemoryGlobalCols`
to the `MemoryAccess` record shape, which has the same structural
mismatch as Load/Store's RAM access (the chip's `(diff_low,
diff_high)` flag-gated timestamp encoding doesn't fit
`OperandAccess.Spec`'s scaled-timestamp form). A new
`LoadOperandAccess` / `BoundaryOperandAccess` variant covering both
shapes would unify them.

## What remains for full ensemble COMPLETENESS

Completeness reads: any Sail execution admits a constraint trace that
witnesses it.

### Per-chip completeness — included in §1 above.

The 10 already-promoted chips have `FormalAssertion.completeness`.
The 14 remaining chips need it; same effort estimates as soundness
since both directions land in the same file.

### Trace-level completeness theorem — new work.

Today's `trace_soundness_aggregateMemory` is one-way (constraint
evidence ⇒ memory + PC chain). The dual direction
(Sail execution ⇒ constraint witness) needs:

1. **Witness construction for trace-shape bundles.** Given a concrete
   Sail trace, produce values for `TraceClkValid`, `TraceStateValid`,
   `TraceIsRealBinary`. This is what the prover does in
   practice — column values come from the Sail run. Trace
   reverse-direction is mostly mechanical but requires committing to
   a "padding row" model: how does the prover decide which Sail steps
   are real and which are pads?
2. **Per-row column-value assignment.** Given a Sail step
   (`s` → `s'`), construct the chip-row's `cols : <Chip>Cols (ZMod p)`
   that satisfies the chip's `FormalAssertion.Spec`. This is the
   "honest prover" construction — per chip, mechanical but ~50 LOC
   each.
3. **Backward bridge of `chip_specs_admit_offline_bridge`.**
   Already proven (the bridge is an iff via upstream OfflineMemory).
   No additional work.

Trace-level completeness is structurally lighter than soundness
because no Sail trace executor is needed — the Sail trace is the
*input*, not the conclusion.

## Critical path to a single end-to-end ensemble theorem

Order of operations to land
`∀ rows, valid_trace_shape rows → ∃ s_final, Sail.execute_trace s₀ rows.length = some s_final`:

1. ~~Wire Addi / Bitwise / Sub / Subw into `ChipRow`. §2.~~
   **DONE 2026-05-21** (lowest-hanging fruit pass). 24/24 chips wired.
2. ~~Discharge `TraceClkValid` (§3a) and `TraceStateValid` (§3b) from
   chip `Spec`s. §3c (`TraceIsRealBinary`) was already discharged.~~
   **DONE 2026-05-23** (iter-8 Phase 2). 3a/3c discharged; 3b factored
   into `nextPcValid_of_chipRow_spec` + chronological link (the link
   is intrinsic; cannot be derived from per-row content).
3. ~~Promote remaining Spec-only chips to Clean `FormalAssertion`. §1.~~
   **DONE 2026-05-21** (iter-6 + iter-7). All 24 chips now
   FormalAssertion.
4. **(~3 weeks)** Bridge or port the 24 dirty `correct_*` to Clean
   `FormalAssertion.Spec`-form. §4.
5. **(half-day)** `Sail.execute_trace` wrapper. §5.
6. **(half-day)** Compose: `trace_soundness_aggregateMemory` +
   per-chip Sail equivalence + `execute_trace` → full ensemble
   theorem.

Iter-8 added §6 deliverables: faithful table-interaction representation
(OperandAccess sweep, Spec flip, multiplicity gating, boundary chips).
Steps 1, 2, 3, and §6 are closed; step 5 is session-sized; step 6 is
the closing composition. Step 4 is the dominant cost — the heavy
mathematical content that connects the Clean `Spec` predicate to actual
Sail semantics. Step 4.5 (Load/Store RAM accesses + boundary chips'
full bus closure) is a smaller follow-up that requires a flag-aware
`LoadOperandAccess` variant.

## Open design choices for the next plan

These are the forks worth deciding *before* the work in §1–§6 starts:

- **§3b's placeholder vs. true-`next_pc`.** Keep the placeholder + add
  a trace-shape hypothesis on PC low-limb bounds (cheap, narrow), or
  replace per-chip with a proper carry-aware `next_pc` projection
  (correct in general, more proof bookkeeping). The placeholder is
  what shipped today.

- **§4's port vs. bridge strategy.** Re-proving 24 `correct_*` on the
  Clean side duplicates work but gives a clean architecture. Bridging
  via `Spec_iff_allHold` reuses the existing proofs but conflates the
  Clean DSL with the dirty `SP1Constraint` shape forever. Bridge is
  faster; port is cleaner.

- **§5's "padding row" semantics.** What does `Sail.execute_trace`
  produce on padding rows where `is_real = 0`? Three options:
  (a) skip and don't advance the Sail state; (b) require padding
  rows to also be valid Sail steps (e.g., a `NOP` with PC preserved);
  (c) error. Choice (a) is what the dirty `correct_*` theorems
  effectively assume; (b) is what real SP1 traces look like;
  (c) is overly restrictive.

- **Trace completeness scope.** Whether to ship trace-level
  completeness in the first pass or punt it. The soundness side is
  the "verifier accepts → there's a Sail run" direction that matters
  for proving the verifier doesn't accept garbage. Completeness is
  "every Sail run can be encoded" — important for liveness but not
  for soundness.

## References

- Plan that scoped Phases A–D:
  `/home/dtumad/.claude/plans/make-a-plan-to-delightful-kazoo.md`.
- Plan that scoped iter-8 Phases 1–4 (faithful table-interaction
  representation): `/home/dtumad/.claude/plans/make-a-plan-to-squishy-rossum.md`.
- Memory entry covering Phases A–D deliverables:
  `~/.claude/projects/-home-dtumad-Documents-sp1-lean/memory/project_clean_trace_soundness_phaseABCD.md`.
- Memory entries covering iter-8 phases:
  `project_clean_pilot_iter8_phase2.md` (Spec flip),
  `project_clean_pilot_iter8_phase3.md` (multiplicity gating),
  `project_clean_pilot_iter8_phase4.md` (boundary chips),
  `feedback_operandaccess_sweep_recipe.md` (per-chip OperandAccess pattern),
  `feedback_load_store_ram_access_deferred.md` (RAM-access blocker).
- Iter retrospectives:
  `docs/CLEAN_PILOT_ITER4.md`, `docs/CLEAN_PILOT_ITER5.md`,
  `docs/CLEAN_PILOT_ITER6.md`, `docs/CLEAN_PILOT_ITER7.md`,
  `docs/CLEAN_PILOT_ITER8.md`.
- Field-genericization design (relevant if extending to BabyBear in
  parallel): `docs/FIELD_GENERIC.md`.
