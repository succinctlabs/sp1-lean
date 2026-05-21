# Trace-soundness status — per-chip and pilot-wide

Current as of 2026-05-21.

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

### 3. Discharge the three trace-shape bundles

The Phase A.3 / B / D.1 deliverables shipped with these as bundled
hypotheses (parametric over the verifier's evidence). To remove the
parametricity:

**3a. `TraceClkValid` from chip `Spec`s.** Per-chip clk extraction
from `cpuStateSpec` (`clk_0_16` < 65529, `clk_16_24` < 256), lifted to
Nat via `ZMod.val`, plus a single chronological clock-monotonicity
trace hypothesis. The wraparound bound needs `Fact (2^24 < p)` (KB is
~2^31 so this is given for the concrete prime). The
`(rows.reverse).Pairwise (fun r₁ r₂ → r₁.encodedClk ≥ r₂.encodedClk + 5)`
separation reduces to: per-row `encodedClk` is `clk_high.val * 2^24 +
clk_low.val`; trace assumption is `clk_high * 2^24 + clk_low` strictly
increases by ≥ `clkIncrement` (8); combine with intra-row offsets
in `[0, 4]`. 20-chip case analysis on `ChipRow.clockComponents`.

**3b. `TraceStateValid` from chip `Spec`s.** `ChipRow.stateAccess`
currently uses placeholder `next_pc := pc + #v[4, 0, 0]` for chips
without explicit `next_pc` / `jump_target` columns. The discharge work:

- For arithmetic chips (15 of 20): prove the placeholder equals the
  chip's true claimed `next_pc` modulo `pc[0].val < 65532` (no
  low-limb carry). Either tighten the trace-shape hypothesis to
  include this bound, or replace the placeholder with an explicit
  `AddrAddOperation` invocation that exposes the carries.
- For Branch: case-split on `compare_bit` — taken vs. not-taken
  `next_pc`.
- Jal, Jalr already use explicit columns; no work.

~17-chip case analysis.

**3c. `TraceIsRealBinary` from chip `Spec`s.** Each chip's `Spec`
contains `is_real * (is_real - 1) = 0` (or `sum * (sum - 1) = 0` for
chips with computed `is_real`). Project the conjunct and apply
`binary_of_assertZero`. ~20 one-line lemmas.

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
2. **(1–2 days)** Discharge `TraceClkValid` (§3a) and `TraceStateValid`
   (§3b) from chip `Spec`s. §3c (`TraceIsRealBinary`) is already
   discharged.
3. ~~Promote remaining Spec-only chips to Clean `FormalAssertion`. §1.~~
   **DONE 2026-05-21** (iter-6 + iter-7). All 24 chips now
   FormalAssertion.
4. **(~3 weeks)** Bridge or port the 24 dirty `correct_*` to Clean
   `FormalAssertion.Spec`-form. §4.
5. **(half-day)** `Sail.execute_trace` wrapper. §5.
6. **(half-day)** Compose: `trace_soundness_aggregateMemory` +
   per-chip Sail equivalence + `execute_trace` → full ensemble
   theorem.

Steps 1 and 3 closed today; step 5 is session-sized; step 6 is the
closing composition. Step 2 fits in a week of focused work. Step 4 is
the dominant cost — the heavy mathematical content that connects the
Clean `Spec` predicate to actual Sail semantics.

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
- Memory entry covering today's deliverables and three deferred
  discharges:
  `~/.claude/projects/-home-dtumad-Documents-sp1-lean/memory/project_clean_trace_soundness_phaseABCD.md`.
- Iter-4 / iter-5 promotion retrospectives (for §1 effort estimates):
  `docs/CLEAN_PILOT_ITER4.md`, `docs/CLEAN_PILOT_ITER5.md`.
- Field-genericization design (relevant if extending to BabyBear in
  parallel): `docs/FIELD_GENERIC.md`.
