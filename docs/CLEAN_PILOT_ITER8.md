# Clean DSL pilot — iteration 8 (faithful table-interaction representation)

Status as of 2026-05-23. Plan:
`~/.claude/plans/make-a-plan-to-squishy-rossum.md`.

## TL;DR

Iter-8 closed the structural gap between SP1Clean's table-interaction
encoding and the source-of-truth SP1 Rust repo at
`/home/dtumad/Documents/sp1`. Four phases:

- **Phase 1** widened every chip's `Assertion.main` to emit
  `SP1Clean.OperandAccess.assertion` per register operand — the
  6-byte-lookup primitive that mirrors SP1's per-row memory-bus byte
  content (`Range(16)` × 5 + `U8Range` on scaled timestamp).
- **Phase 2** flipped 23 `ChipRow.Spec` arms from legacy `<Chip>.Spec`
  to `<Chip>.assertion.Spec` (Add was already done). Re-aimed all the
  `cpuStateSpec_of_spec_*` / `is_real_binary_*` / `nextPc_of_spec_*`
  per-chip dispatch lemmas at the FormalAssertion form.
- **Phase 3** added a memory-bus gating lemma + `ChipRow.isRealField`
  projection + padding-aware `aggregateMemoryAccessesFiltered`
  aggregator that drops `is_real = 0` rows. Side-by-side with the
  unfiltered aggregator.
- **Phase 4** added `MemoryGlobalCols` column struct + `.memInit` /
  `.memFinalize` `ChipRow` constructors (mirroring SP1's
  `MemoryInitCols` shape) + a `TraceStateBoundary` predicate that ties
  the trace's first-row `pc` to a committed `initial_pc` and the
  last-row `next_pc` to `final_pc`.

```
$ lake build SP1Clean
Build completed successfully (8580+ jobs).

$ lake build SP1Clean 2>&1 | grep -cE '^(error|warning):'
0
```

All new top-level trace-soundness theorems pass the axiom audit with
only `propext, Classical.choice, Quot.sound`.

## Phase 1: OperandAccess sweep (24 chips, ~5 days)

The plan called for every chip's `Assertion.main` to emit
`SP1Clean.OperandAccess.assertion` per register-operand memory access
(at canonical offsets +4 / +3 / +2 for op_a/b/c). 23 chips were swept
following the AddChip template from iter-7's iter-8-prep pass; Add was
already in the target shape.

**Operand-layout cheat sheet (the per-chip pattern):**

| Tier | Chips | Calls |
|------|-------|-------|
| 1-operand | UType, Jal | op_a/+4 |
| 2-operand | Addi, Branch, Jalr | op_a/+4, op_b/+3 |
| 3-operand R-type | Add, Sub, Subw, Bitwise, Lt, Addw, Mul, ShiftLeft, ShiftRight, DivRem | op_a/+4, op_b/+3, op_c/+2 |
| 2-reg + 1 RAM | LoadByte, LoadDouble, LoadHalf, LoadWord, LoadX0 | op_a/+4, op_b/+3 (RAM deferred) |
| 2-reg + 1 RAM | StoreByte, StoreDouble, StoreHalf, StoreWord | op_a/+4, op_b/+3 (RAM deferred) |

**Per-chip discharge:** new `memoryAccessesValid_of_spec_<chip>` lemmas
mirroring the Add POC at `MemoryConsistency.lean:733-749` projected the
new `OperandAccess.Assertion.Spec` conjuncts onto the
`memoryAccessSpec` clauses the trace aggregator consumes. 15 chips
have full per-chip discharge (Add + UType + Jal + Addi + Branch + Jalr
+ Sub + Subw + Bitwise + Lt + Addw + Mul + ShiftLeft + ShiftRight +
DivRem). The 9 Load/Store chips have register-side widening but no
per-chip discharge — see "RAM-access blocker" below.

**Build-cost notes:**
- 15 chips needed `set_option maxHeartbeats 800000 in` on their
  `elaborated` instance — `localLength_eq` synthesis hits the default
  200k cap for chips with > ~20 input fields.
- The obtain/refine ordering for OperandAccess clauses depends on
  emission order in `main`. Placing OperandAccess at the **end** of
  `main` (after all assertZero gates) is the canonical AddChip pattern
  and keeps the destructure clean. Branch attempted at start of main
  and required re-ordering.

**RAM-access blocker (Load/Store, 9 chips):** The chips' load_mem /
store_mem timestamp encoding uses a `(diff_low, diff_high)` split-form
gated by a `load_memory_flag` (for clock_high boundary crossings).
This shape doesn't match `OperandAccess.Spec`'s scaled-timestamp form
`(clk_low + offset - prev_low - 1 - diff_low_limb) * 65536⁻¹ < 256`,
which assumes both timestamp endpoints lie in the same clock_high
window. Fix requires a new `LoadOperandAccess.assertion` variant —
deferred to Phase 4.5. See
`feedback_load_store_ram_access_deferred.md`.

## Phase 2: ChipRow.Spec flip + nextPcValid dispatch (~2 days)

**Three flips:**

1. **`ChipRow.Spec` arms.** All 23 arms in
   `MemoryConsistency.lean:579-603` migrated from `<Chip>.Spec` to
   `<Chip>.assertion.Spec`. Mechanical one-line replacement.

2. **24 `cpuStateSpec_of_spec_*` lemmas.** Each lemma's body becomes
   `change <Chip>.Assertion.FormalSpec cols at h; exact h.<conjunct>`.
   Most chips have cpuStateSpec at conjunct 1; Addi has it at
   conjunct 2 (after the leading `AddOp.Spec`).

3. **24 `is_real_binary_*` lemmas.** Same pattern with a uniform
   `apply binary_of_assertZero; change + unfold + tauto` proof. The
   `unfold + tauto` is robust to per-chip conjunct-position variation
   (positions range from 4 to 11 depending on sum-of-flag structure).

**Jal gained `CPUState.assertion`** — a legacy iter-5 quirk: Jal's
original `main` had inline byte lookups for clk_0_16/clk_16_24 instead
of the `CPUState.assertion` subcircuit. Phase 2 added the subcircuit
emission + matching `cpuStateSpec` conjunct as position 1 of
`FormalSpec`, plus updated soundness/completeness proofs.

**§3b structural reality.** The plan framed §3b as "discharge
`TraceStateValid` from chip Specs". In practice the chain
(`a.next_pc = b.pc` for adjacent rows) is intrinsically about
adjacency — content no per-row chip Spec can provide. Phase 2
factored the discharge: per-row `nextPcValid` content (AddrAddOp.Spec
or analogous) comes from chip Specs via
`nextPcValid_of_chipRow_spec`; chronological adjacency stays a
verifier-supplied trace-shape hypothesis. The docstring on
`traceStateValid_of_chip_specs` documents this honestly.

## Phase 3: Multiplicity gating + padding-aware aggregator (~1.5 days)

**Genuinely new content:** `Memory_send_iff_isU64` —
`(.send (.memory ...) mult).toProp ↔ mult = 1 → Word.isU64 prev_value`
under `mult ∈ {0, 1}`. Covers both register and RAM address shapes
uniformly (`toProp` is address-independent).

**Documented why sum-of-flag and XOR-of-binary don't need new
lemmas:** the existing `ByteOpcode_send_iff_constrain` /
`Program_send_iff_clause` / `Memory_send_iff_isU64` accept any `mult`
with a binarity hypothesis. Phase 2's `is_real_binary_*` lemmas
already provide the binarity for sum-of-flag chips; the
`ALUTypeReader.Constraints`-emitted `(is_real - imm_c) * (is_real -
imm_c - 1) = 0` provides it for the XOR case. No per-arity wrappers
needed.

**Padding-aware aggregator** added side-by-side with the unfiltered
version: `aggregateMemoryAccessesFiltered` drops rows where
`isRealField = 0`. Two bridging lemmas:
`aggregateMemoryAccesses_eq_filtered_of_all_real` (no-padding traces
coincide) and `aggregateMemoryAccessesFiltered_of_all_padding`
(all-padding → empty list). Switching the trace-soundness pipeline to
use the filtered version is deferred (it would require re-discharging
the timestamp-sorted/nodup properties for the filtered list).

**`aggregateStateAccesses` didn't need filtering** — `pcChainProp`
already case-splits on `is_real ≠ 0` for adjacency, so padding rows
pass through vacuously.

## Phase 4: Boundary chips + TraceStateBoundary (~1.5 days)

New file `SP1Clean/MemoryGlobalChip.lean` with `MemoryGlobalCols`
mirroring SP1's `MemoryInitCols<T>`
(`/home/dtumad/Documents/sp1/crates/core/machine/src/memory/global.rs:256-298`,
13 fields). Both `MemoryGlobalInit` and `MemoryGlobalFinalize` share
the column layout in SP1; they differ only in interaction-kind
(InitControl=14 vs FinalizeControl=15) and address-monotonicity
direction.

**Minimal Phase 4 Spec:** `cols.is_real * (cols.is_real - 1) = 0`.
SP1's source-of-truth emits this binary gate at `global.rs:313`
(`builder.assert_bool(local.is_real)`); the rest of the chip's
constraint surface (range checks on addr/prev_addr/value,
`LtOperationUnsigned` monotonicity gate, two `IsZeroOperation`
witnesses) is deferred to a Phase 4.5 sub-iter that lifts
`MemoryGlobalCols` to a full `FormalAssertion`.

**ChipRow extension:** added `.memInit` / `.memFinalize` constructors
with placeholder arms across 6 projection functions
(`memoryAccesses = []`, `clockComponents = (clk_high, clk_low)` raw,
`Spec = MemoryGlobal.Spec`, `offsets = []`, `isRealField =
cols.is_real`, `cpuStateSpec = True`, `nextPcValid = True`,
`stateAccess` with placeholder `pc = next_pc = #v[0,0,0]`).

**Refactored two lemmas in `MemoryConsistencyClock.lean`**
(`rowAccessTuples_pairwise_of_cpuStateSpec`,
`rowAccessTuples_timestamp_range`) to handle boundary chips' empty
access lists via a `cases row <;> first | <interior> | <boundary>`
fallthrough pattern.

**`TraceStateBoundary` predicate** in `StateConsistency.lean`:
```
structure TraceStateBoundary (rows : List (ChipRow p))
    (initial_pc final_pc : Vector (ZMod p) 3) : Prop where
  initial_match : (rows.head?).map (·.stateAccess.pc) = some initial_pc
  final_match   : (rows.getLast?).map (·.stateAccess.next_pc) = some final_pc
```

**`trace_soundness_with_boundary`** strengthens
`trace_soundness_aggregateMemory` with the boundary closure. The
output now includes `TraceStateBoundary rows initial_pc final_pc`
alongside the offline-memory permutation, PC chain, and is_real
binary.

## Open work for follow-ups

**Phase 4.5 (Load/Store RAM + boundary memoryAccesses):** Both
involve the same structural mismatch — chip natural shape uses
`(diff_low, diff_high)` instead of scaled-timestamp form. Solving
either requires a new `LoadOperandAccess` (or
`BoundaryOperandAccess`) variant. Estimated half-day to design + half-day
per chip family.

**§4 (port 24 `correct_*` to Clean):** The dominant remaining cost.
Each chip needs its Sail equivalence stated on the Clean side; ~3
weeks total per the plan's estimate.

**§5 (Sail trace executor):** Half-day session.

**Step 6 (compose the ensemble theorem):** Half-day session, runs
after step 4 and step 5.

## References

- Plan: `~/.claude/plans/make-a-plan-to-squishy-rossum.md`
- Updated status: `docs/TRACE_SOUNDNESS_STATUS.md`
- Phase memories: `project_clean_pilot_iter8_phase2.md`,
  `project_clean_pilot_iter8_phase3.md`,
  `project_clean_pilot_iter8_phase4.md`
- Recipes: `feedback_operandaccess_sweep_recipe.md`,
  `feedback_load_store_ram_access_deferred.md`
