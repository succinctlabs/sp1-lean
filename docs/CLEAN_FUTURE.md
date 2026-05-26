# SP1Clean — Open work & roadmap

What remains for full ensemble soundness + completeness, per-chip sorry register, phased migration plan, and durable lessons from prior iterations. Companion to `docs/CLEAN_OVERVIEW.md` (current state).

## Critical path to a single end-to-end ensemble theorem

Order of operations to land `∀ rows, valid_trace_shape rows → ∃ s_final, Sail.execute_trace s₀ rows.length = some s_final`:

1. ~~Wire Addi / Bitwise / Sub / Subw into `ChipRow`.~~ **DONE 2026-05-21** (lowest-hanging fruit pass). 24/24 chips wired.
2. ~~Discharge `TraceClkValid`, `TraceStateValid`, `TraceIsRealBinary` from chip `Spec`s.~~ **DONE 2026-05-23** (iter-8 Phase 2). 3a/3c discharged via `traceClkValid_of_chip_specs` and `traceIsRealBinary_of_chip_specs`; 3b factored into `nextPcValid_of_chipRow_spec` + chronological link (the link is intrinsic; cannot be derived from per-row content).
3. ~~Promote remaining Spec-only chips to Clean `FormalAssertion`.~~ **DONE 2026-05-21** (iter-6 + iter-7). All 24 chips now FormalAssertion.
4. **(~3 weeks)** Bridge or port the 24 dirty `correct_*` to Clean `FormalAssertion.Spec`-form. **Dominant remaining work.** See §"Step 4 — bridge or port dirty correct_*" below.
5. **(half-day)** `Sail.execute_trace` wrapper. `LeanRV64D` exposes per-instruction Sail steps but no trace executor. ~50 LOC of trace-recursion: thread a `SailState`, advance one step per real row, skip padding rows (rely on `is_real = 0` ⇒ noop), error on partial states. Mechanical, single-file.
6. **(half-day)** Compose: `trace_soundness_aggregateMemory` + per-chip Sail equivalence + `execute_trace` → full ensemble theorem.

Iter-8 added §6 deliverables: faithful table-interaction representation (OperandAccess sweep, Spec flip, multiplicity gating, boundary chips). Steps 1, 2, 3, §6 are closed. Step 4 is the dominant cost. Step 4.5 (Load/Store RAM accesses + boundary chips' full bus closure) is a smaller follow-up that requires a flag-aware `LoadOperandAccess` variant.

### Step 4 — bridge or port dirty `correct_*`

Currently 0/24 chips have Sail equivalence on the Clean side. Two strategies:

- **(a) Re-prove on Clean.** Each chip-row `Spec` + Sail state link ⇒ `spec_X.run s = sp1_X.run s`. The existing dirty `correct_*` proofs are templates but use `SP1Constraint.allHold` not Clean `Assumptions/Spec`. Per-chip rewriting at the `Spec` boundary.
- **(b) Bridge.** Prove once a meta-theorem `Clean.Spec_iff_allHold : chip.Spec cols ↔ chip.constraints.allHold` (one direction per chip — the iff already exists for most via `iff_sp1`). Then `dirty.correct_*` composes mechanically. Cheaper but requires every chip to expose an `iff_sp1`-shaped lemma; UType has one, the 10 FormalAssertion chips have soundness/completeness which is structurally the same.

Strategy (b) is the natural path given today's scaffolding. Effort per chip family ranges from hours (Add) to days (DivRem) depending on how tangled the chip's `Spec` is.

## Two open `sorry`s in the multiplicity-bus refactor

`docs/MULTIPLICITY_BUS.md` owns the closure plans; this file is just the pointer:

- `SP1Clean/AddwChip/Circuit.lean:152` — AddwChip `op_c` completeness gap.
- `SP1Clean/Soundness/MemoryConsistency.lean:1067` — Memory bus addw discharge.

Both have clear closure paths in `MULTIPLICITY_BUS.md` §Phase 3–5. Start there if you're picking either up cold.

## Per-chip sorry register & verdicts

Audit dimensions (D1 spec semantic purity, D2 composition fidelity, D3 multiplicity gating, D4 Sail isolation, D5 completeness reachability) are defined in the original audit; treat them as the methodology for each chip's verdict. Total at audit time (2026-05-25): **82 sorry occurrences across 25 files**. Estimated delta if Phases 2–4 land: −45 to −60.

### Chips

| Chip | Verdict | Sorries | Next action |
|---|---|---|---|
| **AddChip** | canonical | 0 | (reference baseline) |
| **AddiChip** | mechanical (Phase 2) | 1 | Drop `AddOp.RawSpec` from `Cols.FormalSpec`; restate as `is_real = 1 → (isU64 ∧ BV equation)`; bridge via `AddOp.iff_sp1_full` |
| **AddwChip** | mechanical (Phase 2) | 0 | Drop `AddwOp.Spec` carry-form from `Cols.FormalSpec`; add `AddwOperation.iff_sp1_full` sibling |
| **SubChip / SubwChip** | mechanical (Phase 2) | 0 / 0 | Same shape as Addi recipe; add `SubOperation.iff_sp1_full` / `SubwOperation.iff_sp1_full` |
| **JalChip** | mechanical (Phase 2) | 4 | Drop `AddOp.RawSpec` ×2 (jump-target + return-address); bridge via `AddOp.iff_sp1_full` ×2 |
| **JalrChip** | mechanical (Phase 2) | 0 (body) | Restate `GatedAddOp` disjunct as semantic; promote `CPUState` to `Gated` |
| **UTypeChip** | mechanical (Phase 2) | 2 | Replace `(AddOperation.constraints …).allHold` envelope with `AddOp.assertion.Spec` (gated `is_real - op_a_0`); migrate `cpuStateSpec` → `CPUState.Gated.Assertion.Spec` |
| **LtChip** | mechanical-extended (Phase 2) | 7 | Structure already canonical; close `LtChip/SailBridge` sorries by composing existing `LtOperationSigned.spec.{signed,unsigned}` bridges |
| **BitwiseChip** | needs-Gated (Phase 3) | 8 | Migrate to `CPUState.Gated` / `ALUTypeReader.Gated`; wrap `BitwiseU16Op.assertion` as proper subcircuit; restate `FormalSpec` semantically |
| **MulChip** | needs-Gated (Phase 3) | 9 | Migrate readers to `.Gated`; reshape `MulOp` to semantic-only (Phase 5 prereq: `MulOperation.iff_sp1_full`); restate per-selector `is_<sel> = 1 → …` |
| **ShiftLeftChip / ShiftRightChip** | needs-Gated (Phase 3) | 10 / 12 | Migrate readers to `.Gated`; add `RV64.sll`/`sllw`/`srl`/`sra` semantic conjuncts gated on `is_real = 1`; reduce structural arithmetic to internal `main` detail. **Closer to ground-up than mechanical.** |
| **Load{Byte,Half,Word,Double}** | needs-memory-routing (Phase 4) | 0 each | Migrate memory access through `LoadMemoryAccessGated.assertion` (already exists); promote `CPUState` to `.Gated`; add semantic conjunct; update `ChipRow.memoryAccesses .<chip>` to `[]` |
| **Store{Byte,Half,Word,Double}** | needs-memory-routing (Phase 4) | 0 each | Same recipe via `StoreMemoryAccessGated.assertion` |
| **LoadX0Chip** | scope-fence (Phase 6) | 1 | After Loads migrated, restate as Load-shape specialized to `op_a_write_value = 0` |
| **BranchChip** | scope-fence (Phase 6) | 4 | 6-way selector + PC-update semantics; recipe doesn't fit cleanly. Keep current sorries with breadcrumbs |
| **DivRemChip** | scope-fence (Phase 6) | ~12 | Canonical "scope-fence" case per CLAUDE.md. Keep breadcrumbed sorries; revisit after Phases 2–4 stabilize the recipe |
| **MemoryGlobalChip** | scope-fence (Phase 6) | 0 | Boundary chip; needs trace-level `memoryAccess` discharge in multiplicity bus |

### Operations

| Operation | Verdict | Sorries | Next action |
|---|---|---|---|
| **AddOperation** | op-canonical | 0 | (reference baseline) |
| **BitwiseU16Operation, IsZero, U16MSB, U16toU8Safe/Unsafe, GatedLtSigned/Unsigned, Load{Byte,Half,Word}Selector, Store*Assembler, Load/StoreMemoryAccessGated** | op-canonical-adjacent | 0 each | None |
| **SubOperation / AddwOperation / SubwOperation / AddrAddOperation / GatedAddOp / BitwiseOperation / LtOperationUnsigned** | op-mechanical | 0 each | Apply AddOp `a8e50fb` recipe: drop `Spec := <Op>.Spec`, restate as `is_real = 1 → (isU64 ∧ <BV equation>)`; add `spec_inv` + `iff_sp1_full` siblings |
| **LtOperationSigned** | op-mechanical | 1 | Close `LtOperationSigned.lean:222` bridge body (Vector-shape mismatch) |
| **IsZeroWordOperation, IsEqualWordOperation, U16CompareOperation** | op-stub | inline-comment sorries (verify with `lake build`) | Complete proof bodies |
| **MulOperation** | op-stub (Phase 5 prereq) | 3 | Close `:340, :349, :353` per-selector stubs; finalize semantic form (uses `execute_MUL_pure` from RISCV.SailPure — borderline D4) |
| **AddressShape** | op-stub | 2 | `Operations/AddressShape.lean:80, :84` — emit boolean gates / bit-decomp lookup per inline future-work comment |

## Phased migration plan

Adapted from the original "Adopting Clean as the source of truth" roadmap. The long-term target is Clean's `Assertion.main` as canonical, SP1's auto-generated `constraints` as a *validator* checked against the Clean source on every regen.

### Phase A — subcircuit gating combinator

Today, multiple chips and operations carry constraint clauses of the form `(SubOp.constraints …).allHold_poly` multiplied by a per-row selector (`is_real`, `is_real − op_a_0`, an opcode flag). When the multiplier is 0, every conjunct vacuously holds; when 1, the operation's constraints must hold. Clean's subcircuit DSL has no gate combinator — calling `AddOp.assertion` from `JalrChip.Assertion.main` forces the carry chain unconditionally; on padding rows or JALR `op_a = x0` rows, completeness fails.

`Gated.assertion : (gate : Expression) → (sub : FormalAssertion α β) → FormalAssertion α β` is the single library addition. Soundness: `gate * sub.constraints = 0 → gate = 0 ∨ sub.constraints = 0`. Completeness: pick a witness depending on `gate`. **~80 LoC** of Clean infrastructure (either upstream or SP1Clean-local) + ~5 LoC per use site. Status: the `GatedAddOp.assertion` (iter-5 Phase-A landing) demonstrated the approach; full `Gated.assertion` combinator generalization unblocks Lt, Branch (×6 gated `LtOperationSigned`), and any future gated-operation chip.

### Phase B — heavy operations

Each gets a Clean `<Op>.assertion : FormalAssertion (ZMod p) Inputs` plus an `iff_sp1` lemma. Ordering by least-cost to highest-cost:

1. **LtOperationSigned** (~150 LoC). Unblocks Lt, Branch (×6), and serves as Tier-2 test bed once Phase-A's `Gated.assertion` exists.
2. **SubOperation** (~80–120 LoC) — borrow→natural carry-form bridge. SP1 emits `d_i` borrows; SP1Clean Spec uses natural `c_i`. Already reconciled in `SP1Operations.Operation.SubOperation.allHold_constraints_iff_poly` with a 4× `linear_combination * hbridge` cascade — replicate in the FormalAssertion proof. Unblocks Path-1 promotion for Sub/Subw chips.
3. **U16CompareOperation, U16toU8Operation{Safe,Unsafe}, IsZeroWordOperation, IsEqualWordOperation** (~50–100 LoC each, all share the AddOp-style structural shape).
4. **AddrAddOperation, AddressOperation** (~80 LoC each). Used by Loads and Stores. Once mirrored, all 7 Load/Store chips drop into Path-2 FormalAssertion mechanically.
5. **ShiftLeft / ShiftRight** (~200–300 LoC each). Bit-decomposition + shift power chain + byte-shift one-hot + limb-shift correctness; SP1 needed `maxHeartbeats 100M`. Budget several days each. Test the Phase-A heartbeat tooling here before tackling Mul.
6. **MulOperation** (~400–600 LoC). 16-limb carry chain; uses U16toU8 + Bitwise sub-fragments. Defer until Shifts validate the approach.
7. **DivRemOperation** (~400+ LoC). Composes MulOperation (×2) + IsZeroWord + AddOperation. Last in priority.

**Cardinal rule:** the Clean `<Op>.Spec` is **definitionally close** to the SP1-side `<Op>.allHold_constraints_iff_poly` RHS. Never re-derive the spec content from the constraint definition — just rename fields and reshape into the Clean record. `iff_sp1` then becomes a one- or two-line `simp` (`AddOperation.iff_sp1` is the template).

### Phase C — reader and CPU-state full FormalAssertion (parallelizable)

CPUState is promoted (`SP1Clean/Reader/CPUState.lean:217`). Other readers are iff-only:

- `SP1Clean/Reader/ALUTypeReader.lean`
- `SP1Clean/Reader/ITypeReader.lean`
- `SP1Clean/Reader/RTypeReader.lean`
- `SP1Clean/Reader/JTypeReader.lean`

Promoting each lets the corresponding chips drop bare `lookup ProgramTable` / `lookup MemoryAccess` calls from `Assertion.main` in favor of subcircuit calls. This sidesteps the Path-1 `Expression.eval env input_var_<vec>[k]` friction. Cost per reader: ~150–200 LoC, modeled on `CPUState.assertion`. Friction to expect: each reader emits *both* program/byte lookups (subcircuit-friendly today) *and* memory sends (need Phase-D / OfflineMemory bridge first). For early iterations, ship readers that drop the memory sends from `FormalSpec` (Path-2 style); add them back later.

### Phase D — write-back tooling

Endgame, after Phases A–C have closed the gap. A small Lean tactic or `#eval` script consumes a `FormalAssertion.elaborated` and emits an SP1-flavored `Vector (Fin KB) N → SP1ConstraintList`. Two paths:

- **D1.** Auto-generate the SP1 `constraints` function from the Clean `Assertion.main`. Most aggressive — Clean is the only source. Eliminates the constraint compiler.
- **D2.** Keep both. Diff the output of `sp1-constraint-compiler` against a Clean-derived dump. Discrepancies fail CI.

**Recommend D2 as the default.** Preserves the SP1 constraint compiler as a useful artifact in its own right (and the link to upstream `Verified-zkEVM/sp1-constraint-compiler`'s correctness story), while making Clean's `Assertion.main` the spec source of truth.

## Bridging hard SP1 proofs without rewriting

The hardest proofs in this repo — DivRem's 5-layer `_poly` helper architecture, ShiftLeft's bit-decomposition tower, MulOperation's 16-limb carry chain — must **not** be rewritten in Clean. The three-layer bridging discipline:

```
Layer 0 — SP1 _poly lemmas (genuinely hard, never touch)
   SP1Operations.<Op>.allHold_constraints_iff_poly
   SP1Chips.<Chip>.allHold_constraints_iff (via spec_<op>)
        ↑ reused by
Layer 1 — Operation-level iff_sp1 in SP1Clean (thin re-export, ~5–15 lines)
        ↑ used by
Layer 2 — Chip-level iff_sp1 in SP1Clean (compose Layer 1 + readers, ~30–50 lines)
        ↑ wrapped by
Layer 3 — FormalAssertion.soundness/completeness in SP1Clean (~15–25 lines)
```

The discipline: **Layer 0 is never duplicated.** Layers 1–3 are pure plumbing. The whole stack ensures every Clean `FormalAssertion` is backed by an SP1 `_poly` lemma that was proved exactly once.

The `_poly` migration was driven by Fin-KB → ZMod-polymorphism. Side effect: every `_poly` Spec is stated over a generic field (the `Field F` instance). Clean's `Expression.eval` evaluates in `ZMod p`. **No `BitVec`-to-`ZMod` conversion needed at the bridge layer.** Pure win — the field-genericism effort and the Clean pilot reinforce each other.

### Friction the bridge layer must guard against

1. **`↑↑` cast residue.** When an SP1 `_poly` RHS contains `(n : F p)` round-trips for byte literals, `Expression.eval` may produce `((n : ZMod p).val : ZMod p)` echoes in the goal. Cheap fix: `Fin.val_cast_of_lt` after bounding the literal. See `byte_decomp_128` in `SP1Foundations/Word.lean`.
2. **`simp_all` leakage.** Repo-wide hazard (commit `419ee1d`). Prefer targeted `simp [...] at h` over `simp_all` in any Layer-2/Layer-3 proof.
3. **`circuit_proof_start` `id`-wrap.** After `circuit_proof_start`, the goal/hypotheses are wrapped in an `id` that breaks `linear_combination` and `mul_eq_zero.mpr`. Fix: `unfold id at *` once.
4. **`Vector.map` over `.push`.** `Vector.map (Expression.eval env) (v.push 0)` doesn't auto-reduce to `(input_v).push 0`. Cheap fix: `simp only [Vector.map_push, h_pc] at h_sub`.
5. **`sub_eq_add_neg` normalization mismatch.** `circuit_proof_start` normalizes the goal but not the hypotheses. Bridge with `simp only [sub_eq_add_neg] at h_spec` after destructuring.

## Canonical ALU-chip Layer-0/Layer-2 shape (post-AddChip refactor)

`SP1Chips/Add/Common.lean` is the reference template for chip-level `allHold_constraints_iff` lemmas going forward. Two structural choices matter:

1. **State both sides of the iff in `.allHold` form**, not `List.Forall SP1Constraint.toProp`. The two are reducibly equal, but `rw` doesn't unfold reducibles during pattern matching — keeping `.allHold` form lets downstream operation/reader `iff_sp1` lemmas fire directly without an inline form-bridge.

2. **The matching SP1Clean Layer-2 `allHold_iff_structural` collapses to a flat rewrite chain.** No `show … from by simp [constraints, …]` block, no manual constraint re-derivation, no inline `List.Forall ↔ .allHold` bridge. Every ALU chip's Layer-2 proof should look this clean.

Existing chip Common.lean files (Sub, Addi, Addw, Subw, Mul, Bitwise, Branch, DivRem, Jal, Jalr, Lt, ShiftLeft, ShiftRight) still use the older form. Migrate opportunistically — when touching a chip's Common.lean for another reason — rather than as a flag-day sweep. **New ALU chip Commons should start in the canonical shape.**

Two caveats observed during the AddChip migration:
- **Trailing `assertZero` clauses can need `(0 : ZMod p)` / `(1 : ZMod p)` ascriptions** on bare literals — Lean's left-to-right literal elaboration otherwise picks `ℕ` and breaks the `simp only` close.
- **The `simp only` close can leave `↑48` / `↑1` cast residue** when a reader op-arg expression mixes `Main[k] * 48 + (1 - Main[k]) * 49` patterns. Append `push_cast; rfl` after the `simp only`.

## Open design choices

These forks are worth deciding before tackling Step 4:

- **§3b's placeholder vs. true-`next_pc`.** Keep the placeholder + add a trace-shape hypothesis on PC low-limb bounds (cheap, narrow), or replace per-chip with a proper carry-aware `next_pc` projection (correct in general, more proof bookkeeping). The placeholder is what shipped today.
- **Step 4's port vs. bridge strategy.** Re-proving 24 `correct_*` on the Clean side duplicates work but gives a clean architecture. Bridging via `Spec_iff_allHold` reuses the existing proofs but conflates the Clean DSL with the dirty `SP1Constraint` shape forever. Bridge is faster; port is cleaner.
- **Step 5's "padding row" semantics.** What does `Sail.execute_trace` produce on padding rows where `is_real = 0`? Three options: (a) skip and don't advance the Sail state; (b) require padding rows to also be valid Sail steps (e.g., a NOP with PC preserved); (c) error. Choice (a) is what the dirty `correct_*` theorems effectively assume; (b) is what real SP1 traces look like; (c) is overly restrictive.
- **Trace completeness scope.** Whether to ship trace-level completeness in the first pass or punt it. The soundness side is the "verifier accepts → there's a Sail run" direction that matters for proving the verifier doesn't accept garbage. Completeness is "every Sail run can be encoded" — important for liveness but not for soundness.

## Open risks

- **Upstream Clean fork health.** The pilot tracks `../clean` on a local branch (`sp1-pilot-misc-dedup`) carrying a one-line dedup patch in `Clean/Utils/Misc.lean`. If upstream's bump-lean-4.29 branch stalls, who maintains the patch long-term? **Mitigation:** pin a specific commit in `lakefile.toml` once upstream stabilizes, or fork permanently under the SP1 org.
- **Constraint-compiler drift.** Every `update_constraints.py` run risks silent SP1Clean breakage. **Mitigation:** add a CI step running `lake build SP1Clean` after constraint regen, gating the PR template on a green SP1Clean build. ~5 lines of CI YAML; pays for itself the first time it catches a drift.
- **Heartbeat budget creep.** Phases B5/B6 (Shifts, Mul) likely need per-file `maxHeartbeats 10000000+`. The precedent in the existing `lakefile.toml` (`synthInstance.maxHeartbeats = 1000000`) shows the repo tolerates this. Document budgets in each file's docstring.
- **Multiplicity tracking.** SP1 sends carry an `AirInteraction.mult`; the Clean lookup encoding has no multiplicity (or rather, the pilot drops `mult` under the chip-level `is_real = 1` premise). Holds today because every constraint has a corresponding `mult ≠ 0 → P` guard discharged by `is_real`. If a future chip introduces *fractional* multiplicities (e.g., per-byte counters), the encoding will need extension. None of the 24 currently-mirrored chips needs this. See `MULTIPLICITY_BUS.md` for the parallel hint-witness `lookupGated` primitive that closes part of this gap.

## What happens to SP1Chips after Phase D

SP1Chips's `correct_*` proves **Sail equivalence**, which Clean doesn't directly model. SP1Chips stays as the **Sail bridge layer**: it takes input from either the original SP1 constraints function or a Clean-derived one (D2 makes them identical-by-CI). The `spec_<op> / sp1_<op> / correct_<op>` triad is independent of which constraint definition Layer-2 imports.

## Durable lessons from prior iterations

Distilled from iter-1 through iter-8 retrospectives. The blow-by-blow line counts and build metrics are in git history; what survives here is the lessons that still inform future work.

**Iter-1 / iter-2 — initial spike and heavy-chip scaling.** First three operations mirrored (Add, Sub, Bitwise); the Misc.lean dedup story with upstream Clean was resolved by a `sp1-pilot-misc-dedup` branch carrying one line of patch. Three risks were probed and resolved on small-to-medium chips: (1) per-chip boilerplate scaling — settled at ~75–115 LoC once the recipe stabilized; (2) Clean interaction representation — stateless lookups (byte/state/program) suffice for per-chip soundness under `is_real = 1`, with memory aggregated trace-level; (3) FormalAssertion promotion via Path-2 (drops bare byte lookups + Vector-indexed assertZero gates) is the workhorse pattern for heavy chips.

**Iter-3 — full mirror landed.** All 25 chips mirrored. The Spec-only tier (`Spec := True` placeholder) was adopted for chips whose underlying operations weren't mirrored yet. JTypeReader added. This was the "every SP1 instruction has a parallel SP1Clean file" milestone.

**Iter-4 — Path-2 recipe solidified.** Seven chips promoted to FormalAssertion. The Path-2 recipe (drop bare byte lookups + Vector-indexed assertZero gates from `Assertion.main`; keep them in the legacy `Spec`) handled the chips where Path-1 hit `Expression.eval env input_var_<vec>[k]` unification friction. Identified the Tier-2 gating need (JalrChip, LtChip, BranchChip — operations multiplied by a per-row selector).

**Iter-5 — Phase-A gating combinator probe.** First `GatedAddOp.assertion` landed, closing the iter-4 Tier-2 finding for AddOp-style operations. JalrChip Path-1.5 partial re-promotion demonstrated the approach end-to-end. Still pending: a polymorphic `Gated.assertion` combinator (lookup-restriction caveat blocks the polymorphic form).

**Iter-6 — Load/Store sweep.** Seven Load/Store chips promoted via Path-2; the iff_sp1-only tier emptied. Confirmed that the `OperandAccess` pattern is the right abstraction for register-side memory operands.

**Iter-7 — heavy-op closure.** Five heavy chips (Branch, DivRem, Mul, ShiftLeft, ShiftRight) reached 24/24 FormalAssertion coverage by Path-2 promotion against their `main`'s surface gates. Operation-specific arithmetic (shift carry chain, MulOperation, DivRem quotient/remainder, branch compare) stays in legacy `Spec` and is consumed via the chip pipeline rather than the FormalAssertion. ShiftLeft drops 10 Vector-indexed gates for the indexed-access reason; ShiftRight follows the same pattern.

**Iter-8 — faithful table-interaction representation.** Four phases closed the gap between SP1Clean's table-interaction encoding and the SP1 Rust source-of-truth. Phase 1: `OperandAccess` sweep across 24/24 register-side; every chip's `Assertion.main` now emits `SP1Clean.OperandAccess.assertion` per register operand. Phase 2: `ChipRow.Spec` flipped from legacy `<Chip>.Spec` to `<Chip>.assertion.Spec` across all 23 arms via `change + unfold + tauto`. Phase 3: multiplicity gating + padding-aware aggregator (`Memory_send_iff_isU64` lemma; `aggregateMemoryAccessesFiltered` side-by-side with the unfiltered aggregator). Phase 4: boundary chips (`MemoryGlobalChip` + `TraceStateBoundary` + `trace_soundness_with_boundary` theorem).

## Iter-8 deferred follow-ups

These are the small follow-ups iter-8 left open:

- **Phase 3.5** — switch the trace-soundness pipeline from `aggregateMemoryAccesses` to `aggregateMemoryAccessesFiltered`. Requires re-discharging the timestamp-sorted/nodup properties for the filtered list.
- **Phase 4.5** — boundary chips' `memoryAccesses` remain empty; full bus closure requires bridging `MemoryGlobalCols` to the `MemoryAccess` record shape. Same structural mismatch as Load/Store's RAM access (the chip's `(diff_low, diff_high)` flag-gated timestamp encoding doesn't fit `OperandAccess.Spec`'s scaled-timestamp form). A new `LoadOperandAccess` / `BoundaryOperandAccess` variant covering both shapes would unify them.
