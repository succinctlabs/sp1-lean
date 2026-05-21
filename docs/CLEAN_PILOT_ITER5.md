# Clean DSL pilot — iteration 5 (iff_sp1 sweep + Phase-A gating combinator)

Status as of 2026-05-21. Companion to `docs/CLEAN_PILOT_ITER4.md`. Plan:
`~/.claude/plans/make-a-plan-to-proud-ember.md`. Roadmap:
`docs/CLEAN_PILOT_ROADMAP.md` (§2 Layer-A + §3 Phase-A).

## TL;DR

Two things landed:

1. **`iff_sp1` coverage swept from 11 → 19 of 23 mirrored chips.** Eight
   chips (LoadByte / LoadHalf / LoadWord / LoadDouble + StoreByte /
   StoreHalf / StoreWord / StoreDouble + UTypeChip) gained chip-level
   `iff_sp1_of_*` lemmas, all proven, no `sorry`. Two new SP1Clean
   helpers (`AddrAddOp` Spec, `ITypeReaderImmutable` Spec) and four new
   SP1-side bridges (`SP1Chips/Store/*/Common.lean`) ship to back them.
2. **First Phase-A gating combinator concrete instance.**
   `SP1Clean.GatedAddOp.assertion` is a hand-written `FormalAssertion`
   that gates the 4 carry-boolean asserts of `AddOp` by a scalar
   `gate : F`, **dropping the lookup-derived range checks** (which
   cannot be soundly gated by field multiplication). `JalrChip`'s
   `is_real`-gated jump-target sum is the first chip-level use site,
   partially closing the iter-4 Tier-2 probe finding.

`lake build SP1Clean` stays at **0 errors / 0 warnings / 0 sorries**
end-to-end (8568 jobs, ~5 min from clean cache). FormalAssertion count
grew from 13 → 14; SP1Clean LoC grew from ~7059 to ~9460 (+~2400, of
which ~250 is bridge code in SP1Chips/).

## What landed (WIP-A: §2 Layer-A iff_sp1 sweep)

| # | Chip | LoC added | Notes |
|---|------|-----------|-------|
| 1 | LoadByteChip   | +196 | `iff_sp1_of_is_lb`, `iff_sp1_of_is_lbu` + 2 SpecForIff defs |
| 2 | LoadHalfChip   | +166 | `iff_sp1_of_is_lh`, `iff_sp1_of_is_lhu` + 2 SpecForIff defs |
| 3 | LoadWordChip   | +153 | `iff_sp1_of_is_lw`, `iff_sp1_of_is_lwu` + 2 SpecForIff defs |
| 4 | LoadDoubleChip |  +79 | `iff_sp1_of_is_ld` + 1 SpecForIff (no signed/unsigned variants) |
| 5 | StoreByteChip  | +118 | `iff_sp1_of_is_real` + SpecForIff. Iter-4 FormalAssertion bundle preserved |
| 6 | StoreHalfChip  |  +95 | `iff_sp1_of_is_real` + SpecForIff |
| 7 | StoreWordChip  |  +95 | `iff_sp1_of_is_real` + SpecForIff |
| 8 | StoreDoubleChip|  +77 | `iff_sp1_of_is_real` + SpecForIff |
| 9 | UTypeChip      |  +69 | `iff_sp1` (single, covers `auipc`/`lui` under `is_real`) |

**Cost per chip: ~106 LoC** (range 69–196), dominated by the destructured
`SpecForIff` defs (12–80 lines each, mirroring the SP1-side
`allHold_constraints_iff_*` RHS verbatim) plus the iff_sp1 theorem
itself (~10–15 lines: rewrite via the SP1 helper, then via the matching
Clean `_iff_sp1` helpers for CPUState / I-type reader / AddrAddOp).

### New helpers backing the sweep

- **`SP1Clean/AddrAddOperation.lean`** (59 LoC). `SP1Clean.AddrAddOp.Spec`
  packages `_root_.AddrAddOperation.allHold_constraints_iff`'s RHS as a
  named predicate; `iff_sp1` is a one-line re-export. Used by all 4 Load
  + 3 Store chips. **Spec + iff_sp1 only — no FormalAssertion bundle**
  (operation-level promotion deferred per roadmap Phase-B).
- **`SP1Clean/Reader/ITypeReaderImmutable.lean`** (72 LoC). Sibling of
  `SP1Clean.ITypeReader.itypeReaderSpec`, with no `op_a_write_value`
  parameter (Store chips read op_a as the source data; the
  `op_a_0 = 1 → prev_value = 0` trailer replaces the write-value
  constraint). Used by all 4 Store chips.
- **`SP1Chips/Store/{StoreByte,StoreHalf,StoreWord,StoreDouble}/Common.lean`**
  (251 LoC total). Each file exposes `Store.<Width>.allHold_constraints_iff_of_is_real`
  — the SP1-side propositional unfolding of the chip's constraint list
  under `is_real = 1`. Powers the matching `iff_sp1_of_is_real` lemmas
  on the Clean side.

### Memory-consistency aggregator update

`SP1Clean/Soundness/MemoryConsistency.lean:363, 449` corrected the
`op_a_write_value` for the LoadWord and LoadHalf `ChipRow` constructors
to include sign-extension limbs derived from `signed_extension_msb`:

```lean
-- LoadWord: op_a_write_value = [lo[0], lo[1], 65535 * msb, 65535 * msb]
-- LoadHalf: op_a_write_value = [lo,    65535 * msb, 65535 * msb, 65535 * msb]
```

Previously these limbs were `cols.op_a_write_value` (a placeholder
field). The fix doesn't add `iff_sp1` coverage on its own but unblocks
the future trace-level OfflineMemory bridge — the aggregator now
projects the correct 64-bit word from a sign-extended 16/32-bit load.

### Coverage matrix after WIP-A

| Category | Iter-4 | Iter-5 |
|---|---|---|
| FormalAssertion bundles | 13 | 14 (+JalrChip Path-1.5; see Phase-A below) |
| `iff_sp1` lemmas | 11 | **19** |
| True-placeholder Specs | 4 | 4 (Mul / ShiftLeft / ShiftRight / DivRem) |
| Total mirrored chips | 23 | 23 |

After this round, **the only mirrored chips without `iff_sp1` are the
four True-placeholder ones whose Specs are stubbed at `True`** (they're
blocked on heavy operation promotion per roadmap Phase-B).

## What landed (Phase-A: gating combinator)

### Design: the lookup-restriction caveat

The intuitive design — a polymorphic `Gated.assertion : Expression →
FormalAssertion α → FormalAssertion (Gated α)` that lifts an arbitrary
inner FormalAssertion into a gated one by multiplying each emitted
`assertZero e` by the gate — **fails on two architectural grounds**:

1. **Lookups can't be gated by field multiplication.** Many inner
   operations (e.g. `AddOp.assertion`) emit `Range(16)` lookups on their
   result limbs. A lookup is table membership, not a polynomial
   equation: `lookup t v` is **not** the same as `lookup t (gate * v)`.
   On a padding row where `gate = 0`, we want the lookup to be
   **vacuous** (multiplicity 0), not to fire with the value 0. Clean's
   lookup encoding has no per-row multiplicity field, so there's no
   shape-preserving rewrite from "ungated lookup" to "gated lookup."
2. **`Circuit` operations aren't traversable from a higher-order def.**
   Even ignoring (1), implementing the lift would require inspecting
   `sub.main`'s emitted operations and rewriting each `.assert e` into
   `.assert (gate * e)`. The `Circuit` monad exposes operations only
   through `do`-block scope, not as a first-class structure
   transformable from outside.

**Resolution:** ship the lookup-restriction caveat as a **documented
pattern**, not a polymorphic combinator. Per inner operation needing a
gated form, hand-write a new `FormalAssertion` whose:
- inputs bundle the inner inputs plus a `gate : F` field,
- `main` emits only the **assertZero half** of the inner's
  constraints, each multiplied by `gate` (lookups are **dropped**),
- `Spec` is `gate = 0 ∨ <carry-only inner.Spec>` (no range bounds),
- soundness uses `mul_eq_zero` (valid in a field),
- completeness case-splits on `Spec`.

The dropped lookups remain in the consuming chip's **legacy chip-level
`Spec`** (carried by `iff_sp1` or trace-level aggregation). On padding
rows where the gate evaluates to 0, those legacy lookup multiplicities
are 0 anyway, matching SP1's gating semantics.

### Files

- **`SP1Clean/Gated.lean`** (87 LoC). Module docstring documenting the
  caveat + pattern. No polymorphic definition.
- **`SP1Clean/GatedAddOp.lean`** (171 LoC). First concrete instance.
  `Inputs ⟨a, b, result, gate⟩`. `main` emits four `gate * (c_k *
  (c_k - 1)) === 0` carry asserts (no lookups). `Spec` is `gate = 0 ∨
  GatedAddOp.Spec a b result`. Soundness ~30 lines via per-carry
  `mul_eq_zero` case-split; completeness ~20 lines via `rcases` +
  `dsimp only at h_gate` to reduce the record projection introduced by
  `circuit_proof_start`'s `input` substitution.

### JalrChip Path-1.5 promotion

`SP1Clean/JalrChip.lean` was the iter-4 Tier-2 probe — two raw
`(AddOperation.constraints ...).allHold` clauses in its `Spec`, gated
on `is_real` and `is_real - op_a_0` respectively, neither of which
could be promoted by iter-4's Path-2 approach.

**Iter-5 promotes one of the two** — the simpler `is_real`-gated
jump-target sum:

```
-- Before (Path-2): clause dropped from Assertion.main; lived in legacy Spec
-- After (Path-1.5):
SP1Clean.GatedAddOp.assertion
  (⟨op_b_memory_prev_value, op_c_imm, jump_target, is_real⟩ :
    Var SP1Clean.GatedAddOp.Inputs (ZMod p))
```

`FormalSpec` gains a new disjunctive clause:

```
(cols.is_real = 0 ∨ SP1Clean.GatedAddOp.Spec
  cols.op_b_memory_prev_value cols.op_c_imm cols.jump_target)
```

Soundness/completeness extend by one component (one `h_gated_sub trivial`
in soundness, one `⟨trivial, h_gated⟩` in completeness). The second
AddOp (`is_real - op_a_0`) **remains in Path-2 drop form** — it needs a
multi-factor gate (two boolean selectors combined into a difference),
which is iter-6 work.

JalrChip net delta: **+48/−23 LoC** including the rewritten module
docstring describing the partial Tier-2 close.

## Iter-6 follow-ups

1. **Second JalrChip clause (`is_real - op_a_0`).** Needs either a
   `GatedAddOp2.assertion` with a 2-factor gate `(g1, g2)` whose `main`
   emits `(g1 - g2) * carry_k * (carry_k - 1) === 0`, or a more general
   linear-combination gate. Roughly 100–150 LoC.
2. **LtChip / BranchChip via `GatedLtOperationSigned`.** Requires the
   Clean-side `LtOperationSigned.assertion` operation first (Phase-B
   step 1, ~150 LoC), then a `GatedLtOperationSigned.assertion` mirror
   of the gated AddOp pattern (~180 LoC). Together unblocks Lt (1
   gate) and Branch (6 per-opcode gates) — at this point the gating
   pattern is generic enough to consider extracting into a parameterized
   combinator.
3. **CI drift gate.** Still missing. The roadmap's recommended ~5 lines
   of CI YAML would catch silent constraint-compiler regen breakages.
   Independent of Phase-A; can land at any time.
4. **AddrAddOperation FormalAssertion.** With 10 chips already
   consuming `AddrAddOp.Spec`, promoting it to a full FormalAssertion
   would unlock Path-1 Load/Store re-promotion (the chip
   `Assertion.main` would invoke `AddrAddOp.assertion` as a
   subcircuit). ~150 LoC modeled on `AddOperation.assertion`.

## Scaling-difficulty answers

The plan asked: how hard is the iff_sp1 sweep vs. the Phase-A combinator?

- **iff_sp1 sweep: ~106 LoC/chip**, well under the iter-4 FormalAssertion
  cost of ~93 LoC/chip in raw budget but with much higher mechanical
  density (each chip's SpecForIff faithfully mirrors the SP1 helper's
  RHS, 30–80 lines). Total ~1050 LoC across 8 chips. Per-chip time:
  ~15–30 min once the template was set.
- **Phase-A combinator: ~260 LoC total** (Gated.lean docs + GatedAddOp
  +48 LoC of JalrChip integration). Roughly two thirds of the time
  spent on understanding `circuit_proof_start`'s `h_input` shape and
  the projection issue resolved by `dsimp only at h_gate`. The actual
  arithmetic in soundness/completeness is straightforward
  (`mul_eq_zero.mp` + 4 linear_combinations).

The Phase-A combinator is **cheaper than expected** (~260 LoC vs the
plan's ~510 LoC estimate). The savings came from scoping `Gated.lean`
as a docs-only file rather than attempting a polymorphic lift.

## Net result

```
$ lake build SP1Clean
✔ [8567/8568] Built SP1Clean (5.4s)
Build completed successfully (8568 jobs).

$ grep -cE '^(error|warning):' build.log
0
```

Eight new chip-level `iff_sp1` lemmas, the first Phase-A gating
combinator concrete instance, one chip partially re-promoted past
the iter-4 Tier-2 blocker. Coverage: 19 of 23 mirrored chips now carry
an `iff_sp1`; the four remaining are blocked on heavy-operation
promotion. Zero regressions.
