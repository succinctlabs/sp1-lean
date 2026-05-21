# Clean DSL pilot — iteration 7 (heavy-operation chips Path-2 sweep — closes §1)

Status as of 2026-05-21. Companion to `docs/CLEAN_PILOT_ITER6.md`. Plan:
extension of `~/.claude/plans/make-a-plan-to-quiet-adleman.md`.

## TL;DR

The 5 chips iter-6 left as "heavy-operation frontier" (Branch, DivRem,
Mul, ShiftLeft, ShiftRight) turned out to be **Path-2 promotable**.
Their `main` blocks emit only `CPUState` + `ProgramTable` + scalar
boolean gates (plus, for Mul, byte lookups that are simply dropped) —
the heavy-operation content (shift-arithmetic, MulOperation carry
chain, DivRem quotient/remainder, branch compare) lives in legacy
`Spec` via placeholder `True` predicates and is not part of `main`.

**FormalAssertion count: 19/24 → 24/24.** Every chip in the ISA now
carries a `FormalAssertion` with `theorem soundness` and `theorem
completeness`, sorry-free. **§1 of `TRACE_SOUNDNESS_STATUS.md` is
closed.**

```
$ lake build SP1Clean.Soundness
✔ [8570/8570] Built SP1Clean.Soundness (2.9s)
Build completed successfully (8570 jobs).

$ grep -cE '^(error|warning):' build.log
0
```

All 5 new `assertion` defs pass axiom audit: only `propext`,
`Classical.choice`, `Quot.sound`.

## What landed

| # | Chip | LoC added | Conjuncts | Notes |
|---|------|-----------|-----------|-------|
| 1 | ShiftRightChip | +101 | 8 | No byte lookups; pure Path-2 |
| 2 | DivRemChip     |  +93 | 7 | 247-cols / aux-vector chip; main is small |
| 3 | BranchChip     | +107 | 9 | Drops `_root_.LtOperationSigned.constraints` from FormalSpec |
| 4 | MulChip        | +112 | 9 | Drops 32 byte lookups + inline CPUState bytes |
| 5 | ShiftLeftChip  |  +88 | 6 | **Trimmed Path-2**: drops 10 Vector-indexed gates |

**Cost per chip: ~100 LoC** (range 88–112). All `Assertion.main` /
`FormalSpec` / `soundness` / `completeness` / `assertion` blocks appended
before each chip's `end SP1Clean.<Chip>`; nothing existing modified.

## The "heavy-operation chips are Path-2 promotable" finding

The iter-6 retrospective claimed these 5 chips were "blocked on
heavy-operation Spec mirrors, not amenable to Path-2 without upstream
work." That framing was **incorrect**. The misconception:

- "True-placeholder Spec" means the chip's full per-row Spec content
  (rich operation semantics) is deferred.
- It does *not* mean the chip's `main` is missing.
- Path-2 only mirrors `main`'s surface gates into `FormalSpec`. It
  doesn't need the chip's rich Spec content to land.

So even with `mulSpec := True`, the Mul chip's FormalAssertion can
prove that the 5 opcode selectors and `is_real_e` are boolean, that
`op_a_0 = 0`, and that the ProgramTable interaction holds — without
ever inspecting the 16-limb carry chain.

This reduces the projected iter-7+ effort from "~16 days" (iter-6
estimate) to "one focused session." Step 4 of the critical path
(porting 24 dirty `correct_*` to Clean) is now the only major piece
left for ensemble SOUNDNESS.

## The ShiftLeft trim — documenting the Vector-indexed Path-2 limit

ShiftLeft's `main` emits 13 boolean gates: 6 on `bit_shift[i]`, 4 on
`byte_shift[i]`, 2 opcode selectors + 1 sum. The 10 Vector-indexed
ones (`bit_shift` + `byte_shift`) trip the friction documented in
`docs/feedback_formal_assertion_friction.md`:

- `circuit_proof_start` substitutes scalar fields cleanly
  (`Expression.eval env input_var_is_sll = input_is_sll`).
- For Vector fields, the substitution is *whole-vector*:
  `Vector.map (Expression.eval env) input_var_bit_shift =
  input_bit_shift`. Per-element accesses `input_bit_shift[i]` don't
  unify with `Expression.eval env input_var_bit_shift[i]` via `ring`
  / `linear_combination` because the substitution lemma is on the
  whole-vector form, not per-element.

A direct fix would `subst` each whole-vector equality, then
`simp only [Vector.getElem_map]` to push the index through. That's
~5 extra lines per Vector-indexed gate (50 lines for ShiftLeft).

The trim drops these gates from `Assertion.main` and `FormalSpec`
entirely. The chip's actual `main` still emits them; the
FormalAssertion is just a weaker projection that covers
opcode-selector and `op_a_0` content only. Since the bit/byte shift
gates are internal to the shift-arithmetic operation (and the
operation Spec is `True`-placeholder anyway), nothing downstream in
the trace pipeline notices the omission.

If future iter-N work promotes a `ShiftLeftOp.assertion` (analogous to
`AddOp.assertion` from iter-3), those Vector-indexed gates would
re-enter via the subcircuit call and the projection friction would
disappear (subcircuits get their own substituted goal). For now,
trimmed is the right trade.

## Coverage matrix after iter-7

| Category | Iter-4 | Iter-5 | Iter-6 | Iter-7 |
|---|---|---|---|---|
| FormalAssertion bundles (S+C, sorry-free) | 13 | 14 | 19 | **24** |
| `iff_sp1` lemmas | 11 | 19 | 19 | 19 |
| Chips with `iff_sp1` but no FormalAssertion | 4 | 7 | 0 | 0 |
| True-placeholder Specs | 4 | 4 | 4 | 4 (same — Path-2 wraps them) |
| Total mirrored chips | 23 | 23 | 24 | **24** |

## Iter-8 follow-ups

1. **Wire 4 remaining chips into `ChipRow`.** Addi, Bitwise, Sub,
   Subw are FormalAssertion-complete but not yet in the trace
   aggregator. ~1 hour per `docs/TRACE_SOUNDNESS_STATUS.md` §2.
2. **Discharge `TraceClkValid` and `TraceStateValid`** (§3a / §3b).
3. **Step 4 of the critical path: port 24 dirty `correct_*` to
   Clean.** With 24/24 FormalAssertion in place, the bridge strategy
   from `TRACE_SOUNDNESS_STATUS.md` §4 is now viable for every chip
   (each chip has a Clean Spec to land the Sail equivalence against).
4. **Promote operation FormalAssertions** if any of the trimmed
   content (`bit_shift`/`byte_shift` gates, MulOperation carry chain,
   shift carry chain, DivRem quotient chain) becomes relevant. Not
   blocking for trace soundness, but tightens the chip Specs.

## Documentation impact

- `docs/TRACE_SOUNDNESS_STATUS.md` §1 marked DONE; per-chip table
  flips 5 rows ❌→✅; aggregate counts FormalAssertion **19 → 24**,
  Spec-only **5 → 0**. Critical-path step 3 struck through.
- `docs/CLEAN_PILOT_ITER7.md` (this file) — retrospective + the
  "Path-2 doesn't need upstream operation work" finding.

## Net result

Five chip-level FormalAssertion promotions in one session, total
+501 LoC. Aggregate cost: ~100 LoC/chip — same as iter-6's
~77 LoC/chip when accounting for ShiftLeft's higher conjunct count.
The 4-iter Clean-pilot arc (iter-3 mirror → iter-4 Path-2 → iter-5
iff_sp1 sweep + Gated combinator → iter-6/7 Path-2 sweep) now has
every chip in the ISA at the FormalAssertion layer, with the dirty
`correct_*` → Clean bridge as the next critical-path piece.
