# Clean DSL pilot — iteration 6 (Path-2 FormalAssertion sweep for Load/Store chips)

Status as of 2026-05-21. Companion to `docs/CLEAN_PILOT_ITER5.md`. Plan:
`~/.claude/plans/make-a-plan-to-quiet-adleman.md`. Status report:
`docs/TRACE_SOUNDNESS_STATUS.md` §1.

## TL;DR

The iff_sp1-bridge tier created in iter-5 is now empty: every chip that
gained an `iff_sp1` lemma in iter-5 (the four Load* variants + the
three Store* siblings of StoreByte, minus StoreByte itself which was
already promoted) now also carries a full `FormalAssertion` with
`theorem soundness` and `theorem completeness`. **Seven Path-2
promotions landed**, lifting Clean `FormalAssertion` coverage from
12/24 to **19/24**.

```
$ lake build SP1Clean.Soundness
✔ [8570/8570] Built SP1Clean.Soundness (2.9s)
Build completed successfully (8570 jobs).

$ grep -cE '^(error|warning):' build.log
0
```

Each promoted `assertion` passes axiom audit cleanly: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`.

## What landed

| # | Chip | LoC added | Conjuncts | Notes |
|---|------|-----------|-----------|-------|
| 1 | StoreDoubleChip | +71 | 3 | Simplest Store (single is_real, no sub-word selector) |
| 2 | StoreWordChip   | +71 | 3 | Adds `_word_offset_flag` to destructure |
| 3 | StoreHalfChip   | +72 | 3 | Adds `_byte_selector_{upper,lower}` to destructure |
| 4 | LoadDoubleChip  | +71 | 3 | Sibling of StoreDouble; opcode 35 |
| 5 | LoadWordChip    | +83 | 5 | First two-selector Load (`is_lw` / `is_lwu` + sum) |
| 6 | LoadHalfChip    | +83 | 5 | Relabel of LoadWord (`lh` / `lhu`, opcodes 30/33) |
| 7 | LoadByteChip    | +90 | 6 | Adds `op_a_0 === 0` gate (final and most complex) |

**Cost per chip: ~77 LoC** (range 71–90). Pure append: no existing code
in any of the seven files was modified — each promotion is a
namespace `Assertion` block plus a 5-line `def assertion : FormalAssertion`
inserted before `end SP1Clean.<Chip>`. The legacy chip-level `Spec`,
`fromMain`, and `iff_sp1_*` lemmas survive unchanged for use by the
trace-level OfflineMemory bridge and the SP1-side `correct_*` theorems.

## The Path-2 recipe (re-applied)

`Assertion.main` keeps only the subcircuit-and-scalar-gate surface:

- `SP1Clean.CPUState.assertion` (was inline byte lookups in
  LoadByte's pre-iter-6 `main` — converted to the subcircuit call,
  matching the StoreByte template),
- `SP1Clean.ProgramTable.assertion` (selector-weighted opcode for the
  multi-variant Loads: `is_lw * 31 + is_lwu * 34` etc.),
- N scalar boolean gates: one per opcode selector + one for the sum
  (Loads with two selectors) + `op_a_0 === 0` (LoadByte only).

Dropped from `Assertion.main` (still present in legacy `main` for
OfflineMemory):

- `load_memory_diff_{low,high}` byte lookups (× 2 per chip),
- For LoadByte: `selected_byte_alt` U8 range + MSB lookup for
  sign-extension,
- For StoreByte (already promoted in iter-4, included here for
  completeness): `result_byte` U8 range + `selected_byte_alt` range.

`FormalSpec` mirrors `Assertion.main` clause-for-clause:

```lean
def FormalSpec (cols : LoadWordCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := cols.is_lw * 31 + cols.is_lwu * 34,
      op_a := cols.op_a, op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  (cols.is_lw + cols.is_lwu) * (cols.is_lw + cols.is_lwu - 1) = 0
```

Soundness and completeness each close in ~10 lines via the standard
template (`circuit_proof_start` → `obtain ⟨…⟩` → `unfold id at *` →
`refine ⟨?_, …⟩` → `exact h_sub trivial` / `linear_combination h_bool`).
The destructure shape exactly matches the conjunct count.

## Coverage matrix after iter-6

| Category | Iter-4 | Iter-5 | Iter-6 |
|---|---|---|---|
| FormalAssertion bundles (S+C, sorry-free) | 13 | 14 | **19** |
| `iff_sp1` lemmas | 11 | 19 | 19 (unchanged) |
| Chips with `iff_sp1` but no FormalAssertion | 4 | 7 | **0** |
| True-placeholder Specs | 4 | 4 | 4 |
| Total mirrored chips | 23 | 23 | 23 |

(Lt + UType were also promoted earlier today via Path-2 — the same
recipe — and are reflected in `TRACE_SOUNDNESS_STATUS.md`'s updated
counts.)

The five remaining Spec-only chips — Branch, DivRem, Mul, ShiftLeft,
ShiftRight — are the ones that **never gained an `iff_sp1` bridge**
because their underlying operations (LtOperationSigned, MulOperation,
ShiftLeft/Right primitives, DivRem's recursive quotient chain) lack
Clean-side Spec mirrors. The Path-2 recipe used here does not transfer
to those chips without first promoting the inner operations.

## Iter-7 follow-ups

1. **Branch family promotion.** Blocked on a Clean-side
   `LtOperationSigned.assertion` (roughly the same shape as
   `GatedAddOp`). Once that lands, Branch's six per-opcode variants
   can be wrapped in a generalized `GatedLtOperationSigned` mirror —
   see iter-5 follow-up §2.
2. **Mul / ShiftLeft / ShiftRight promotion.** Each requires its
   underlying operation's `FormalAssertion`. MulOperation's 60+
   conjunct expansion is the headline cost (see iter-5 perf notes);
   the shift carry chain needs per-shift-amount case analysis.
3. **DivRem promotion.** Mechanical given the existing `Common.lean`
   helper architecture, but elaboration-heavy (247-element Main vector,
   17–40 min cold build).
4. **Re-promote LoadByte's CPUState-bytes section via the subcircuit.**
   The pre-iter-6 `main` of LoadByteChip used the inline two-byte
   lookups for the CPUState clk bounds rather than calling
   `SP1Clean.CPUState.assertion`. The iter-6 `Assertion.main` uses the
   subcircuit form (matching StoreByteChip); whether the legacy `main`
   should be refactored to match is a tidiness call, not a correctness
   one. The `Spec` is unaffected either way.

## Documentation impact

`docs/TRACE_SOUNDNESS_STATUS.md` updated to reflect:
- 9 per-chip table rows flipped `❌ Spec only` → `✅` (the 7 above
  plus Lt + UType catch-up).
- Aggregate counts: FormalAssertion **10 → 19**, Spec-only **14 → 5**.
- §1 narrative trimmed from 14-chip backlog to 5 remaining, with
  the `iff_sp1`-bridge tier called out as now empty.
- Critical-path estimate for §1: **~2 weeks → ~1 week** of focused
  work (DivRem still dominates).

## Net result

Seven chip-level FormalAssertion promotions, each ~77 LoC, all green.
The Clean-pilot wave that started in iter-3 (initial mirror) and ran
through iter-4 (Path-2 introduction) → iter-5 (iff_sp1 sweep) closes
its memory-touching Load/Store arc here. The remaining 5 chips are the
"heavy-operation" frontier, and the next sweep needs subcircuit
promotions for LtOperationSigned, MulOperation, and the shift-carry
chain to unlock them — same pattern as iter-5's `GatedAddOp.assertion`,
applied to one more operation family per follow-up.
