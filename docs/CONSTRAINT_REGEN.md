# Constraint regeneration playbook

When the SP1 constraint compiler changes the column shape of any chip — adds, removes, or reorders columns — the auto-generated body of `<Chip>/Constraints.lean` is rewritten by `update_constraints.py`, but several hand-written sites that reference column indices need a coordinated update too. This doc captures the recipe used for the `is_trusted` removal in PR #92, since that single column drop cascaded across 17 chips and was the single largest source of regressions.

Reuse this playbook for any future column-shape change.

## What `update_constraints.py` does

- Reads `SP1_DIR` from the environment (path to an external SP1 checkout that builds `sp1-constraint-compiler`).
- For each `(chip, operation?, prefix)` entry in `CONSTRAINTS_LIST` at the top of the script, shells out to `cargo run -p sp1-constraint-compiler -- --chip <chip> [--operation <op>] --format lean`.
- Splices the compiler's stdout into the target Lean file *between* the `section constraints` and `end constraints` markers. Everything outside those markers is preserved.
- Output paths: chip-level → `SP1Chips/<prefix>/<chip>/Constraints.lean`, operation-level → `SP1Operations/<prefix>/<operation>/Constraints.lean`.

## What it does NOT touch

These sites all need manual updates after a column-shape change:

1. The `allHold_constraints_iff` lemma in each Reader (RHS conjunct list).
2. The `allHold_constraints_iff_is_real` specialization that fires when `is_real = 1`.
3. `set` aliases in `<Chip>/Constraints.lean` outside the markers (e.g. `set is_real := Main[N-1]`).
4. `def sp1_op_a / sp1_op_b / sp1_op_c` projections in `<Chip>Chip.lean`.
5. `is_real` location: if the last column moved, `h_is_real : Main[N-1] = 1` needs the new index.
6. The `Vector F N` / `Vector (ZMod p) N` width if the total column count changed.
7. Any `by_cases` chains in Reader proofs that case-split on a column you removed (they collapse to fewer cases).

## Prerequisites

- An external SP1 checkout that builds `sp1-constraint-compiler`. Set `SP1_DIR` to the checkout root.
- `cargo` on `PATH`.
- Lean toolchain installed (`lake` resolves `lean-toolchain`).

Run from repo root: `SP1_DIR=/path/to/sp1 python3 update_constraints.py`.

## Recipe for a column drop (canonical: `is_trusted` removal)

1. **Identify the cutoff index.** Find the column's old position before regenerating:
   ```
   git show <pre-removal-commit>^:SP1Chips/Add/Constraints.lean \
     | grep -oE "is_trusted := Main\[[0-9]+\]"
   ```
   Call this `removed_idx`. If multiple columns were removed, you have multiple cutoffs (and the shift is multi-step).

2. **Regenerate.** `SP1_DIR=… python3 update_constraints.py`. This rewrites the auto-generated bodies but leaves index references in hand-written code stale.

3. **Mechanically shift `Main[k]` references** in every hand-written `*/Constraints.lean` and `*Chip.lean`:
   ```python
   import re
   removed_idx = ...   # from step 1
   shift = 1           # 1 column dropped
   text = re.sub(r', is_trusted := Main\[\d+\]', '', text)
   def sub(m):
       k = int(m.group(1))
       return f"Main[{k - shift}]" if k > removed_idx else m.group(0)
   text = re.sub(r"Main\[(\d+)\]", sub, text)
   ```
   For an inserted column, `shift` is negative and the comparison flips to `>= insert_idx`.

4. **Adjust the `Vector F N` / `Vector (ZMod p) N` width** in any signature that mentions it explicitly (chip helpers, theorem statements). `sed -i 's/Vector F <old>/Vector F <new>/g; s/Vector (ZMod p) <old>/Vector (ZMod p) <new>/g'` over the chip's two files.

5. **Update the iff-lemma RHS** in the Reader files (`SP1Operations/Reader/<Reader>.lean`):
   - Remove (or add) the column's conjunct from `allHold_constraints_iff`.
   - Remove (or add) the matching simplification in `allHold_constraints_iff_is_real`.
   - Collapse any `by_cases` branch that case-split on the removed column. ALUTypeReader is the canonical example: a nested `by_cases htrust` flattened to the single remaining branch when `is_trusted` left.

6. **Update `set` aliases** in `<Chip>/Constraints.lean` outside the markers — e.g. if `set is_real := Main[34]` is now `Main[33]`.

7. **Re-check `sp1_op_a/b/c`** in `<Chip>Chip.lean`. These project specific indices; they need the same shift.

8. **Build chip-by-chip** with `lake env lean SP1Chips/<Chip>Chip.lean`. Anything that fails on an out-of-range `Main[k]` or a stale RHS in `allHold_constraints_iff` points to step 5–7 missing an edit.

## Stop-marker fallback (when re-closing 17 chips at once)

If the cascade is too large to re-close one chip at a time, the alternative is a "shift + stop" pattern: shift the indices mechanically and inject `stop` markers at the start of each broken proof so the build stays green while you work down the list.

This was the strategy used during the `is_trusted` cleanup. Pattern:

1. After the index shift, walk each `Constraints.lean` and `<Chip>Chip.lean` line-by-line. For every `theorem correct_*` and every `:= by` in a hand-written lemma, inject `stop` at the indent of the next non-blank line.
2. `stop` alone is not a valid proof terminator — append a `trivial` or leave the original tactics in place (they won't execute past `stop`).
3. If a `def` body uses `by ... stop ...` and only references `Main`/`cstrs`/`h_is_X` after `stop`, Lean won't auto-include them from the `variable` block. Inject `have _ := Main; have _ := cstrs; have _ := h_is_X` before `stop`.
4. For lemmas with `(h : is_<op> Main)` that get stopped early, inject `have _ := h` before `stop` to avoid an unused-variable warning.
5. When most lemmas in a file stop early, prefer `set_option linter.unusedVariables false` at the top of the namespace over scattering `have _ := X` everywhere. Branch / ShiftRight / DivRem / Jal all used this during the cascade.
6. Old Load/Store helpers (e.g. `allHold_constraints_iff_of_is_lb`) sometimes have RHSes that no longer elaborate after the shift. Stubbing them to `↔ True` is fine; chip proofs that call them should `stop` right before the rewrite.

Once all chips compile with stops, work down the list re-closing each `correct_*` proof. The state-of-the-art commit trail to study as a worked example:

- `e686807` — the regen + initial shift (introduces the stops).
- `3322146` / `6de007b` / `1526474` / `af299c9` — successive waves of stop removal as proofs close.
- `f2f5ccd` / `c9a458c` — JAL / JALR closure, which needed the new sail-v4 axioms in addition to the index shift.
- `899d1c3` — final cleanup once nothing was stopped: removes assumptions and axioms whose preconditions never fired anymore.

## Verification

- `grep -rn "stop" SP1Chips/ SP1Operations/` should return zero. (After PR #92, this is the steady state.)
- `grep -rn "sorry" SP1Chips/ SP1Operations/ SP1Foundations/` should also return zero.
- `lake build` finishes with zero `^error:` and zero `^warning:` (`grep -cE '^(error|warning):' build.log`).
- The first chip you re-close end-to-end (typically AddChip — smallest, highest leverage) should look identical in shape to the version of `AddChip.lean` that's currently in HEAD; deviations indicate the shift or iff-lemma update was inconsistent.

## When NOT to use this playbook

- **Don't hand-edit anything inside `section constraints ... end constraints`.** The next regeneration will overwrite it. If the auto-generated block looks wrong, regenerate.
- **Don't apply a `-1` shift to a chip without confirming what the compiler actually output.** PR #92 (and earlier) saw bugs where the iff RHS, set aliases, and constraints def all went out of sync because someone manually shifted indices without re-running `update_constraints.py`. Always regenerate first, shift second.

## Fin-KB deletion-sweep template

Once a chip has a sorry-free `correct_*_poly` companion (see
`FIELD_GENERIC.md`), the parallel `Fin KB` layer is dead weight and
can be dropped. The sweep was executed on 2026-05-15 across every
chip; the recipe below is what generalized cleanly.

### Order: top-down per chip

For each chip, delete in this order so each commit's per-module build
stays clean:

1. Chip-level `<Chip>Chip.lean`: Fin KB `correct_<v>`, `sp1_op_*`,
   top-level `variable (Main : Vector (Fin KB) N)`, prologue helpers
   (`correct_prologue_facts` if it exists).
2. Sail-level `spec_<v>` defs in the chip file: **keep** them. They
   have no field dependence and are referenced by `correct_*_poly`.
3. Per-opcode files (`DivRem/DivRem.lean`, `DivRem/DivuRemu.lean`,
   etc.): bare cores (`div_rem`, `divu_remu`, …) + `spec.<v>` wrappers.
4. Helper file (`<Chip>/Common.lean`): Fin KB sections
   (`field_arithmetic`, `opcodes`, `entailed_constraints`, `operands`)
   + chip-local lemmas like `div_mod_decomposition_w`, `sum_zero_abs`.
5. Constraints file (`<Chip>/Constraints.lean`): hand-written iff
   lemmas (`allHold_constraints_iff`, `allHold_constraints_alu_ops`).
   **Leave the autogen parametric `def constraints` block alone.**
6. Re-check doc comments. Strings like
   `/-- Polymorphic counterpart of `X`. -/` become self-referential
   once `X` is gone; grep `Polymorphic counterpart` after each
   deletion and edit each docstring to drop the lead sentence.

### Inventory caveats

Pre-deletion inventory can wrongly flag field-agnostic lemmas as
"unused Fin KB" because they live in a `Fin KB`-scoped section. Watch
for these specifically:

- If the lemma's signature has `{x : Fin KB}` or
  `{v : Vector (Fin KB) N}` *in the binder list*, it is Fin KB-
  specific. Delete.
- If the signature is in `ℤ` / `ℕ` / `BitVec` and the only Fin KB
  connection is the enclosing `variable` block, it's field-agnostic.
  **Keep** and move it outside the section if needed. Examples caught
  during the DivRem sweep: `tdiv_tmod_unique_full` (pure ℤ, used by
  `div_rem_poly` + `divw_remw_poly`), `tdiv_tmod_unique_full_nat`,
  `extractLsb_is_toInt` (pure BitVec, used by `divw_remw_poly`).

When in doubt, `rg '\b<lemma_name>\b' SP1Chips/ SP1Operations/
SP1Foundations/` before deleting.

### Pattern: self-contained `_poly` cluster

Each chip's helper files typically end with a `section poly_helpers`
(or just a `_poly` cluster at the end of the file) that is self-
contained — it defines its own `is_real_poly`, `is_<op>_poly`,
`allHold_constraints_iff_<...>_poly`, `single_op_poly`, etc. The
deletion sweep is then "remove everything between `end constraints`
and `section poly_helpers` plus the leading `variable (Main : Vector
(Fin KB) N)` + `def is_real` block".

### Verification

After every per-file deletion commit:

1. `lake build SP1Chips` clean: 0 errors, 0 warnings.
2. `rg 'Vector \(Fin KB\)' SP1Chips/` should shrink monotonically.
3. `rg '\.allHold\b' SP1Chips/` likewise (the field-agnostic
   `.allHold_poly` projection has a different name).
4. `rg 'Fin KB' SP1Chips/` will still show hits inside `--` doc
   comments referencing the old recipe — these are fine. Grep `--`-
   excluded for the structural check.
5. `lean_verify` on every `correct_<v>_poly` to confirm no `sorryAx`
   slipped in. Standard axioms only (`propext`,
   `Classical.choice`, `Quot.sound`).

The 2026-05-15 sweep deleted ~3290 lines from DivRem alone and ~1660
lines from ShiftRight; the cumulative SP1Chips/ deletion was ~7000
lines net. See `git log --grep="drop Fin KB"` for the per-commit
trail.

### KB-specific literal pre-check

Before committing to a chip's full `_poly` migration *and* later
deletion, run the field-genericness check from
`FIELD_GENERIC.md`'s "KB-specific literal blockers" section:

```bash
grep -oE ' \* [0-9]{8,}' SP1Chips/<Chip>/Constraints.lean | sort -u
```

If the chip's constraint body uses an 8+-digit literal that's
field-specific (e.g. `2097414145 = 64⁻¹ mod KB`), the `_poly`
companion either needs an extra typeclass hypothesis or the upstream
compiler needs a refactor — see the linked doc for the trade-offs.
Don't start the migration until that question is settled, or the
deletion sweep at the end becomes impossible.

## Note on the DivRem multi-file layout

DivRem is the only chip whose `Constraints.lean` was too large to keep monolithic. Helpers and per-opcode proofs were split into siblings under `SP1Chips/DivRem/`:

- `Constraints.lean` — autogen `section constraints ... end constraints` plus the closely-coupled `allHold_constraints_iff_poly`. **This is still the only file the regen script touches**; the script only edits content between the `section constraints` and `end constraints` markers, which all live here.
- `Common.lean` — `is_*_poly` flag defs, `single_op_poly`, `register_bounds_poly`, `op_a_is_0_poly`, `ops_U64_b_c_poly`, `sp1_op_{a,b,c}_poly`, and shared auxiliaries (`div_mod_decomposition_w`, `tdiv_tmod_unique_full*`, `sum_zero_abs_poly`, `Word_toInt_poly_neg_form_eq_HWord_toInt_poly`).
- `DivRem.lean` / `DivuRemu.lean` / `DivwRemw.lean` / `DivuwRemuw.lean` — one opcode pair each (`<variant>_poly` core).

After a regen, the only file that should show splices is `Constraints.lean`. If the iff RHS needs a corresponding update (step 5 of the playbook above), the lemma lives in the same file. Helper updates (step 6) for `register_bounds` / `ops_U64_b_c` / `single_op` / `op_a_is_0` live in `Common.lean`. The four opcode files only need attention if a `Main[k]` index referenced by the destructured-then-renamed variables (`a0..a3`, `b0..b3`, `c0..c3`, etc.) at the head of `spec.<variant>` changes meaning — in practice the `set ... := Main[k]` block at the head of each spec wrapper is the only place where indices appear literally.
