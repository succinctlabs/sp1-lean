---
name: Mechanical Main[idx] shift + stop pattern for chip updates
description: When a constraint regeneration removes a column and shifts later indices, use a Python script to do the shift and inject `stop` — don't hand-edit or re-derive proofs.
type: feedback
originSessionId: 46ad662a-b54b-497b-a0ef-b07390243b4b
---
When the constraint compiler drops a column from a chip (e.g. `is_trusted`), every `Main[k]` index above the cutoff shifts down by 1 (or by 2 if two columns were dropped). The hand-written helpers in `*/Constraints.lean` and the `*Chip.lean` file both reference many indices and need matching shifts — often 50+ occurrences per chip.

**Why:** In this session the user explicitly said "If the build is timing out you should just add a stop at the start of the proof rather than building over and over". Attempting to close proofs manually or build-verify each edit is orders of magnitude slower than mechanically shifting indices + stopping.

**How to apply:**

1. Find the removed column's old index by running `git show <commit>^:SP1Chips/<Chip>/Constraints.lean | grep -oE "is_trusted := Main\[[0-9]+\]"`. Call this `removed_idx`.

2. Apply a Python shift script to both `SP1Chips/<Chip>/Constraints.lean` and `SP1Chips/<Chip>Chip.lean`:

   ```python
   import re
   # Remove is_trusted fields
   text = re.sub(r', is_trusted := Main\[\d+\]', '', text)
   # Shift Main[k] -> Main[k-1] for k > removed_idx
   def shift(m):
       k = int(m.group(1))
       if k > removed_idx:
           return f"Main[{k-1}]"
       return m.group(0)
   text = re.sub(r"Main\[(\d+)\]", shift, text)
   ```

3. Fix the file-wide `Vector (Fin KB) N` with `sed -i 's/Vector (Fin KB) <old>/Vector (Fin KB) <new>/g'`.

4. Inject `stop` after every `:= by` in the hand-written tail of Constraints.lean (after `end constraints`) and every `theorem correct_*` in the Chip.lean. Use Python walking the file line-by-line, adding `stop` at the correct indent (match the indent of the next non-blank line).

5. For `lemma spec.<op> (h : is_<op> Main) :` blocks in Constraints.lean, inject `have _ := h` before `stop` — otherwise `h` becomes an unused-variable warning.

6. In Chip.lean theorems, inject `have _ := state_cstrs` (and `have _ := cstrs`, `have _ := h_is_*` if needed) before `stop` — the `variable` block's `cstrs`/`h_is_*` get auto-included if referenced later, but if everything after `stop` is dead, they need explicit mention.

7. If there are many lemmas that stop early and leave their own params unused, prefer file-wide `set_option linter.unusedVariables false` (placed just after `namespace <Name>`) over scattering `have _ := X` everywhere. Branch, ShiftRight, DivRem, Jal all use this.

**Gotchas:**

- Old Load/Store chip helpers (`allHold_constraints_iff_of_is_lb` etc.) have RHSes with `is_trusted := Main[25]` fields and out-of-bounds `Main[48]` references after shift. These don't elaborate at all — stubbing to `↔ True` is fine. Chip proofs that used these helpers should then `stop` right before the `rw [allHold_constraints_iff_of_is_lb ...]` line.
- `def sp1_op_a : BitVec 5 := by ...` — if the body only references `Main`/`cstrs`/`h_is_X` after `stop`, Lean won't auto-include them from the `variable` block, and callers `sp1_op_a Main cstrs h_is_X` fail with "Function expected". Fix: inject `have _ := Main; have _ := cstrs; have _ := h_is_X` inside the `by` block BEFORE `stop`.
- `stop` alone is invalid at the end of a proof block (Lean expects a following tactic). Append `trivial` or leave the original proof tactics in place (they won't execute but satisfy the parser).
- Indent matters: auto-inserted `stop` must match the indent of the tactics that follow it, not the `by` keyword. Use regex to detect indent from the next non-blank line.

This pattern was applied successfully to 17 chips in one session. See `project_is_trusted_removal_stops.md` for the per-chip coverage list.
