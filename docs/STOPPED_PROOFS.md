# Stopped proofs — is_trusted removal cleanup

Commit `e686807` ("Updated extraction without is_trusted and some opcode changes") regenerated every `SP1Chips/*/Constraints.lean` after dropping the `is_trusted` field from Reader record types (`RTypeReader`, `ITypeReader`, `ITypeReaderImmutable`, `ALUTypeReader`). This shifted `Main` indices above the removed column by −1 (or by −2 for Load/Store chips, which also dropped a `public_value` column).

A follow-up session applied mechanical index shifts and `stop` markers to make the 17 affected chips compile. The stops produce `declaration uses sorry` warnings and need to be closed with real proofs.

## What's stopped

### Fully closed — no stop needed

- `SP1Chips/SubwChip.lean` — `correct_subw` closes cleanly after the mechanical shift.
- `SP1Chips/Load/LoadDouble/Constraints.lean` — the `allHold_constraints_iff_of_is_ld` helper's `simp` proof still closes.

### Chip-level theorems stopped

- ~~`LoadDoubleChip.correct_ld`, `StoreDoubleChip.correct`, `StoreByteChip.correct`, `StoreHalfChip.correct`, `StoreWordChip.correct`~~ — closed.
- ~~`LoadByteChip.correct_lb/lbu`, `LoadHalfChip.correct_lh/lhu`, `LoadWordChip.correct_lw/lwu`~~ — closed.
- `BitwiseChip.correct_xor/xori/or/ori/and/andi`
- `LtChip.correct_slt/slti/sltu/sltiu` (plus `sp1_op_a/b/c` defs inside the chip file)
- `MulChip.correct_mul/mulh/mulhu/mulhsu/mulw`
- ~~`ShiftLeftChip.correct_sll/slli/sllw/slliw`~~ — closed.
- `ShiftRightChip.correct_srl/srli/srlw/srliw/sra/srai/sraw/sraiw`
- `BranchChip.correct_beq/bne/blt/bge/bltu/bgeu`
- `DivRemChip.correct_div/divu/divw/divuw/rem/remu/remw/remuw` + `correct_prologue_facts` helper
- `JalChip.SP1JAL_correct` + `op_a_lt32_of_constraints` helper

### Constraints.lean helpers stubbed/stopped

- ~~`Load/LoadByte/Constraints.lean` — `allHold_constraints_iff_of_is_lb/lbu` stubbed to `↔ True` with `stop`~~ — restored.
- ~~`Load/LoadHalf/Constraints.lean` — same stubbing for `lh/lhu`~~ — restored.
- ~~`Load/LoadWord/Constraints.lean` — same for `lw/lwu`~~ — restored.
- `Bitwise/Constraints.lean` — `allHold_constraints_iff`, `single_op`, `register_bounds`, `immediate_bounds`, `op_a_is_0`, `ops_U64_b_c`, `ops_U64_a`, `ops_U64`, `sp1_op_a/b/c/c_imm`, `spec.xor/xori/or/ori/and/andi` all have `stop`
- `Lt/Constraints.lean` — 4 `allHold_constraints_iff_*` lemmas stopped (simple `simp_all; intros; omega` proofs that timed out)
- `Mul/Constraints.lean` — `allHold_constraints_iff`, `single_op`, `register_bounds`, `op_a_is_0`, `ops_U64_b_c`, `sp1_op_a/b/c`, `spec.mul/mulh/mulhu/mulhsu/mulw` stopped
- ~~`ShiftLeft/Constraints.lean` — `allHold_constraints_iff`, `cancel_mul_65536`, `is_mod_64`, `single_op`, `sll_real`, `sllw_real`, `bounds`, `sp1_op_a/b/c/c_imm/c_imm_w`, `spec.sll/slli/sllw/slliw` stopped~~ — closed.
- `ShiftRight/Constraints.lean` — many stops; `set_option linter.unusedVariables false` file-wide
- `Branch/Constraints.lean` — `single_op`, `is_trusted_of_constraints`, `eq_signExtend_of_is_real`, `add_signExtend_of_constraints` stopped
- `DivRem/Constraints.lean` — many stops; `set_option linter.unusedVariables false` file-wide

### Not done — deferred

- `SP1Chips/JalrChip.lean` / `SP1Chips/Jalr/Constraints.lean` — the regeneration had changes beyond the `is_trusted` removal (size went 39 → 35, a −4 shift) that need case-by-case analysis.

## Index shifts applied per chip

Shift rule is "for every `Main[k]` with `k > cutoff`, replace with `Main[k−1]`" (unless noted).

| Chip | Old size → new | Removed column | Shift rule |
|------|----------------|----------------|-----------|
| Add, Addi, Sub | already done in commit | Main[28], [25], [28] | — |
| Addw | partial in commit | — | `stop` already in place |
| Subw | 33 → 32 | Main[28] (is_trusted) | k > 28 → k − 1 |
| Bitwise | 52 → 51 | Main[32] | k > 32 → k − 1 |
| Lt | 45 → 44 | Main[32] | k > 32 → k − 1 |
| Mul | 83 → 82 | Main[28] | k > 28 → k − 1 |
| ShiftLeft | 66 → 65 | Main[32] | k > 32 → k − 1 |
| ShiftRight | 70 → 69 | Main[32] | k > 32 → k − 1 |
| Branch | 46 → 45 | Main[25] | k > 25 → k − 1 |
| DivRem | 247 → 246 | Main[28] | k > 28 → k − 1 |
| Jal | 32 → 31 | Main[22] | k > 22 → k − 1 (opcode also 33 → 46) |
| Load/Store chips | −2 each | Main[25] + a public_value column | two separate −1 shifts |

## Mechanical shift + stop pattern

For any future chip that needs the same treatment:

1. **Find the removed column** by comparing the current generated constraint with its predecessor:

   ```bash
   git show e686807^:SP1Chips/<Chip>/Constraints.lean | grep -oE "is_trusted := Main\[[0-9]+\]"
   ```

   Call the result `removed_idx`.

2. **Apply the Python shift** to both the `Constraints.lean` and `<Chip>Chip.lean` files:

   ```python
   import re
   # Remove is_trusted field references
   text = re.sub(r', is_trusted := Main\[\d+\]', '', text)
   # Shift Main[k] -> Main[k-1] for k > removed_idx
   def shift(m):
       k = int(m.group(1))
       if k > removed_idx:
           return f"Main[{k-1}]"
       return m.group(0)
   text = re.sub(r"Main\[(\d+)\]", shift, text)
   ```

3. **Fix the file-wide `Vector (Fin KB) N`:**

   ```bash
   sed -i 's/Vector (Fin KB) <old>/Vector (Fin KB) <new>/g' SP1Chips/<Chip>/Constraints.lean SP1Chips/<Chip>Chip.lean
   ```

4. **Inject `stop`** after every `:= by` in the hand-written tail of `Constraints.lean` (after `end constraints`) and every `theorem correct_*` in the `Chip.lean`. Walk the file line-by-line and add `stop` at the indent of the next non-blank line.

5. **`lemma spec.<op> (h : is_<op> Main)` blocks** — inject `have _ := h` before `stop` to silence the unused-variable warning.

6. **Chip.lean theorems** — inject `have _ := state_cstrs` (and `have _ := cstrs`, `have _ := h_is_*` if needed) before `stop` so the `variable`-block parameters auto-include. Otherwise, `def sp1_op_a : BitVec 5 := by stop; ...` won't capture `Main`/`cstrs` from the variable block and callers fail with "Function expected".

7. **If many lemmas stop early** — reach for file-wide `set_option linter.unusedVariables false` just after the `namespace <Name>` line rather than scattering `have _ := X`. Branch, ShiftRight, DivRem, and Jal all use this.

## Gotchas observed during the update

- `stop` followed by nothing is a parse error — append `trivial` or leave the original proof tactics in place. They won't execute but satisfy the parser.
- Auto-inserted `stop` must match the indent of the *next tactic*, not the `by` keyword. Use regex to detect indent from the following line.
- Load/Store helpers have RHSes with `is_trusted := Main[25]` field refs and out-of-bounds indices after shift — these don't elaborate at all. Stubbing to `↔ True` is fine; chip proofs that used them should then `stop` right before the `rw [allHold_constraints_iff_of_is_* ...]` line.
- `def sp1_op_a : BitVec 5 := by ...` in LtChip-style files (term-level proofs) need the `have _ := Main; have _ := cstrs; have _ := h_is_X` *inside* the `by` block to trigger variable auto-inclusion. Putting them outside `by` is a syntax error.
- `grind`, `omega`, and `aesop` on proofs that were previously closed by `simp_all` after the shift often time out rather than fail with a specific error. If a build exceeds ~60 s for a single lemma, stop it rather than waiting.

## Closing a stopped proof

When picking up work:

1. Read the old proof (preserved verbatim below each `stop`).
2. Note that the Reader no longer provides `cols.is_trusted = 1` — the classic extraction pattern `(h_reader.2.2.1.resolve_right (by decide))` needs to target a different conjunct.
3. Check if the hand-written helper in the same chip's `Constraints.lean` also has a `stop` — if the chip proof depends on that helper, close the helper first.
4. Rebuild only the touched file (`lake env lean SP1Chips/<Chip>Chip.lean`) rather than the whole package — DivRem and Branch take several minutes each.

## Lessons learned from ShiftLeft (closed) and others

- **Verify the `section constraints` block first.** Run `update_constraints.py` to ensure the auto-generated indices match SP1's current output. The hand-written code (iff RHS, `set` aliases, `is_real`, `sp1_op_*`) must mirror those indices. If they're off, the iff lemma's `simp [constraints, ...]` proof leaves an unsolved goal whose LHS and RHS differ in just a few `Main[k]` indices or opcode literals — that's the diagnostic signature.
- **`Main[i] = 0` substitution and `op_a_0` aliasing.** When the constraints def includes `(.assertZero Main[13])` (i.e., op_a_0 = 0), `simp [constraints]` propagates `Main[13] = 0` into the embedded `ALUTypeReader.constraints` call's `op_a_0` field. The iff RHS still has `op_a_0 := Main[13]`. Either (a) add `Main[13] = 0` as a trailing conjunct on the RHS and discharge with `rw [h13]`, or (b) leave the RHS open and prove `Main[13] = 0` is needed too. The original `simp_all [sub_eq_zero]` doesn't bridge this gap on its own.
- **Stale `set is_trusted := Main[i]` aliases.** With `is_trusted` removed, `Main[32]` (or wherever) is now `op_a_write_value[0]`. The proof body's `set is_trusted := Main[32]` line then collides with `set a0 := Main[32]` — both alias the same column, which confuses `omega` (it sees them as separate variables and can't substitute one for the other). Fix: delete the stale `set is_trusted := …` line in each spec.* lemma.
- **`bounds` lemma destructure shift.** `ALUTypeReader.allHold_constraints_iff_is_real` lost the leading `cols.is_trusted = is_real` conjunct. Drop the leading `h0` from any `obtain ⟨h0, h1, …, h18⟩ := alu` pattern in chip helpers (`bounds`, `register_bounds`, etc.) — `h18.1` then catches the trailing 2-tuple `(¬op_a_0 = 0 → …) ∧ (¬imm_c = 0 → …)` correctly, restoring the original proof.
- **`tauto` after `simp [constraints, sub_eq_zero]`.** In `allHold_constraints_iff` the simp closes most of the iff but leaves a residual `tauto`-shaped goal — the boolean disjunctions on the RHS need to be reordered against the LHS form. Adding `tauto` after the simp closes the standalone helper.
