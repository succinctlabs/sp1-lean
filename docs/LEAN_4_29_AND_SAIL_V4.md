# Lean 4.29 + Sail v4 adaptation notes

Topical guide for the two upstream-driven adaptation efforts that landed in PR #92. These quirks repeated across many commits in the upgrade and are worth keeping institutional memory of, since the same shapes will recur the next time either dependency moves.

## Lean 4.29 specifics

### `BitVec.ofNatLT_eq_ofNat` rewrite ordering

Symptom: rewriting `BitVec.ofNatLT_eq_ofNat` *after* unfolding the chip's `PC` term leaves the lemma's LHS unable to match. The cast shape drifts as `PC` unfolds.

Fix: rewrite `BitVec.ofNatLT_eq_ofNat` *before* the `PC` rewrite, or stage the proof so the cast is resolved first. Canonical example: `correct_subw` (commit `16b1294`, "close correct_subw: defer BitVec.ofNatLT_eq_ofNat until after PC rewrite" — the "defer" wording in the message is misleading; the deferral is the *fix*, not the bug).

### `DecidableEq regidx`

Symptom: in 4.23, `instance : DecidableEq regidx := by simp; infer_instance` worked because `regidx`'s inner `BitVec (if false then 4 else 5)` reduces to `BitVec 5`. In 4.29, that path no longer finds the instance — `simp` normalizes the conditional but typeclass search doesn't pick the result up.

Fix: `instance : DecidableEq regidx := fun v v' => decidable_of_iff (v = v') (by simp)`. See `SP1Foundations/Register.lean:32`.

### `simp_all` regression on disjunctive conjunctions

Symptom: in 4.23, `have h : Main[i] = 1 := by simp_all [sub_eq_zero]` could discharge `Main[i] = 1` even when the hypothesis was a deeply nested conjunction containing `(... ∨ -1 = 0)` (the `-1 = 0` disjunct is `False` in `Fin KB` and gets eliminated). In 4.29, `simp_all` no longer pursues that elimination, leaving an unsolved goal.

Fix: project to the disjunctive hypothesis explicitly, then `.resolve_right (by decide)` to drop the `-1 = 0` branch, then `omega` or `sub_eq_zero` to recover the equation. Canonical example: `op_a_lt32_of_constraints` in `SP1Chips/JalChip.lean`. The pattern is:

```lean
have h : Main[i] = 1 := by
  have := (h_cstrs.2.2.2.1).resolve_right (by decide)
  omega
```

### `simp_all` general leakage

Independent of 4.29 but worsened in this cycle: `simp_all` can rewrite hypotheses you didn't intend to touch. The temp patch in `419ee1d` ("temp patch for leaky simp_all call") localizes the workaround in `DivRem/Constraints.lean`. Prefer **targeted** `simp [...] at h` over `simp_all` in this repo; if you must use `simp_all`, audit the full goal afterwards.

### High-priority arithmetic instance synthesis

Symptom: instance synthesis for `Fin KB` (or any hot type that participates in thousands of generated arithmetic terms) fans out to 5–9 candidates per operation. With chip constraints containing thousands of `Fin KB` ops, this dominates elaboration time. ShiftRight took ~779s of cumulative synthesis time before the fix.

Fix: declare the arithmetic instances at high priority. `SP1Foundations/Field.lean` does:

```lean
@[instance 10000] instance : Add (Fin KB) := ...
@[instance 10000] instance : Mul (Fin KB) := ...
-- ditto Sub, Neg, Pow, etc.
```

When you introduce a new arithmetic type that will appear at this scale, do this immediately — it's cheap and the alternative is a real perf regression.

### `BitVec.setWidth` simp normal-form drift

Symptom: `simp` rewrites `BitVec.setWidth (BitVec.extractLsb …)` to `BitVec.ofNat _ (… .toNat >>> _)`. After that, `apply bitVec_sshiftright_eq` fails because the syntactic LHS is gone.

Fix: either rewrite once with `bitVec_sshiftright_eq` then close with the unfolded equation (see `exec_RTYPEW_pure_bv_to_w`'s SRAW case in `SP1Foundations/SailM.lean`), or simp into the new normal form with `simp [BitVec.extractLsb, BitVec.setWidth_eq, BitVec.extractLsb', BitVec.toNat_setWidth]` and reason from there.

### `bv_decide` and `↑↑` casts

Symptom: `bv_decide` reports "potentially spurious counterexample" with `BitVec.ofNat 128 ↑↑(...).toNat` listed as opaque. The double-cast `ℕ → Fin KB → ℕ` is introduced when a literal `ℕ` flows into a `Vector (Fin KB) n` slot.

Fix: strip the cast first using `Fin.val_cast_of_lt` (when you can prove the value `< KB` — byte slices give `< 256`, etc.), then call `bv_decide`. Canonical example: `byte_decomp_128` in `SP1Foundations/Word.lean`.

### Structural pattern matching in config-driven definitions

Symptom: 4.29 tightened pattern-match exhaustiveness in `if-then-else` over evaluated booleans (commit `b3995e8`, "build errors from structural config pattern matches"). Code that worked in 4.23 because the evaluator collapsed `if false then ... else ...` now needs explicit handling.

Fix: rewrite using `match` or pull the boolean out of the type so the elaborator can see it's a literal. The fix is usually mechanical once you spot it.

## Sail v4 specifics

### Renames

- `bool_to_bits` → `bool_to_bit`
- `bool_bits_forwards` → `bool_bit_forwards`

### Removals

- `shift_right_arith` — gone; the right-shift proofs now go through `simp [shift_bits_right_arith, Sail.BitVec.toNatInt]` plus `congr 1` (see `SailM.lean` SRAW case).
- `check_misaligned` — gone; alignment is now checked by `jump_to`'s new platform-read gate (see below).
- `default_write_acc` — gone; not replaced.
- `force_pc_eq` — no longer a `@[simp]` lemma; the previous decl is commented out in `SailM.lean`. PCs are now equal definitionally where they need to be.

### `Sail.BitVec.toNatInt` simp residue

Sail v4 leaves `Sail.BitVec.toNatInt` in goals where v2 had implicit nat coercions. The fix is universal: add `Sail.BitVec.toNatInt` to the `simp [...]` list whenever you see `↑BitVec.toNat` residue. This is a one-line pattern, but it's easy to miss because the residue often shows up *after* a successful simp call appears to do nothing.

### New platform reads in control flow

Sail v4 added two platform-extension reads inside control-flow instructions that SP1's `isInitialized` precondition cannot discharge directly:

- `update_elp_state` (called by `execute_JALR`) reads `cur_privilege` to test `currentlyEnabled Ext_Zicfilp`.
- `jump_to` reads `misa` to test `currentlyEnabled Ext_Zca`.

SP1 doesn't enable either extension, so the reads are state-preserving in our setting. Three theorems in `SP1Foundations/MemChecks.lean` close the gap (they were initially axioms in `d9ae993` and were promoted to theorems before the PR opened):

- `update_elp_state_of_isInitialized` — Zicfilp disabled ⇒ `update_elp_state = pure ()`.
- `jump_to_of_mod4_eq_zero` — 4-aligned target ⇒ `jump_to target = writeReg nextPC target`.
- `jump_to_of_mask_mod4_eq_zero` — specialization for JALR's `(rs1 + imm) & ~1` shape.

Plus `SailState.isInitialized_insert` to keep the precondition surviving post-write state extensions, and `mod4_eq_zero_of_0_1_are_0` (reverse of the existing `mul4_means_0_1_are_0`) for chips with bit-level alignment hypotheses.

### `MemoryAccessType` replaces `AccessType`

Sail v4 changed PMP/PMA check signatures from `AccessType.Write Data` / `AccessType.Read ()` to `MemoryAccessType.Store mem_payload.Data` / `MemoryAccessType.Load mem_payload.Data`. Existing axioms `pmp_check_machine` / `pmp_check_machine'` were updated to the new shape, and new axioms `pma_check_machine` / `pma_check_machine'` (`SP1Foundations/Assumptions.lean:123,132`) were added to mirror the PMP pair for the new PMA check the v4 extraction emits.

### `execute_RTYPE'` vs `execute_RTYPE`

When chip proofs `simp [spec_*, sp1_*, execute_<TYPE>]`, sail v4's heavier monadic shape can leave residual Sail bookkeeping that was harmless in v2. Naming convention introduced in this cycle: a primed variant (`execute_RTYPE'`, `execute_RTYPEW'`, etc.) is the "isolated pure part" of the operation. **Drop unprimed `execute` from your simp set if you see leftover SailM noise in your goal.** Use the primed variant alone.

### Sail-v4 source repo move

`Lean_RV64D` now tracks `https://github.com/opencompl/sail-riscv-lean` `main`. The previous `succinctlabs/sail-riscv-lean @ sp1-lean-air-verification` fork is no longer used. If you `git log` the sail dep for context, point at the upstream repo.
