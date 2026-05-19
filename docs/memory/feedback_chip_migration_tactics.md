---
name: Chip-level _poly migration tactical patterns (Track C1)
description: Seven recurring frictions encountered during Add/Sub/Subw/Jal/Jalr chip migration over ZMod p — distinct from operation-level patterns
type: feedback
originSessionId: 40683e1b-dc1e-4432-b82a-a811cfe75be6
---
Tactical patterns learned migrating chip-side `correct_*` proofs to
`_poly` consumption (AddChip / SubChip / SubwChip, 2026-05-01). These
are chip-level — distinct from operation-level patterns documented in
`feedback_poly_proof_patterns.md`. Apply when migrating any new chip
under Track C1.

**1. Motive error on `rw [← is_subw]` when goal contains dependent occurrences.**

**Why:** After `simp_all` rewrites `Main[k]` using `is_msb` (which has
form `Main[k] = if (HWord.toBitVec32_poly cols.value).msb then 1 else
0`), the goal contains `(HWord.toBitVec32_poly cols.value).msb` inside
`if`/`Decidable` positions. A subsequent `rw [← is_subw]` (rewriting
`a.low - b.low` back to `HWord.toBitVec32_poly cols.value`) fails the
motive checker — Lean refuses to abstract the source pattern when the
target also contains `(toBitVec32_poly cols.value).msb` inside a
Decidable position.

**How to apply:** Do the chain `rw [← is_subw, sign_extend_*_poly is_U32_val]`
BEFORE `by_cases h_is_op_a_0 : Main[k] = 0` / `simp_all`. Then `simp_all`
sees only the unfolded form (with `if (a.low - b.low).msb`) and the
motive issue never arises. SubwChip's correct proof structure:
```
rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
  LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
rw [← is_subw, HWord.sign_extend_32_to_64_msb_poly is_U32_val]
by_cases h_is_op_a_0 : Main[6] = 0
· simp_all
· simp_all; ...
```

**2. `simp_all` collapses `Fact (2^17 < p)` to `Fact True` via local `hp17`.**

**Why:** If `hp17 : 131072 < p` (or any equivalent unfolding of `2^17 <
p`) is in scope before `simp_all`, simp uses it to rewrite the
proposition `2 ^ 17 < p` to `True`, which then propagates into the
`Fact (2^17 < p)` instance, leaving `inst✝ : Fact True` —
unrecoverable for downstream `Word.toBitVec64_poly_lowLimb_add_nat`-
style lemmas that need the original Fact.

**How to apply:** Don't bind `hp17 : 131072 < p` in the outer scope.
Re-derive it AFTER `simp_all`, when needed:
```
have hp_lt : 131072 < p := by
  have := Fact.out (p := 2 ^ 17 < p)
  have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
  omega
```
Same applies to any `(N : ZMod p).val = N` derivation that uses
`hp17` — declare close to use, not at proof start.

**3. `(N : ZMod p).val` doesn't reduce for opcode literals outside the val_X_zmod_p set.**

**Why:** `Field.lean` provides `val_X_zmod_p` simp lemmas for X ∈
{2, 4, 8, 16, 32, 256, 65536}. Reader iff_poly lemmas for chips with
other opcodes (Subw uses opcode 20, Addw uses 19, etc.) leave
`Opcode.ofNat (ZMod.val 20)` un-reduced because simp can't simplify
`(20 : ZMod p).val`.

**How to apply:** Add a local `val_X_lt` chain right after `haveI :
NeZero p`:
```
have h20_lt : (20 : ℕ) < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (20 : ℕ) < 2 ^ 17 := by decide
  omega
have h20_val : (20 : ZMod p).val = 20 := ZMod.val_natCast_of_lt h20_lt
```
Then pass `h20_val` to the reader simp set:
```
simp [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real,
  Opcode.ofNat, Nat.ble, h20_val] at reader_cstrs
```
For chips with multiple opcode literals in the constraint, derive each.

**4. `simp [← BitVec.toNat_inj]` recursion in `if_neg` discharge.**

**Why:** The pattern `rw [if_neg (by simp [← BitVec.toNat_inj]; omega)]`
works for SubChip but exhausts heartbeats / max recursion in larger
chips (SubwChip). simp seems to loop on the BitVec.toNat unfolding
combined with the larger context.

**How to apply:** Replace with an explicit `have`:
```
have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
  intro heq
  rw [← BitVec.toNat_inj] at heq
  simp at heq
  omega
rw [if_neg h_bv_neq, if_neg h_bv_neq]
```
The single `rw [←]` (instead of `simp [←]`) avoids the loop.

**5. Sign-extend simp set for HWord-result chips.**

**Why:** Migrating any 32-bit chip (Subw, Addw, Mulw, etc.) requires
unfolding `execute_RTYPEW_pure_w_poly` AND `execute_RTYPEW_pure_32_w_poly`
AND the Sail `sign_extend` wrapper to expose the `BitVec.signExtend`
form that `HWord.sign_extend_32_to_64_msb_poly` matches.

**How to apply:** Use this simp set:
```
simp only [execute_RTYPEW_pure_w_poly, execute_RTYPEW_pure_32_w_poly,
  LeanRV64D.Functions.sign_extend, Sail.BitVec.signExtend]
```
The Sail wrappers are `attribute [simp]` (in `SP1Foundations/BitVec.lean`)
so plain `simp` finds them, but `simp only` requires explicit listing.

**6. Upfront `simp [..., h_is_real]` strips later iff_is_real_poly applicability.**

**Why:** A chip-level `simp [SP1ConstraintList.allHold_poly, constraints,
SP1Constraint.toProp_poly, h_is_real] at cstrs` substitutes `M[N] = 1` in
ALL the sub-constraints, including the readers' `is_real` argument. The
reader sub-cstr now has `is_real := 1` literally, so a later
`rw [Reader.allHold_constraints_iff_is_real_poly h_is_real]` fails to
unify (the lemma expects `is_real` as a metavariable for `h : is_real = 1`,
but `is_real` is already `1`). Either pass `(is_real := 1) rfl` (works
but leaves projections un-reduced), or restructure UType-style.

**How to apply:** Mirror UType's pattern:
```
simp [constraints] at cstrs   -- no h_is_real
obtain ⟨..., reader_cstrs, rest⟩ := cstrs
rw [Reader.allHold_constraints_iff_is_real_poly h_is_real] at reader_cstrs
-- now apply h_is_real explicitly to other sub-cstrs as needed:
rw [h_is_real] at res_cstrs   -- AddOp etc.
-- For multi-component multiplicities like (Main[25] - Main[13]):
have hm : Main[25] - Main[13] = 1 := by rw [h_is_real, h13]; ring
rw [hm] at inc_pc_cstrs
```
Used in JalrChip 2026-05-03.

**7. `aesop` recursion on `isInitialized` side-goals.**

**Why:** In `rw [update_elp_state_of_isInitialized _ _ (by aesop)]` and
`rw [run_readReg_of_isInitialized _ _ (by aesop)]`, aesop must prove
`isInitialized (some-modified-state)`. With many bound hypotheses in
scope (chip cstrs, constraint destructures), aesop's search space
explodes and hits max recursion.

**How to apply:** Restrict aesop's hypothesis context with
`clear *- hs`:
```
rw [update_elp_state_of_isInitialized _ _ (by clear *- hs; aesop)]
rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
```
Used in JalChip + JalrChip. The Fin KB versions had the same pattern
implicitly (smaller contexts, aesop terminated).

These seven frictions are now load-bearing for any new Track C1
migration. Together with `feedback_poly_proof_patterns.md` (operation-
level), they cover the bulk of repeatable chip-migration drag.
