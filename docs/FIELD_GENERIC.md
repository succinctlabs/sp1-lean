# Field-genericization

The SP1 AIR formalization is parameterizable over `{F : Type} [Field F]`
(plus light extras at call sites — `[Fact (Nat.Prime p)]`,
`[Fact (2^17 < p)]`, `CoeHead F ℕ`). Concrete proofs are anchored at
`F := Fin KB` (KoalaBear); polymorphic `_poly` companions exist for
every chip so a future deployment over BabyBear / Mersenne31 / another
STARK field can reuse the proof scaffold instead of forking it.

This doc captures current state, the design that was chosen, the
polymorphic proof patterns that recur, the KB-specific literal traps
to watch for, the DivRem worked example, and a compressed timeline
appendix. For the toolchain side, see `LEAN_AND_SAIL_NOTES.md`. For
the proof-perf and gotchas side, see `PROOF_PATTERNS.md`. For
constraint-shape regen mechanics, see `CONSTRAINT_REGEN.md`.

## Current state — 2026-05-15

**The effort is substantively complete.** All 24 chips have at least
one `correct_*_poly` theorem; `grep -rn "Fin KB" SP1Chips
SP1Operations` returns 0 matches; `lake build` is clean (8522 jobs,
0 errors, 0 warnings); every `correct_*_poly` audited via
`lean_verify` shows only standard axioms (`propext`,
`Classical.choice`, `Quot.sound`, plus pre-existing
`bv_decide.ax_*` for the bv-using arms). **No `sorryAx`** anywhere
in the polymorphic surface.

The upstream `sp1-constraint-compiler` emits field-generic Lean
directly: `{F : Type} [Field F] [CoeHead F ℕ]? (Main : Vector F N) :
SP1ConstraintList F`. The Rust changes live in `sp1`'s
`dtumad/field-generic-constraint-extraction` branch:
`crates/hypercube/src/ir/{shape,expr,func,var,ast}.rs` plus the binary
at `crates/core/compiler/src/main.rs` (transitive `CoeHead F ℕ`
fixpoint over the module call graph).

`update_constraints.py` is now a verbatim writer over the compiler's
output — it shells out to `cargo run -p sp1-constraint-compiler` and
splices the result between each file's `section constraints` /
`end constraints` markers. No post-processing. Four scalar-only ops
(`IsZeroOperation`, `U16CompareOperation`, `U16MSBOperation`,
`CPUState`) emit `F : Type` rather than `Type*` because the Rust IR
can't see through a `Shape::Struct` to tell whether the hand-written
Lean counterpart contains `Word F` internally — operations are
unconditionally `F : Type`. Compiles fine (`Type ⊆ Type*`); zero
downstream callers depend on `Type*`.

**Chip migration scoreboard:**

| Status | Count | Chips |
|---|---|---|
| ZMod p only (done) | 24 | Add, Addi, Addw, Bitwise, Branch, DivRem, Jal, Jalr, 4×Load, LoadX0, Lt, Mul, ShiftLeft, ShiftRight, 4×Store, Sub, Subw, UType |
| Hybrid / Fin KB-only | 0 | — |

The only remaining `Fin KB` references in the formalization live in
`SP1Foundations/Field.lean` (the concrete KoalaBear instance block)
— intentional, anchors the `F := Fin KB` instantiation.

**Follow-up cleanup (not blocking):**
`sp1/crates/core/compiler/src/ir/` (2839 lines, `ast.rs` +
`builder.rs`) is dead code in the upstream — no `mod ir;` in the
binary's `main.rs`, no `lib.rs`. Confirmed by moving the dir aside
and rebuilding successfully. Pending an explicit cleanup commit
upstream.

## Layer map

| Layer | File pattern | Field status | Why |
|---|---|---|---|
| Datatypes | `SP1Foundations/Constraint.lean`, `Word.lean` | Generic `(F : Type*) [Field F]` | Datatypes don't depend on the prime; only call sites do. |
| Field instances + computational lemmas | `SP1Foundations/Field.lean` (`KoalaBear` namespace) | KB-specific (by design) | These define `Fin KB` *as* a usable field; high-priority instances are perf-critical (see `PROOF_PATTERNS.md`). |
| Generic field lemmas | `SP1Foundations/Field.lean` (polymorphic primitives) | Generic | `mul_inv_{4,65536}_eq_one_iff_poly`, `val_sub_cases`, `val_*_ne_zero`, `small_nat_eq_zmod`, `CoeHead` instances. Used by every `_poly` proof. |
| Operation/Compare/Reader auto-gen | `SP1Operations/{Operation,Compare,Reader}/*/Constraints.lean` | Parametric `F` (upstream-emitted) | Compiler emits over `{F : Type} [Field F]`. |
| Operation/Compare/Reader hand-written | `SP1Operations/{Operation,Compare,Reader}/*.lean` (top-level) | `_poly` companions for every iff/spec | Concrete `Fin KB` versions deleted; `_poly` versions are the canonical surface. |
| Chip auto-gen | `SP1Chips/<Chip>/Constraints.lean` | Parametric `F` | Same as ops. |
| Chip top-level | `SP1Chips/<Chip>Chip.lean` | `correct_*_poly` instantiated at `ZMod p` with `[Fact (Nat.Prime p)] + [Fact (2^17 < p)]` | KB-typed `correct_*` removed across all chips; `_poly` is the surface. |
| Sail bridge | `SP1Foundations/SailM.lean` | Field-agnostic | Bridges to `BitVec`/`Nat`; never touches `KB`. |
| Custom tactics | `SP1Foundations/Tactics.lean` | Generic | `bv_amicus_kerneli` is `BitVec`-width-parameterized; `get_elem_tactic` rebound to `norm_num1`; `mul_diff_one_neq` already takes `[Field α]`. |

## How to instantiate at a different prime field

Recipe for adding a parallel `ZMod <NewPrime>` instantiation (e.g.
BabyBear = `2^31 - 2^27 + 1`):

1. **Add the new prime's instance block in `SP1Foundations/Field.lean`.**
   Mirror the `KoalaBear` namespace: prime fact (`Fact (Nat.Prime
   <NewPrime>)`), `NeZero`, `Field` (via `ZMod.instField`),
   `NoZeroDivisors`, and the 11 high-priority arithmetic instances.
   The arithmetic instances are perf-critical — without them,
   typeclass synthesis explodes (see `PROOF_PATTERNS.md`).

2. **Confirm the `Fact (2^17 < <NewPrime>)` precondition holds.** Most
   `_poly` lemmas assume this. If your prime is smaller, you'll need
   to refactor the bound thresholds in the polymorphic primitives.
   BabyBear (`~2^31`) and Mersenne31 (`2^31 - 1`) are both fine.

3. **Run the SP1 constraint compiler.** With the upstream field-
   generic emission (current state), no per-prime regen is needed —
   `Constraints.lean` files are parametric over `F`. The new prime
   simply instantiates `F := ZMod <NewPrime>` at the call site.

4. **Instantiate the chip-level `correct_*_poly` theorems at the new
   prime.** Each takes `{p : ℕ} [Fact (Nat.Prime p)] [Fact (2^17 < p)]`.
   No re-proving required — the proofs are already polymorphic.

5. **Adjust KB-specific literal blockers (if hit).** Two chips
   (`ShiftLeft`, `ShiftRight`) embed `2097414145 = 64⁻¹ mod KB`
   directly in their constraint bodies. For a different prime,
   either compute the new literal and provide a bridge fact, or
   refactor the upstream compiler to emit `(64 : F)⁻¹` symbolically.
   See "KB-specific literal blockers" below.

6. **Sail bridge** (`SP1Foundations/SailM.lean`) is field-agnostic.
   No changes expected.

**Estimated effort** for a BabyBear instantiation given this
groundwork: 1–2 sessions for the field setup and bridges, ~1 session
to thread the new prime through chip instantiations. The Shift\*
literal issue is the main wild card — see below.

## Polymorphic proof patterns

The patterns below recur across `_poly` companion proofs over
`ZMod p`. Future migration / extension work hits these often enough
that anticipating them upfront cuts iteration time substantially. Each
pattern includes a file/line citation into a working call site.

### 1. `simp_all` strips `Fact` instances and local helpers — re-derive after

When you `simp_all` to normalize a chunk of constraint structure,
local `have h := ...` bindings and synthesized `[Fact (...)]`
instances may disappear from the post-`simp_all` context. The
CLAUDE.md warning about "leaky simp_all" applies in the polymorphic
case too.

A specific variant: if `hp17 : 131072 < p` is in outer scope before
`simp_all`, simp rewrites the proposition `2 ^ 17 < p` to `True`,
which propagates into the `Fact (2^17 < p)` instance, leaving
`inst✝ : Fact True` — unrecoverable for downstream
`Word.toBitVec64_poly_lowLimb_add_nat`-style lemmas that need the
original `Fact`.

**Fix**: declare bounds AFTER `simp_all`, not before. Use
`ZMod.val_natCast_of_lt (show (N : ℕ) < p by omega)` (which only
needs `hp_lt : 131072 < p` from `Fact (2^17 < p)`) rather than the
`val_*_zmod_p` simp family (which needs the original `Fact`).
Canonical pattern around `correct_mul_poly` in `SP1Chips/MulChip.lean`
and the `Phase 5` Mul chip migration cluster.

### 2. Shadow hypotheses before `rcases` if you'll need them later

`rcases h with ⟨...⟩` consumes `h`. If you need to invoke a
different lemma on the *original* constraint list later (e.g.
`spec.unsigned_poly` / `spec.signed_poly` after destructuring), shadow
it first:

```lean
intro cstrs
have cstrs := cstrs   -- shadow
rcases cstrs with ⟨...⟩
-- original `cstrs` is back in scope after the rcases
```

Canonical: `LtOperationSigned.spec.branch` and the `branch_poly`
companion in `SP1Operations/Compare/LtOperationSigned.lean`.

### 3. Anonymous-constructor struct projections need explicit simp normalization

`{ field := #v[a, b, c, d], ... }.field[2]` doesn't reduce to `c`
without simp. After `rw [iff_lemma]`, the iff RHS often has anonymous
constructors of `cols` structs whose `[i]` accesses must be unfolded.

**Fix**: add after destructuring an `iff_poly`:

```lean
simp only [Vector.getElem_mk, List.getElem_toArray,
  List.getElem_cons_zero, List.getElem_cons_succ]
  at h_f0 h_f1 h_f2 h_f3 ...
```

### 4. Field-level `<` doesn't auto-reduce to `.val <`

`ZMod.instLT` makes `(x : ZMod p) < y` literally `x.val < y.val`, but
Lean's unifier doesn't unfold this for tactic lemmas that expect
explicit `.val < ...`. Convert manually:

```lean
have hr0' : cols.bitwise_operation.result[0].val < 256 := by
  have h : cols.bitwise_operation.result[0].val < (256 : ZMod p).val := hr0
  rw [h256_val] at h; exact h
```

where `h256_val : (256 : ZMod p).val = 256` (re-derived per pattern 1
if `simp_all` has fired).

### 5. `ByteOpcode.ofNat (ZMod.val k)` needs `(k : ZMod p).val = k` to reduce

When chip / op constraints use opcodes like 1 (OR), 2 (XOR), 9 (SLT)
as `ZMod p` literals, the constraint structure becomes `match
ByteOpcode.ofNat (ZMod.val 1) with ...`. Simp won't pick the OR arm
without first reducing `(1 : ZMod p).val = 1` (via `ZMod.val_one p`
with `[Fact (1 < p)]`) or `(2 : ZMod p).val = 2` (via
`val_2_zmod_p` / `ZMod.val_natCast_of_lt`).

`Field.lean` provides `val_X_zmod_p` simp lemmas for X ∈ {2, 4, 8,
16, 32, 256, 65536}. Reader iff_poly lemmas for chips with other
opcodes (Subw uses 20, Addw uses 19, etc.) need a local
`val_X_lt` chain:

```lean
have h20_lt : (20 : ℕ) < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (20 : ℕ) < 2 ^ 17 := by decide
  omega
have h20_val : (20 : ZMod p).val = 20 := ZMod.val_natCast_of_lt h20_lt
simp [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real,
  Opcode.ofNat, Nat.ble, h20_val] at reader_cstrs
```

### 6. Motive errors on `rw [← is_subw]` after dependent simps

After `simp_all` rewrites `Main[k]` using `is_msb` (which has form
`Main[k] = if (HWord.toBitVec32_poly cols.value).msb then 1 else 0`),
the goal contains `(HWord.toBitVec32_poly cols.value).msb` inside
`if`/`Decidable` positions. A subsequent `rw [← is_subw]` then fails
the motive checker.

**Fix**: do the chain `rw [← is_subw, sign_extend_*_poly is_U32_val]`
BEFORE `by_cases h_is_op_a_0` / `simp_all`. Then `simp_all` sees only
the unfolded form. Canonical: `SubwChip`'s correct proof structure.

### 7. `intros; subst_vars; grind` for `grind` ring-init failures on free `Fin KB`

`grind` reports "error while initializing `grind ring` operators:
instance for `NatCast.natCast` is not definitionally equal to the
expected one `Lean.Grind.Semiring.natCast`" when a free `Fin KB`
variable is in scope. The fix is to substitute the concrete numeral
(usually `is_real = 1`) through the goal first: `intros; subst_vars;
grind`. Works when the remaining `Fin KB` terms are structure
fields / indexed entries — not when the goal genuinely needs ring
reasoning over free variables.

### 8. `not_eq_inv * (x - y) = 1` contradiction under `x = y`

In Compare/Lt chips with the standard uniqueness witness
`not_eq_inv * (x - y) = 1`, proving `¬(x = y)` after `intros;
rename_i eqc`:

```lean
rw [eqc] at lt_07
simp only [sub_self, mul_zero] at lt_07
exact absurd lt_07 (by decide)
```

`simp_all` is too aggressive here — `simp only` is the right
granularity. Canonical: `LtOperationSigned.spec.branch` at
`SP1Operations/Compare/LtOperationSigned.lean:166–188`.

### 9. `clear *- hs; aesop` for `isInitialized` side-goals

In `rw [update_elp_state_of_isInitialized _ _ (by aesop)]` /
`rw [run_readReg_of_isInitialized _ _ (by aesop)]`, aesop must prove
`isInitialized (some-modified-state)`. With many bound hypotheses
(chip cstrs, constraint destructures), aesop's search space explodes
and hits max recursion.

**Fix**: restrict aesop's hypothesis context with `clear *- hs`:

```lean
rw [update_elp_state_of_isInitialized _ _ (by clear *- hs; aesop)]
rw [run_readReg_of_isInitialized _ _ (by clear *- hs; aesop)]
```

Used in `JalChip` and `JalrChip`.

### 10. Upfront `simp [..., h_is_real]` blocks later `iff_is_real_poly`

A chip-level `simp [..., h_is_real] at cstrs` substitutes `M[N] = 1`
in ALL the sub-constraints, including the readers'. A later
`rw [Reader.allHold_constraints_iff_is_real_poly h_is_real]` then
fails to unify (the lemma expects `is_real` as a metavariable, but
it's already `1`).

**Fix**: destructure first without `h_is_real`, then `rw` the iff,
then apply `h_is_real` explicitly to other sub-cstrs:

```lean
simp [constraints] at cstrs   -- no h_is_real
obtain ⟨..., reader_cstrs, rest⟩ := cstrs
rw [Reader.allHold_constraints_iff_is_real_poly h_is_real]
  at reader_cstrs
rw [h_is_real] at res_cstrs   -- AddOp etc., applied per-component
```

Canonical: `JalrChip` 2026-05-03.

### 11. Multi-variant chips: `sum_eq_one_*` + `single_op_poly`

When a chip has multiple variants sharing one big
`allHold_constraints_iff_poly` (Bitwise: 6 arms; Branch: 6; Mul: 5),
don't write 6× per-variant iff_polys. Write one shared iff_poly plus
two families of small helper lemmas:

- `sum_eq_one_of_eq_one_{left, mid, right}` (or analogous for N>3):
  given one column `= 1` and the bool/sum disjunctions, conclude
  `sum = 1`. Discharges `1 = 0` / `2 = 0` / `3 = 0` contradictions
  via `linear_combination` with explicit coefficients + `ZMod.val_*`
  injection.
- `single_op_poly`: given all bool disjunctions plus `sum = 1`,
  conclude mutual exclusion (one column at 1 forces the others to 0).

For multi-variant chips with `N > 3` arms, the cleanest engine is
`linear_combination` over the rotated arguments. See
`Bitwise/Constraints.lean` (3-way → 6 arms via `sum_eq_one_of_eq_one_*`)
and `Mul/Constraints.lean` (`MulOperation.single_op_poly`'s 5-way
boolean cascade with `four_bools_sum_zero` discharging 16 explicit
cases) for the canonical patterns.

For DivRem's 8-way mutex, the Nat-level recipe is cheaper than
128-case rcases:

```
linear_combination -sum_disj  -- permute sum so active flag is first
-- 7 ZMod.val_add_of_lt rewrites lift Σ = 1 from field to Nat
-- omega closes "others = 0"
-- (ZMod.val_eq_zero _).mp bridges back
```

### 12. Opcode-arg reduction: `push_cast; ring`, not direct `rw [show ...]`

When the iff_poly RHS has nested op-constraint calls with opcode
arguments like `Main[48] * 2 + Main[49] * 1 + Main[50] * 0`, Lean
prints the literals as `↑2`, `↑1` (Nat-cast displayed) but
typecheck-equals `2`, `1`. A direct
`rw [show Main[48]*2 + Main[49]*1 + Main[50]*0 = 2 from by ring]`
fails because the syntactic form has casts `ring` resolves but `rw`'s
pattern matcher does not.

**Fix**: `push_cast; ring` inside the `show`:

```lean
have h_xor_args : (Main[48] * 2 + Main[49] * 1 + Main[50] * 0 : ZMod p) = 2 := by
  rw [h_M48, h_M49, h_M50]; push_cast; ring
rw [h_xor_args] at h_bop
```

### 13. Struct-projection unfold: simp the operation constraints into `h_bop`

After applying `BitwiseU16Operation.spec.xor_poly` to `h_bop`, the
result has shape `Word.toBitVec64_poly (BitwiseU16Operation.constraints
b cc cols 2 1).1 = ...`. The `.1` projection on the operation's
tuple-typed output doesn't auto-reduce — unfold the operation's
constraint definition to expose the explicit byte-combined vector:

```lean
simp [BitwiseU16Operation.constraints,
  U16toU8OperationUnsafe.constraints,
  BitwiseOperation.constraints] at h_bop
```

### 14. `.cast` in `execute_*_pure_int` goals is `Nat → ℤ`, not `ZMod.cast`

When porting a chip-level `_poly` proof that goes through
`execute_*_pure_int` (DIV_REM is the standout), the post-simp goal
shows:

```
⊢ BitVec.ofNat 64 (b0.val + b1.val * 65536 + ...) =
    BitVec.ofNat 64 (b0.cast + b1.cast * 65536 + ...).toNat
```

The `.cast` is **NOT** `ZMod.cast` — it's the `Nat → ℤ` coercion
inserted to type-check `BitVec.ofNat 64 (q : ℤ)`, and the outer
`.toNat` is `Int.toNat`. The closer is:

```lean
push_cast [ZMod.cast_eq_val]; rfl
```

Plain `rfl` fails because the expressions are definitionally equal
only after the casts are pushed through. `bv_decide` fails because
the expressions involve free `ZMod p` variables. `norm_cast` makes no
progress because the casts are already at the leaves and the
`Int.toNat` isn't a cast it knows how to dispose of.

## KB-specific literal blockers

Some chip constraints embed precomputed field inverses that only
exist in KoalaBear. These block clean field-generic migration without
an extra typeclass hypothesis.

### Detection

```bash
grep -oE ' \* [0-9]{8,}' SP1Chips/<Chip>/Constraints.lean | sort -u
```

Any 8+-digit literal in a `*` context is suspect. The compiler's
output is comparing to "is this divisible by k" via multiplication
by `k⁻¹` and a small-result check (`((x - witness) * k⁻¹).val < ...`).

### The actual blocker

`ShiftLeft` and `ShiftRight` both contain `2097414145 = 64⁻¹ mod KB`
in their constraint bodies (e.g. `let E84 : F := E83 * 2097414145`
and `((c0 - m) * 2097414145).val < 1024`). For any other prime,
`2097414145` has no special meaning, so the divisibility-by-64 check
encoded as "multiply by precomputed inverse, check result is small"
**cannot be proven polymorphic** without an extra hypothesis.

Universal literals like `256` and `65536` (used in `Mul` / `DivRem`)
work in any prime large enough that the literal doesn't wrap; that's
why those migrations succeeded with just `[Fact (2^17 < p)]` and
friends.

### Options for unblocking

(a) **Carry the bit-trick as a hypothesis.** Add `Fact ((2097414145 :
ZMod p) * 64 = 1)` (or analogous for `k⁻¹` for other `k`) as a
precondition on every `_poly` theorem. Honest: theorems hold for any
field where the bit-trick holds. KB is one such.

(b) **Compiler refactor.** Change the upstream compiler to emit
`(64 : F)⁻¹` symbolically rather than the precomputed numeric value.
The four inverse families currently embedded: `(2^2)⁻¹`, `(2^3)⁻¹`,
`(2^8)⁻¹`, `(2^16)⁻¹`, plus the shift family's `(64 : F)⁻¹`. Each
field's bridge lemmas (`KoalaBear`'s `inv_*BB_eq*` cluster) then
become the per-field simp normal-form lemmas that rewrite `(k : F)⁻¹`
to the literal at the concrete instantiation.

The Shift\* chips' `_poly` companions landed *despite* this issue
because the literal is consistent across the proof — it just means
the proofs require `Fact (2 ^ 17 < p)` *plus* the implicit
`<NewPrime>` analogue of `2097414145`'s definition if instantiated at
a different prime. A later effort can adopt option (b) cleanly.

### Surface symptom (separate failure mode)

`ShiftLeft`'s `allHold_constraints_iff_poly` attempts also blew up
along a separate axis: a 195-let constraints body and ~70-clause RHS
means `simp [constraints, sub_eq_zero]; tauto` runs >8 minutes and
exhausts memory. Same shape applies to DivRem (~247 cols), Mul,
Bitwise, Branch (~46–52 cols). Working migrations avoid the
chip-level `iff_poly` and use direct destructure of the constraint
list per arm (Branch's `BranchChip.lean:232` pattern is canonical).
See `feedback_mul_iff_poly_complexity` in memory for the bound-source
mismatch that makes a literal port not close anyway.

## Worked example: DivRem `_poly` port

The DivRem migration was the longest single-chip effort of the
field-genericization. The story is worth preserving as a worked
example because the blockers were unusually structural and the
resolution patterns generalize.

**Scope.** 8 spec wrappers (`spec.div_poly`, `spec.divu_poly`,
`spec.rem_poly`, `spec.remu_poly`, `spec.divw_poly`,
`spec.divuw_poly`, `spec.remw_poly`, `spec.remuw_poly`) on top of 4
shared cores (`div_rem_poly`, `divu_remu_poly`, `divw_remw_poly`,
`divuw_remuw_poly`). Each core is 300–1000 lines of constraint-
algebra reasoning over `ZMod p`.

**Phase 1 — Foundation** (2026-05-05). Chip-local infrastructure
(`is_real_poly`, 8 `is_<variant>_poly`, `sp1_op_*_poly`,
`register_bounds_poly`, `ops_U64_b_c_poly`, `op_a_is_0_poly`,
`single_op_poly` via the 8-way `.val` arithmetic + `omega` engine).
Mechanical ports of the `Fin KB` helpers; landed in 6 commits.

**Phase 2 — 4 cores** (2026-05-05 to 2026-05-14). Each core port hit
three recurring blockers:

1. **Opening contradictions in the `(0,0)` and `(1,1)` rcases.** The
   `Fin KB` version closed by `decide`; over `ZMod p`, the `(1,1)`
   case needs `(2 : ZMod p) ≠ 1` (from `Fact (2^17 < p) ⇒ p > 2`).
   Lift the contradiction to a literal `Prop` hypothesis BEFORE the
   `simp_all` (which would otherwise collapse `Fact (2^17 < p)` to
   `Fact True` per pattern §1).

2. **`Nat → ℤ` cast residue in the `c = 0` branch.** Pretty-printed
   as `.cast` but actually the `Int.toNat` coercion. Closes via
   `push_cast [ZMod.cast_eq_val]; rfl` — see pattern §14.

3. **8-way `b_cry3` end-game.** Each `cry_i ∈ {0, 1}` carry bit
   must be bridged to `cry_i.val ≤ 1` explicitly before `omega` can
   close. New auxiliary `div_mod_decomposition_w_poly` (Common.lean)
   was needed at the `.val` level since `ZMod p` lacks native `% / /`.

**Phase 3 — 8 spec wrappers** (2026-05-14). Each wrapper is a
mechanical port of the `Fin KB` spec body with three structural
fixes:

- `Nat.cast_one` normalization for `↑(1 : ℕ) - is_word` vs literal
  `1 - is_word`.
- `msb_bridge_eq` for the `U16MSBOperation` output form mismatch
  (Nat-level `≥ 32768` vs ZMod-level `(32768 : ZMod p) ≤`).
- Per-arm trailing-goal reshape — generic `apply
  Word.isU64_of_cases_poly <;> simp_all` doesn't cover all 18 trailing
  isU64 shapes; first attempts under-closed by ~1 arm.

**Phase 4 — `correct_*_poly` × 8** (2026-05-15). The final blocker
was the 3-form `w_eq_msb_*` hypothesis variance across `all_goals`
side-goals in `divw_poly` / `remw_poly`: the same hypothesis appears
in 3 different syntactic shapes ((32768 : ZMod p) ≤ ?x / ?x.val ≥
32768 / raw `List.Forall` via `U16MSBOperation.spec.gen_poly`).
Resolved with per-side-goal `first | … | … | …` derivation chains
covering all 3 forms, plus a new `msb_arm_closer_poly` helper for
`Word.isU64_poly #v[x, y, m*65535, m*65535]` shapes. `div_poly` /
`rem_poly` had no sign-extension and needed only pre-extracted U64
limb bounds — surprisingly enough on its own.

**Verification.** `lake build` (full): 0 errors, 0 warnings. `lean_verify`
on all 8 `DivRem.Poly.correct_*_poly`: zero `sorryAx`. Standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`, plus the pre-existing
`combine_MUL_MULH_poly._native.bv_decide.ax_*` /
`extractLsb_is_toInt._native.bv_decide.ax_*` for the bv-using arms).

**Lessons that generalize.**

- **Pre-destructure U64 hypotheses first.** Always try
  `have ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64_poly is_U64_c`
  before adding more complex closer arms — it's often enough on its
  own and is much cheaper than adding msb closer arms.
- **`apply` to combinator-form hypotheses, not their unfolded form.**
  Use `apply eq_msb_b` + `change (32768 : ZMod p).val ≤ b3.val; rw
  [val_32768_zmod_p]; exact h` instead of trying to rewrite into the
  pre-simp form, which is no longer present after `simp [rem_*, c_*,
  b_msb_*] at *`.
- **`unfold` beats `rw [name]` for multi-occurrence rewrites.** When
  both LHS and RHS use `Word.toInt_poly`, `rw [Word.toInt_poly]` only
  unfolds the first occurrence; `unfold Word.toInt_poly` unfolds all.
- **`first | ... | ...` for hypothesis variance.** When the same
  hypothesis appears in N syntactic forms across `all_goals` side-
  goals, list each form as an alternative in a `first` chain rather
  than trying to normalize to one shape upfront.

**Post-migration sweep.** The Fin KB layer was deleted across 7
commits totaling ~3290 lines (`221fc0d` → `fcd36a2`). Inventory caught
3 "solo" lemmas (`tdiv_tmod_unique_full`, `_nat`,
`extractLsb_is_toInt`) that look chip-specific but are actually
field-agnostic and were kept. See `CONSTRAINT_REGEN.md`'s "Fin-KB
deletion-sweep template" for the generalized recipe.

## Appendix: Timeline and design rationale

Compressed from the original 2256-line session log. Major decision
points and the reasoning behind each.

### 2026-04-26 — Effort start

Baseline: `Fin KB` / `KB` / `KoalaBear` mentioned in 3,790 tokens
across the repo (352 in `SP1Foundations`, 1,189 in `SP1Operations`,
2,249 in `SP1Chips`; 766 hand-written, 3,024 in auto-gen
`*/Constraints.lean`). 57 `correct_*` theorems across 17 chip files.
Build wall-clock 727s (8508 jobs, clean).

KB-specific inverse literals in source: `2130673921 = (65536 : Fin
KB)⁻¹` (61 occurrences), `2122383361 = (256 : Fin KB)⁻¹` (67),
`1864368129 = (8 : Fin KB)⁻¹` (19), `1598029825 = (4 : Fin KB)⁻¹`
(14). `Field.lean` carries 14 hand-written KB-literal bridge lemmas
(`inv_*BB_eq[']` family) mapping these to symbolic
`(k : Fin KB)⁻¹` form.

### Phase 0 — Tracking + baseline (complete, 2026-04-26)

`docs/FIELD_GENERIC.md` created. Inventory of KB-references, KB
literals, KB-specific lemmas, and `correct_*` theorems captured.

### Phase 1 — Parameterize core datatypes (complete, 2026-04-26)

`AirInteraction (F : Type*)`, `SP1Constraint (F : Type*)`,
`SP1ConstraintList F` parameterized. No typeclass requirements at the
inductive level. `deriving DecidableEq` generates `DecidableEq
(SP1Constraint F)` parametrically.

`toProp` and `toStateProp` left at `SP1Constraint (Fin KB) → _` for
this phase. The `(F : Type*)` parameterization rippled into ~70 type-
position uses in auto-gen `Constraints.lean` files; rewrite baked into
`update_constraints.py`'s post-splice regex. `lake build` clean.

### Phase 2 — `Field.lean` reorganization + bridge audit (complete, 2026-04-26)

**Scope deflation discovered during execution.** The 14 KB-literal
lemmas in `Field.lean` are inherently KB-specific bridges — mathlib
already has the generic-side equivalents (`inv_eq_of_mul_eq_one_right`
etc.); the bridge is the part that depends on the prime. No
substitution possible.

Audit findings: only 5 operations invoke `inv_*BB_eq*` lemmas (`Add`,
`AddrAdd`, `Addw`, `Sub`, `Subw`). Zero operations use fully-
qualified `KoalaBear.*` names — bridge lemmas reach them via
root-scope simp. Only `LtOperationSigned` uses `decide`, and only for
`(1 : Fin KB) ≠ 0` (generic-shaped).

### Phase 3 — `SP1Operations` iff/spec classification (complete, 2026-04-26)

Per-file audit. 19 of 23 hand-written operation/compare/reader files
have iff lemmas; **all 19 are structurally generic** (proofs use
mathlib field tactics + KB-literal bridges). Phase 3 concluded as a
classification exercise, not a rewrite.

### Phase 4 — `SP1Chips` audit (complete, 2026-04-26)

Per-chip audit. Zero chips use fully-qualified `KoalaBear.*` names.
Three chips use `inv_*BB_eq*` bridges: `BranchChip` (12),
`JalrChip` (3), `LoadByteChip` (30). All other `Fin KB` references
in chips are in `Vector (Fin KB) N` signatures and `correct_*`
theorem statements (KB-typing by design).

### Phase 5 — Cleanup + retrospective (complete, 2026-04-26)

Headline change: the `(F : Type*)` parameter on
`SP1Constraint`/`AirInteraction`/`SP1ConstraintList`, the mechanical
`(Fin KB)` annotation rewrite in 48 auto-gen files, and the
`update_constraints.py` post-splice rewrite. The remaining "Phase
2/3/4" work was almost entirely an audit confirming the current code
was already field-generic in structure, with KB-coupling cleanly
localized to `Field.lean`'s bridge lemmas and the auto-gen literal
output.

### Sub-phase A — Upstream emits `(Fin KB)` directly (complete, 2026-04-26)

Followup after the user reversed the original "keep auto-gen
KB-bound" decision. `(Fin KB)` annotation moved into the upstream so
the `update_constraints.py` post-splice rewrite is unnecessary.
Changes in `crates/core/compiler/src/main.rs` and
`crates/{hypercube,core/compiler}/src/ir/{ast,func}.rs`. Verification:
full regen produces zero byte-diff against the existing tree.

Discovery: there are two `FuncDecl` types in upstream SP1 —
`compiler/src/ir/ast.rs` (operations) and an analogous struct in
`hypercube/src/ir/` (chips). The compiler's `to_output_lean_type` and
`to_lean_type` are dead-coded for our chip path; the hypercube
versions are the live ones.

### Sub-phase B — `ZMod p` parameterization (2026-04-26)

**Design**: `ZMod p` is mathlib's canonical prime-field carrier;
`ZMod p = Fin p` definitionally when `p > 0`. `[Fact (Nat.Prime p)]
+ [NeZero p]` synthesizes everything we need from `Field` /
`Fintype` / `DecidableEq`. `ZMod.val : ZMod p → ℕ` replaces
`Fin.val`. Missing: `LT (ZMod p)` and `Mod (ZMod p)` (mathlib
deliberately omits these because `ZMod 0 = ℤ` has different ordering
semantics). Resolution: rephrase `<`/`%` uses as `.val < c` /
`.val % c = 0` (Nat-level).

**Step 1 attempt — `.val` rephrase**: changed `toProp` line 68 from
`pc0 % 4 = 0` to `pc0.val % 4 = 0`. All four Store chips failed to
elaborate within 10 minutes (vs ~5s baseline). Some downstream simp
lemma reacts pathologically to the `.val % 4 = 0` shape. RAM
exhausted parallel builds. **Reverted.** Adopted ad-hoc `ZMod
instLT/instMod` instances dispatching via `.val`.

**Step 2 attempt — Parametric `Word.lean` lift**: change `Word.isU64`
from `Word (Fin KB) → Prop` to `{p : ℕ} [NeZero p] (Word (ZMod p)) →
Prop`. ~50 internal Word.lean lemmas broke because Lean's unifier
does NOT solve `Fin KB ≟ ZMod ?p` for `?p`, even though `ZMod KB =
Fin KB` definitionally. Direct annotation `@Word.isU64 KB _ w` works
but every call site would need this. **Reverted.**

**Step 3 attempt — Global `Fin KB → ZMod KB` rename**: tried atomic
rename in three files. Two showstopper issues:

1. Missing `HShiftLeft (ZMod KB)` instance. Lean core registers
   `Fin.instHShiftLeft : HShiftLeft (Fin n) Nat (Fin n)` but no
   analogue on `ZMod`. The 4 `shiftl_*BB_eq_one` lemmas fail to
   elaborate.

2. **`inv_mul_eq_one₀` doesn't unify on `ZMod p`.** After `rw
   [inv_*BB_eq']`, the goal is `4⁻¹ * x = 1 ↔ x = 4`. The pattern
   `?a⁻¹ * ?b = 1` from `inv_mul_eq_one₀` fails to match. Confirmed
   via `lean_run_code` on raw mathlib — not specific to our
   instances. Root cause: `(4 : ZMod p) ≠ 0` elaborates with `Zero`
   from `CommRing`'s path; `inv_mul_eq_one₀` expects `Zero` from
   `GroupWithZero`'s path. Two different paths to the same value;
   not unifiable by Lean's discrimination tree.

**Conclusion (preserved as a load-bearing finding):** the current
`Fin KB`-as-canonical-surface architecture is actually well-designed
for the typeclass-graph concerns. Switching the carrier to `ZMod KB`
directly hits mathlib's dual-path problem on every bridge lemma. **Do
not pursue the rename.** For a different prime, follow the parallel-
instance recipe in "How to instantiate at a different prime field"
above. Don't try to switch to `ZMod` as the surface type.

### Sub-phase B.4–B.11 — Polymorphic `_poly` cascade (2026-04-27 to 2026-04-28)

Pivoted from the rename strategy to the **additive `_poly`** strategy:
keep `Fin KB` defs in place and add `_poly` siblings parameterized
over `{p : ℕ} [Fact (Nat.Prime p)]` (+ `[Fact (2^17 < p)]`). Zero
chip-side churn; the polymorphic surface exists for future reuse.

Cascade order: Foundation (`SP1Foundations/`) → Operations
(`SP1Operations/`) → Chips (`SP1Chips/`). By 2026-04-28:
- Foundation 736 `_poly` occurrences across 7 files.
- Operations 21 ops in `update_constraints.py`'s `PARAMETRIC_OPS`
  dict, struct + auto-gen Constraints lifted to `(F : Type)` /
  `(F : Type*)`; hand-written iff_poly: 5 readers + 6 bridge-coupled
  ops + 5 spec_poly + LtUnsigned/Signed (partial).
- Build clean at B.11 (0 errors, 0 warnings, 8508 jobs).

### Track A — Operation-level `_poly` completion (2026-05-01)

All 5 outstanding `_poly` lemmas landed:
`LtOperationUnsigned.spec_poly`, `LtOperationSigned.spec.signed_poly`,
`LtOperationSigned.spec.branch_poly`, `BitwiseU16Operation.spec.{and,
or, xor}_poly`. Foundation + Operations complete.

### Track B — Chip-side migration attempt (2026-05-01, BLOCKED)

Tried using `(constraints Main).allHold_poly (p := KB)` ascription
with `Fin KB`-bound chip auto-gen. Failed at the destructure step:
`List.forall_append` couldn't unify `+++` at `Fin KB` with outer
`List.Forall` at `ZMod KB`. Definitionally equal but `simp`'s pattern
matcher doesn't bridge the parameter position. See
`PROOF_PATTERNS.md` "Fin KB ↔ ZMod KB defeq gap in `+++` distribution"
for the diagnostic.

### Track C1 — Chip-level parametric emission (2026-05-01 to 2026-05-05)

Resolution path for the Track B blocker. Extended
`update_constraints.py` with a `PARAMETRIC_CHIPS` dict (chip name →
universe + needs_coe_head). Per-chip opt-in. The chip's
`<Chip>/Constraints.lean` now returns `SP1ConstraintList F`
parametric in `(F : Type) [Field F]`. Pilot: SubChip 2026-05-01
(commit `e810b29`). Cascaded across Sub / Add / Subw / Addi /
Addw+Addiw / UType / Lt / Bitwise / Jal / Jalr / Store{Byte,Double,
Half,Word} / Load{Byte,Double,Half,Word} / LoadX0 / Mul / Branch /
DivRem / ShiftLeft / ShiftRight by 2026-05-15.

### Track C2 — Fin KB deletion sweep (2026-05-15)

Once all 24 chips had sorry-free `correct_*_poly` companions, the
parallel `Fin KB` layer was deletable. Initial 7 commits drained
Lt / Branch / ShiftLeft / Bitwise / Mul / 4×Load. Merge `e81f2f2`
brought in the other session's ShiftRight `_poly` proofs. Commits
`3db0db0` and `0f063b6` deleted ShiftRight's `Fin KB` tree. DivRem
sweep was 7 commits ending `fcd36a2`.

Total deletion: ~7000 lines net across `SP1Chips/`. After the sweep:
zero `Fin KB` in `SP1Chips/SP1Operations` (only doc comments
mention it). `lake build SP1Chips` clean.

### 2026-05-15 — Upstream compiler now emits `F` directly

The `update_constraints.py` post-processor's
`PARAMETRIC_CHIPS`/`PARAMETRIC_OPS` opt-in dicts were retired. The
upstream `sp1-constraint-compiler` (branch
`dtumad/field-generic-constraint-extraction`) rewritten to emit
field-generic Lean unconditionally. Changes in
`crates/hypercube/src/ir/{shape,expr,func,var,ast}.rs` plus the
binary at `crates/core/compiler/src/main.rs`. `update_constraints.py`
is now a verbatim writer (~200 lines deleted). End state of the
effort.

### Decisions log (key forks)

- **2026-04-26 (Phase 0):** Hybrid scope chosen over full polymorphism
  initially. Rationale: 17 chips with 57 `correct_*` theorems too
  much surface to rewrite in one effort.
- **2026-04-26 (Sub-phase A):** Compiler now emits `(Fin KB)`
  directly. Rationale: post-splice rewrite was a workaround; upstream
  emission is the structural fix.
- **2026-04-26 (Sub-phase B step 3):** Do NOT pursue global `Fin KB
  → ZMod KB` rename. Rationale: mathlib's instance graph for `ZMod
  p` reaches `Zero`/`MulZeroClass` through `CommRing` while
  `inv_mul_eq_one₀` reaches it through `GroupWithZero`; not
  unifiable. The current `Field (Fin KB) := ZMod.instField KB`-via-
  Fin architecture is well-designed for the typeclass-graph concerns.
- **2026-04-27 (Sub-phase B.4):** Pivot to additive `_poly` strategy.
  Rationale: zero chip-side churn; polymorphic surface exists for
  future reuse.
- **2026-05-01 (Track C1):** Chip-level parametric emission via
  `PARAMETRIC_CHIPS`. Rationale: resolves Track B's `+++` defeq
  blocker structurally; enables per-chip opt-in migration.
- **2026-05-15 (Track C2 + upstream rewrite):** Delete `Fin KB`
  layer chip-by-chip; retire `PARAMETRIC_*` dicts in favor of
  unconditional upstream emission. Rationale: with all `correct_*_poly`
  sorryAx-free, parallel layer is dead weight; upstream emission
  removes the per-chip opt-in maintenance burden.
