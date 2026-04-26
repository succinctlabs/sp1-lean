# Field-genericization effort

A running document for the multi-phase effort to lift this formalization off the
`Fin KB` (KoalaBear) field and onto an arbitrary prime field. Updated at every
phase boundary. The implementation roadmap is in
`~/.claude/plans/make-a-plan-to-soft-aho.md`.

## Goal

Make the SP1 AIR formalization parameterizable over `{F : Type*} [Field F]`
(plus minimal extras like `[Fact (Nat.Prime p)]`, `[LinearOrder F]`, and a
`F → ℕ` projection where the constraint semantics need it) so that a future
deployment over a different STARK field (BabyBear, Mersenne31, etc.) can reuse
the proof scaffold instead of forking it.

## Non-goals (this round)

- **Auto-generated `*/Constraints.lean` blocks stay `Fin KB`-typed.** The Rust
  `sp1-constraint-compiler` keeps emitting `Fin KB` and the literal
  `2130673921` (`= (65536 : Fin KB)⁻¹`). We do not modify the upstream
  compiler.
- **Top-level `correct_*` chip theorems stay instantiated at `Fin KB`.** We are
  not (yet) producing `correct_<chip>_generic` variants. The win is that any
  future generic variant has dramatically less to redo.
- **No second concrete field.** Success criterion is the type checker, not a
  parallel BabyBear instantiation. (BabyBear is a stretch goal documented in
  Phase 5 as forward guidance.)

## Layer map (target end state)

| Layer | File pattern | Field-status target | Why |
|---|---|---|---|
| Datatypes | `SP1Foundations/Constraint.lean`, `Word.lean` | Generic `(F : Type*) [Field F]` | Datatypes don't depend on the prime; only call sites do. |
| Field instances + computational lemmas | `SP1Foundations/Field.lean` (`KoalaBear` namespace) | KB-specific (by design) | These define `Fin KB` *as* a usable field; high-priority instances are perf-critical (see `docs/PERF_PATTERNS.md`). |
| Generic field lemmas | `SP1Foundations/Field.lean` (new `Field.Prime` namespace) | Generic | Provides `[Field F]`-level versions of `inv_16BB_eq'` etc. that the operation lemmas can call instead of the KB-specific ones. |
| Operation/Compare/Reader auto-gen | `SP1Operations/{Operation,Compare,Reader}/*/Constraints.lean` | KB-bound (auto-gen) | Compiler emits `Fin KB`. Constructor inference forces `F = Fin KB` at the call site. |
| Operation/Compare/Reader hand-written | `SP1Operations/{Operation,Compare,Reader}/*.lean` (top-level) | Iff lemmas remain over the KB-typed `def constraints`, but the **proof body** uses generic-field tactics only. | Removes accidental KB-coupling so a future generic version of the operation lemma is mostly a copy-paste with type variable. |
| Chip auto-gen | `SP1Chips/<Chip>/Constraints.lean` | KB-bound (auto-gen) | Same reason as operation auto-gen. |
| Chip top-level | `SP1Chips/<Chip>Chip.lean` | Statements KB-typed; proof bodies KB-coupling reduced | Same reason as operation hand-written. |
| Sail bridge | `SP1Foundations/SailM.lean` | Already field-agnostic | Bridges to `BitVec`/`Nat`; never touches `KB`. No work needed. |
| Custom tactics | `SP1Foundations/Tactics.lean` | Already generic | `bv_amicus_kerneli` is `BitVec`-width-parameterized; `get_elem_tactic` rebound to `norm_num1`; `mul_diff_one_neq` already takes `[Field α]`. No work needed. |

## Baseline metrics (start of effort, 2026-04-26)

### `Fin KB` / `KB` / `KoalaBear` token counts

| Directory | Total | Hand-written | Auto-gen (`*/Constraints.lean`) |
|---|---:|---:|---:|
| `SP1Foundations/` | 352 | 352 | 0 |
| `SP1Operations/` | 1,189 | 153 | 1,036 |
| `SP1Chips/` | 2,249 | 261 | 1,988 |
| **Total** | **3,790** | **766** | **3,024** |

The 766 hand-written occurrences are the upper bound on what this effort can
touch; the 3,024 auto-gen occurrences stay KB-bound by scope decision.

### KB-specific inverse literals in source

| Literal | Meaning | Occurrences | Files |
|---|---|---:|---|
| `2130673921` | `(65536 : Fin KB)⁻¹` | 61 | 17 files (Reader, AddOperation, AddrAdd, Addw, Sub, Subw, Branch, Jal, Field) |
| `2122383361` | `(256 : Fin KB)⁻¹` | 67 | (audit per-phase) |
| `1864368129` | `(8 : Fin KB)⁻¹` | 19 | (audit per-phase) |
| `1598029825` | `(4 : Fin KB)⁻¹` | 14 | (audit per-phase) |

Most occurrences are in auto-gen `*/Constraints.lean` files (KB-bound by
scope). The hand-written occurrences (`SP1Operations/Reader/*.lean`,
`SP1Operations/Operation/Add{w,rAdd}Operation.lean`, `SP1Foundations/Field.lean`)
are the migration surface for Phase 2/3.

### KB-specific lemmas in `Field.lean` (Phase 2 migration list)

Hand-written, `rfl`-only or KB-arithmetic-specific. All to be moved into a
`KoalaBear.Computational` sub-namespace and given generic `Field.Prime`
counterparts where possible.

| Lemma | Line | Generic substitute (proposed) | Migration status |
|---|---:|---|---|
| `shiftl_2BB_eq_one` | 57 | `(2^2 : F)⁻¹ * 2^2 = 1` (mathlib `inv_mul_cancel`) | TODO |
| `shiftl_3BB_eq_one` | 58 | same shape, `2^3` | TODO |
| `shiftl_8BB_eq_one` | 59 | same shape, `2^8` | TODO |
| `shiftl_16BB_eq_one` | 60 | same shape, `2^16` | TODO |
| `inv_2BB_eq` | 62 | `(2^2 : F)⁻¹ = 2^2 / 2^4 = ...` (use mathlib `inv_eq_of_mul_eq_one_right`) | TODO |
| `inv_3BB_eq` | 63 | same | TODO |
| `inv_8BB_eq` | 64 | same | TODO |
| `inv_16BB_eq` | 65 | same | TODO |
| `inv_2BB_eq'` | 67 | mathlib `eq_inv_of_mul_eq_one_left` | TODO |
| `inv_3BB_eq'` | 68 | same | TODO |
| `inv_8BB_eq'` | 69 | same | TODO |
| `inv_16BB_eq'` | 70 | same — **most-used** (5+ call sites) | TODO |
| `inv_mul_*BB_eq_one` | 72–75 | trivially `rfl` from generic `inv` | TODO |
| `mul_inv_*BB_eq_one` | 77–80 | same | TODO |
| `inv_mul_*BB_eq_iff` (4) | 82–89 | generic `mul_eq_one_iff_eq_inv` family | TODO |
| `inv_mul_*BB_eq_iff'` (4) | 91–98 | mul-comm wrap of above | TODO |
| `mul_inv_16BB_eq_one_iff` | 101 | mathlib `mul_inv_eq_one₀` | TODO |
| `inv_16BB_zero_or_one` | 104 | generic `Field` reasoning | TODO |

The `KoalaBear.Computational` namespace becomes the per-instance dispatch:
when a generic proof is instantiated at `Fin KB`, the simp set includes the
`Computational` lemmas to discharge the literal facts by `rfl`.

### KB instances to keep KB-specific (in `KoalaBear` namespace)

| Instance | Line | Why kept KB-bound |
|---|---:|---|
| `prime_KoalaBearPrime` | 26 | Concrete primality fact; instantiation surface for `[Fact (Nat.Prime KB)]`. |
| `Fact_BBPrime` | 28 | Wraps the above. |
| `NeZero KB` | 29 | Concrete fact. |
| `Field (Fin KB)` | 32 | This is what *makes* `Fin KB` a field (via `ZMod.instField`). |
| `NoZeroDivisors (Fin KB)` | 33 | Concrete via `Fin.noZeroDivisors_of_prime`. |
| 11 high-priority arithmetic instances | 40–49 | Perf-critical (see `docs/PERF_PATTERNS.md` — initial profile showed 779s typeclass inference in ShiftRight without these). |

### `correct_*` theorem inventory

57 `correct_*` theorems across 17 chip files (Add, Addi, Addw, Bitwise, Branch,
DivRem, LoadByte, LoadDouble, LoadHalf, LoadWord, Lt, Mul, ShiftLeft,
ShiftRight, Sub, Subw, UType). Spot-check command:

```bash
grep -rno "^theorem correct_\|^lemma correct_" SP1Chips | wc -l   # expect 57
```

### Build baseline

`lake build` pre-effort (2026-04-26):

- Wall-clock: **727 s** (12 min 7 s), 8508 jobs, EXIT=0.
- Errors: 0. Warnings: 0 (clean per CLAUDE.md's bar).
- Slowest jobs: `SP1Chips.ShiftRight.Constraints` (363 s),
  `SP1Chips.ShiftLeft.Constraints` (307 s),
  `SP1Chips.DivRem.Constraints` (268 s) — these are the auto-gen blocks that
  stay KB-bound, so genericization should not affect them.

## Phase progress

### Phase 0 — Tracking doc + baseline (in progress)

- [x] Create `docs/FIELD_GENERIC.md`
- [x] Capture KB-reference counts split hand-written vs auto-gen
- [x] List KB-specific inverse literals + files
- [x] List KB-specific lemmas in `Field.lean` with proposed generic substitutes
- [x] List KB-specific instances kept KB-bound by design
- [x] Inventory `correct_*` theorems
- [x] Record `lake build` wall-clock baseline (727 s)

### Phase 1 — Parameterize core datatypes (complete, 2026-04-26)

- [x] `AirInteraction (F : Type*)` — parameterized over `F` only; typeclass
  requirements live on the functions that consume it, not the inductive itself.
- [x] `SP1Constraint (F : Type*)` — same pattern.
- [x] `SP1ConstraintList F := List (SP1Constraint F)` (`@[reducible] def`).
- [x] `toProp` and `toStateProp` left at `SP1Constraint (Fin KB) → _` (Phase 3
  lifts these to generic `F` with `[LT F]`, `[Mod F]`, etc.).
- [x] `allHold` and `initialState` similarly KB-instantiated for now.
- [x] `update_constraints.py` post-splice rewrite added: rewrites bare
  `SP1ConstraintList` → `SP1ConstraintList (Fin KB)` after the constraint
  compiler emits Lean. Future regen produces field-typed annotations
  automatically.
- [x] 48 auto-gen `*/Constraints.lean` files updated mechanically (one-shot
  perl rewrite, same regex as the regen post-splice).
- [x] All 57 `correct_*` theorems still close. `lake build` clean
  (8508 jobs, EXIT=0, 0 errors, 0 warnings).
- [x] Build wall-clock: **537 s** vs 727 s baseline (caching helps; the cold
  rebuild cost is unchanged because the parameterization is type-level).

**Design notes:**

- The minimal change kept the inductives polymorphic over `(F : Type*)` with
  no typeclass requirements at the inductive level. `deriving DecidableEq`
  generates `instance [DecidableEq F] : DecidableEq (SP1Constraint F)` which is
  satisfied at `F = Fin KB`.
- Two `simp` lemmas in `Constraint.lean` (`toProp_assertZero`,
  `toProp_send_byte`) needed `(F := Fin KB)` annotations on the constructor
  calls because Lean can't always infer the type parameter from the constructor
  alone in a `simp` context.
- The `SP1ConstraintList F` parameterization rippled into ~70 type-position
  uses in auto-gen `Constraints.lean` files. The rewrite is mechanical and
  baked into the regen pipeline.
- Decision **deferred**: typeclass `FinLike F` vs explicit projection function
  for `.val : F → ℕ` in `toStateProp`. Punted to Phase 3 when we actually need
  the generic version.

### Phase 2 — Field.lean reorganization + bridge audit (complete, 2026-04-26)

**Scope deflation discovered during execution.** The original Phase 2 framing
("lift KB lemmas to generic counterparts") only partially holds. The 14
KB-literal lemmas in `Field.lean` (e.g. `inv_16BB_eq'` =
`2130673921 = 65536⁻¹`) are *not* substitutable with mathlib equivalents —
they're inherently KB-specific bridges from the SP1 constraint compiler's
literal output (`2130673921`) to a `Field`-generic form (`65536⁻¹`). Mathlib
already has the generic-side lemmas (`inv_eq_of_mul_eq_one_right`,
`mul_inv_eq_one₀`, etc.) — the bridge is the part that depends on the prime.

What was done:

- [x] Added top-of-file doc-comment explaining the two-role structure:
  concrete instances + KB↔generic bridges.
- [x] Added section markers (`### Generic field helpers`, `### KB ↔ generic-form
  bridges`, `### Integer helpers`) for discoverability.
- [x] Audited usage of KB-bridge lemmas across `SP1Operations`. **Only 5
  operations** invoke `inv_*BB_eq*` lemmas: `Add`, `AddrAdd`, `Addw`, `Sub`,
  `Subw`. **Zero** operations use fully-qualified `KoalaBear.*` names — the
  bridge lemmas reach them via root-scope simp.
- [x] Audited `decide`/`native_decide` usage in operation iff proofs. Only
  `LtOperationSigned` uses `decide`, and only for `(1 : Fin KB) ≠ 0` — a fact
  that holds in any `Fin p` with p ≥ 2, not deeply KB-specific.

**Implication for Phase 3.** Most of the 23 hand-written
`Operation`/`Compare`/`Reader` iff lemmas are already structurally generic —
their proofs use mathlib field tactics (`sub_eq_zero`, `mul_inv_eq_one₀`,
`omega`, `aesop`). Phase 3 becomes mostly a *classification* exercise (mark
each as structurally-generic vs. KB-tied) rather than a rewrite. The 5
operations using `inv_*BB_eq*` are the main KB-coupling surface; their proofs
remain valid because the bridge lemmas live in `Fin KB`-instantiated
`namespace KoalaBear` (root-scope `@[simp]` registration means generic-style
proofs still fire).

What did **not** happen (and why):

- **No `KoalaBear.Computational` sub-namespace introduced.** The current flat
  structure with section comments achieves the same discoverability without
  forcing every call site to qualify the names. Reconsider only if a second
  field gets added (Phase 5 forward guidance).
- **No `Field.Prime` namespace introduced.** There are no genuinely
  generic-but-not-in-mathlib lemmas to put there. If Phase 3 surfaces some,
  add the namespace then.
- **No call-site migration.** All current call sites already invoke the
  bridges in the right way; nothing to rewrite.

`lake build` clean after the doc-comment additions.

### Phase 3 — `SP1Operations` iff/spec lemma classification (complete, 2026-04-26)

The Phase 2 audit revealed Phase 3 is mostly classification, not rewriting.
The proofs in `SP1Operations` already use mathlib field tactics + the
KB-literal bridges from `Field.lean`; the bridges fire at the `Fin KB`
instantiation but the surrounding proof structure is field-generic. Only
`LtOperationSigned` uses `decide` and only on `(1 : Fin KB) ≠ 0`, a fact that
holds in any non-trivial `Fin p` field, so it's not deeply KB-tied.

Per-file classification:

| File | KB bridges | `decide` | Iff lemma class |
|---|---:|---:|---|
| `Compare/IsEqualWordOperation.lean` | 0 | 0 | **Structurally generic** |
| `Compare/IsZeroOperation.lean` | 0 | 0 | **Structurally generic** |
| `Compare/IsZeroWordOperation.lean` | 0 | 0 | **Structurally generic** |
| `Compare/LtOperationSigned.lean` | 0 | 2 | **Structurally generic** (`decide` on `(1:Fin KB)≠0` — generic-shaped) |
| `Compare/LtOperationUnsigned.lean` | 0 | 0 | **Structurally generic** |
| `Compare/U16CompareOperation.lean` | 0 | 0 | **Structurally generic** |
| `Operation/AddOperation.lean` | 1 | 0 | Structurally generic via `inv_16BB_eq'` bridge |
| `Operation/AddrAddOperation.lean` | 3 | 0 | Structurally generic via `inv_16BB_eq'` bridge |
| `Operation/AddwOperation.lean` | 1 | 0 | Structurally generic via `inv_16BB_eq'` bridge |
| `Operation/BitwiseU16Operation.lean` | 0 | 0 | **Structurally generic** |
| `Operation/SubOperation.lean` | 1 | 0 | Structurally generic via `inv_16BB_eq'` bridge |
| `Operation/SubwOperation.lean` | 1 | 0 | Structurally generic via `inv_16BB_eq'` bridge |
| `Operation/U16MSBOperation.lean` | 0 | 0 | **Structurally generic** |
| `Operation/U16toU8OperationSafe.lean` | 13 | 0 | Structurally generic, KB-bridge heavy (most-coupled file) |
| `Reader/ALUTypeReader.lean` | 6 | 0 | Statement KB-tied (`* 2130673921 < 256` overflow checks); proof structure generic |
| `Reader/CPUState.lean` | 2 | 0 | Same |
| `Reader/ITypeReader.lean` | 4 | 0 | Same |
| `Reader/JTypeReader.lean` | 2 | 0 | Same |
| `Reader/RTypeReader.lean` | 6 | 0 | Same |
| `Operation/BitwiseOperation.lean` | — | — | **No iff lemma** (chip uses auto-gen directly) |
| `Operation/MulOperation.lean` | — | — | **No iff lemma** (chip uses auto-gen directly) |
| `Operation/U16toU8OperationUnsafe.lean` | — | — | **No iff lemma** (chip uses auto-gen directly) |
| `Reader/ITypeReaderImmutable.lean` | — | — | **No iff lemma** (chip uses auto-gen directly) |

**Result:** 19 of 23 hand-written operation/compare/reader files have iff
lemmas, and **all 19 are structurally generic** — their proofs would carry
over to a different field given equivalent bridges (the per-prime `inv_*BB_eq*`
analogues) and the `< 256` overflow-check thresholds adjusted for the new
prime's modulus.

**No code changes** in Phase 3. The proof structure was already correct; the
audit was the deliverable. `lake build` unchanged from end of Phase 2.

**What this means for a future BabyBear instantiation** (forward-pointer to
Phase 5):

1. Provide BabyBear analogues of the 14 KB-literal bridge lemmas in
   `Field.lean` (different literal values, same shape).
2. Re-run the SP1 constraint compiler against the BabyBear field (the upstream
   Rust compiler emits different literals per prime).
3. Add the `update_constraints.py` post-splice rewrite for BabyBear's
   `SP1ConstraintList` annotation.
4. Re-prove the 19 operation iff lemmas at `Fin BabyBearPrime` — the proof
   tactics should carry verbatim (modulo the new bridges firing).
5. Re-prove the 57 chip `correct_*` theorems at the new field — same expected
   behavior.

The 4 operations without iff lemmas (`BitwiseOperation`, `MulOperation`,
`U16toU8OperationUnsafe`, `ITypeReaderImmutable`) are consumed directly from
their auto-gen `constraints` def in chip proofs, and would need analogous
chip-level treatment at the new field.

### Phase 4 — `SP1Chips` audit (complete, 2026-04-26)

Same finding as Phase 3: chips are largely free of explicit KB-coupling.

Per-chip audit:

| Chip | Size | KB bridges | `decide` | `KoalaBear.` |
|---|---:|---:|---:|---:|
| `AddChip` | 75 | 0 | 2 | 0 |
| `AddiChip` | 84 | 0 | 2 | 0 |
| `AddwChip` | 160 | 0 | 2 | 0 |
| `BitwiseChip` | 367 | 0 | 11 | 0 |
| `BranchChip` | 699 | **12** | 0 | 0 |
| `DivRemChip` | 381 | 0 | 16 | 0 |
| `JalChip` | 107 | 0 | 1 | 0 |
| `JalrChip` | 208 | **3** | 0 | 0 |
| `LoadByteChip` | 482 | **30** | 2 | 0 |
| `LoadDoubleChip` | 289 | 0 | 5 | 0 |
| `LoadHalfChip` | 492 | 0 | 25 | 0 |
| `LoadWordChip` | 504 | 0 | 17 | 0 |
| `LtChip` | 271 | 0 | 4 | 0 |
| `MulChip` | 288 | 0 | 10 | 0 |
| `ShiftLeftChip` | 232 | 0 | 8 | 0 |
| `ShiftRightChip` | 472 | 0 | 16 | 0 |
| `StoreByteChip` | 119 | 0 | 0 | 0 |
| `StoreDoubleChip` | 120 | 0 | 0 | 0 |
| `StoreHalfChip` | 120 | 0 | 0 | 0 |
| `StoreWordChip` | 121 | 0 | 0 | 0 |
| `SubChip` | 76 | 0 | 1 | 0 |
| `SubwChip` | 82 | 0 | 1 | 0 |
| `UTypeChip` | 211 | 0 | 3 | 0 |

**Findings:**

- **Zero chips use fully-qualified `KoalaBear.*` names.** All KB-specific
  lemmas reach proofs via root-scope `@[simp]` registration.
- **Three chips use `inv_*BB_eq*` bridges**: `BranchChip` (12),
  `JalrChip` (3), `LoadByteChip` (30). These are the main KB-coupling surface
  in `SP1Chips`. Each bridge call is the same pattern: rewriting the
  constraint compiler's literal output to `65536⁻¹` form via
  `simp [..., inv_16BB_eq']`. Same shape as the operation lemmas — the
  coupling lives in the bridge call, not the surrounding proof.
- **`decide`/`native_decide` calls are generic-shape**, not KB-specific. The
  most common pattern is `Fin.BitVec_ofNat_add_eq_add_ofNat _ 4 (by decide)
  (by omega)` — the `by decide` discharges a `Decidable` side condition
  (likely a small `Nat`/`Fin` bound) of a generic mathlib lemma. These would
  carry over to any `Fin p` instantiation unchanged.
- **`Fin KB` references in chips** are primarily in `Vector (Fin KB) N` type
  signatures for `Main` rows and in `correct_*` theorem statements — KB-typing
  by design, not coupling we want to remove.

**No code changes** in Phase 4. The chip proofs were already largely free of
KB-coupling beyond what's expected from the auto-gen + bridge pattern. `lake
build` unchanged from end of Phase 2.

**Three chips to revisit on a BabyBear instantiation** (Phase 5
forward-pointer): `BranchChip`, `JalrChip`, `LoadByteChip` — wherever the
bridge call sites appear, swap `inv_16BB_eq'` for the BabyBear analogue.

### Phase 5 — Cleanup & retrospective (complete, 2026-04-26)

**Final state of the effort.**

- [x] Audited unused KB-specific lemmas in `Field.lean`. Of the 14 hand-written
  KB-literal lemmas:
  - `inv_16BB_eq'` is heavily used (7 calls across 5 operation files).
  - `inv_16BB_eq` (no apostrophe) and `inv_{2,3,8}BB_eq[']` (6 lemmas) have 0
    named uses outside `Field.lean`. They form a symmetric family with
    `inv_16BB_eq'` and exist for completeness; **kept** to avoid a regression
    risk if a new chip needs them, since re-deriving the literal value is
    annoying. Maintenance cost is near zero.
  - The `@[simp]`-attributed lemmas (`shiftl_*BB_eq_one`,
    `inv_mul_*BB_eq_one`, `mul_inv_*BB_eq_one`, `inv_mul_*BB_eq_iff`,
    `mul_inv_16BB_eq_one_iff`, `inv_16BB_zero_or_one`) fire implicitly via the
    simp set. **Kept** because removing them risks silent proof breakage in
    chips that rely on the simp normal form without naming the lemma.
- [x] Final layer-map snapshot (see "Layer map" near the top of this doc — it
  was written for the target end state and matches what we landed at).
- [x] BabyBear (or other prime) instantiation forward-guidance — see "How to
  instantiate at a different prime field" below.
- [x] Pruned stale memory note `project_is_trusted_removal_stops.md` — the
  `is_trusted` cleanup is complete (CLAUDE.md confirms; `grep -c '^stop$'
  SP1Chips/**/*.lean = 0`).

**Aggregate token-count change:** the effort changed almost no source code by
volume. The headline change is the `(F : Type*)` parameter on
`SP1Constraint`/`AirInteraction`/`SP1ConstraintList`, the mechanical
`(Fin KB)` annotation rewrite in 48 auto-gen files, and the `update_constraints.py`
post-splice rewrite. The remaining "Phase 2/3/4" work was almost entirely an
audit that documented the current code as already field-generic in structure,
with the KB-coupling cleanly localized to `Field.lean`'s bridge lemmas and the
auto-gen literal output.

**`lake build` final:** clean, 0 errors, 0 warnings (matches baseline).

## How to instantiate at a different prime field

Recipe for adding a parallel `Fin <NewPrime>` instantiation (e.g. BabyBear =
`2^31 - 2^27 + 1`):

1. **Add the new prime's instance block in `SP1Foundations/Field.lean`.**
   Mirror the `KoalaBear` namespace: prime fact (`Fact (Nat.Prime <NewPrime>)`),
   `NeZero`, `Field` (via `ZMod.instField`), `NoZeroDivisors`, and the 11
   high-priority arithmetic instances. The arithmetic instances are
   perf-critical — without them, typeclass synthesis explodes (see
   `docs/PERF_PATTERNS.md`).

2. **Add new bridge lemmas mirroring `inv_*BB_eq[']`, `shiftl_*BB_eq_one`,
   etc., for the new prime.** Compute the literal value of `(2^k)⁻¹ mod
   <NewPrime>` for `k ∈ {2, 3, 8, 16}`, then state `(literal :
   Fin <NewPrime>)⁻¹ = 2^k` and friends. The lemma bodies all close by `rfl`
   or `inv_eq_of_mul_eq_one_right (by rfl)`. **At minimum** you need the
   `_16` family (the `_2/_3/_8` families are present for symmetry but unused
   in the current proofs).

3. **Run the SP1 constraint compiler against the new field.** The upstream
   Rust `sp1-constraint-compiler` emits `Fin KB` literally and computes the
   inverse-of-`2^k` literal for KB. Either:
   - Modify the compiler to be prime-parametric (out of scope of the work
     captured in this doc — would touch `SP1_DIR`).
   - Or run the compiler with the new prime configured, then post-process the
     output to substitute the field type and literal values via
     `update_constraints.py` (the existing post-splice rewrite is a starting
     point).

4. **Update `update_constraints.py`** to also rewrite `Fin KB` →
   `Fin <NewPrime>` and the literal values when the target field is the new
   one. Keep the KB and new-prime rewrites independent (e.g. via a CLI
   toggle).

5. **Re-prove the 19 operation iff lemmas at the new field.** They're
   structurally generic per the Phase 3 audit; expect the proof tactics to
   carry verbatim once the new bridges fire.

6. **Re-prove the 57 chip `correct_*` theorems.** Per the Phase 4 audit, the
   only KB-coupling beyond the auto-gen is in `BranchChip`, `JalrChip`, and
   `LoadByteChip`'s use of `inv_*BB_eq*` bridges — swap these for the
   new-prime analogues. The `decide`/`omega` side-condition discharges should
   carry over.

7. **Sail bridge** (`SP1Foundations/SailM.lean`) is field-agnostic — the
   bridge wraps `BitVec 64` regardless of which `Fin p` is on the constraint
   side. No changes expected.

**Estimated effort for a BabyBear instantiation given this groundwork:**
1–2 sessions for the field setup and bridges (steps 1–4); 2–4 sessions to
re-prove operations + chips (steps 5–6) since the structure is preserved.

## Known KB leaks (to be filled in as Phase 3/4 progresses)

For each item: file:line, what blocks generalization, and what would be needed
to lift it (e.g., "needs `CharP F p` with `p > 2^16`", "needs `Fin`-specific
`.val` projection", "needs `decide`-strength on the concrete prime").

*(empty until Phase 3 starts)*

## Decisions log

- **2026-04-26** (Phase 0): Hybrid scope chosen over full polymorphism. Rationale: 17 chips with 57 `correct_*` theorems is too much surface to rewrite in one effort; keeping the chip statements KB-typed lets the auto-gen pipeline keep working unchanged.
- **2026-04-26** (Phase 0): Compiler stays KB-bound. Rationale: avoids cross-repo coordination; the generic-field win lives at the layer above the auto-gen, where call sites force `F = Fin KB` through constructor inference.
- **2026-04-26** (Phase 0): No second concrete field this round. Rationale: BabyBear instantiation can be done in a follow-up effort once the generic surface stabilizes; the Phase 5 forward-guidance section will document the recipe.
