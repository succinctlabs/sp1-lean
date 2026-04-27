# Field-genericization effort

A running document for the multi-phase effort to lift this formalization off the
`Fin KB` (KoalaBear) field and onto an arbitrary prime field. Updated at every
phase boundary. The implementation roadmap is in
`~/.claude/plans/make-a-plan-to-soft-aho.md`.

## Next session pickup

**Status as of 2026-04-26**: Phases 0-5 + Sub-phase A complete + sub-phase B
**partial: ad-hoc instances landed**. Sub-phase B Steps 1-2 attempted with
key empirical findings (see "Sub-phase B — Step 1/2 attempt" below). `lake
build` clean.

**Concrete sub-phase B progress this session**:

- Added `instance ZMod.instLT (p : ℕ) [NeZero p]` and `instance ZMod.instMod`
  to `SP1Foundations/Field.lean`. These let constraint semantics use `<` /
  `%` syntax on `ZMod p` field elements (gated by `[NeZero p]`) and
  definitionally agree with `Fin.instLT` / `Fin.instMod` at `p := KB`. They
  are the foundation that future lifts of `toProp` / `toStateProp` to
  `SP1Constraint (ZMod p)` will build on.

**Findings that change the plan from the original design (B.1)**:

- **Original design Step 1 (`.val`-rephrase)** is unworkable. Rephrasing
  `pc0 % 4 = 0` → `pc0.val % 4 = 0` in `toProp` causes the four Store chips
  to time out (>10 min vs ~5s baseline) due to a pathological simp expansion
  in chip-side `simp [SP1Constraint.toProp, ...]`. **Reverted.** The design
  doc's "Alternative" path (ad-hoc `LT`/`Mod` instances on `ZMod p`) is the
  way forward — and now landed.
- **Original design Step 2 (parametric `{p : ℕ} [NeZero p]` lift of Word.lean)**
  fails dot-notation unification pervasively. When chip code calls `w.isU64`
  on `w : Word (Fin KB)` and `Word.isU64` expects `Word (ZMod ?p)`, Lean's
  unifier does not solve `?p := KB` from `Fin KB ≟ ZMod ?p`, even though
  `ZMod KB = Fin KB` definitionally. **Tested** via partial Word.lean lift —
  ~50 internal lemmas broke. **Reverted.**
  - Direct (non-parametric) ZMod KB calls work fine via dot notation
    (verified via `lean_run_code`), but that's just a rename, not a
    polymorphism win.
  - Workarounds for the parametric case would need explicit `@`
    annotations at every call site, or replacement of dot notation with
    explicit `Word.isU64 (p := KB) w` form. Neither is acceptable scope.

**To continue sub-phase B**, the recommended next session sequence:

1. Read "Sub-phase B — Step 1/2 attempt" findings below.
2. Decide: do you want to push harder on the parametric Word.lean lift
   (will likely require either a `class HasNatVal F` typeclass with
   `outParam` to force unification, or a wholesale rewrite to use explicit
   `@` annotations)? Or accept the more limited scope: the `LT`/`Mod`
   instances are landed, and full Word.lean lift is deferred to a future
   effort (perhaps coupled with the upstream compiler change in step 3).
3. If pushing harder: investigate `outParam` and `instance` resolution
   tactics. The Sail bridge in `SP1Foundations/SailM.lean` is field-agnostic
   and unaffected.
4. **Step 3+** (cross-repo, deferred): Update upstream constraint compiler
   to emit `ZMod p` and symbolic `(2^k : ZMod p)⁻¹`.

## Goal

Make the SP1 AIR formalization parameterizable over `{F : Type*} [Field F]`
(plus minimal extras like `[Fact (Nat.Prime p)]`, `[LinearOrder F]`, and a
`F → ℕ` projection where the constraint semantics need it) so that a future
deployment over a different STARK field (BabyBear, Mersenne31, etc.) can reuse
the proof scaffold instead of forking it.

## Scope (as of 2026-04-26 — Phases 0-5 + Sub-phase A done)

- **Datatypes (`SP1Constraint`, `AirInteraction`, `SP1ConstraintList`) are
  parameterized** over `(F : Type*)` (no typeclass requirements at the
  inductive level).
- **Auto-generated `*/Constraints.lean` blocks emit `(Fin KB)` annotations
  directly** from the upstream constraint compiler (sub-phase A; the
  post-splice rewrite was removed). The upstream still emits the inverse
  literal `2130673921` (KB-specific). Sub-phase B would change both.
- **Top-level `correct_*` chip theorems stay instantiated at `Fin KB`.** Not
  (yet) producing `correct_<chip>_generic` variants.
- **No second concrete field instantiated yet.** Success criterion is the
  type checker, not a parallel BabyBear instantiation. (BabyBear is a
  stretch goal documented in "How to instantiate at a different prime
  field" as forward guidance.)
- **Sub-phase B (full `F`/`ZMod p` parameterization with chip-side
  variable declaration) is designed but not implemented.** See
  "Sub-phase B — Design" below and the "Next session pickup" pointer at
  the top of this doc.

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
  automatically. **(Removed in Sub-phase A — see below; the upstream now
  emits the annotation directly.)**
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

## Sub-phase A — Upstream emits `(Fin KB)` directly (complete, 2026-04-26)

Followup to Phase 1 after the user reversed the original "keep auto-gen
KB-bound by leaving the upstream alone" decision. The `update_constraints.py`
post-splice rewrite was a workaround; this sub-phase moves the `(Fin KB)`
annotation into the upstream so the rewrite is unnecessary.

**Changes in `../sp1`** (branch `dtumad/constraint-extractor-update`):

| File | Change |
|---|---|
| `crates/core/compiler/src/main.rs:101` | Chip-level outer signature: `: SP1ConstraintList :=` → `: SP1ConstraintList (Fin KB) :=` |
| `crates/core/compiler/src/ir/ast.rs:454-469` | Operation-level `to_output_lean_type()`: KoalaBear → `Fin KB`; bare `SP1ConstraintList` → `SP1ConstraintList (Fin KB)` |
| `crates/core/compiler/src/ir/ast.rs:660-679` | Operation-level `to_lean_type()` for `Ty::Expr`/`Ty::Word`/`Ty::ArrWordSize`/`Ty::ArrWordByteSize`: KoalaBear → `(Fin KB)` |
| `crates/core/compiler/src/ir/ast.rs:910/939/957` | Let-binding type annotations in operation bodies: `KoalaBear` → `Fin KB` |
| `crates/core/compiler/src/ir/ast.rs:1131` | `let CS{i} : SP1ConstraintList := ` → `let CS{i} : SP1ConstraintList (Fin KB) := ` (operation call sites in operation bodies) |
| `crates/hypercube/src/ir/ast.rs:251` | `let CS{i} : SP1ConstraintList := ` → `let CS{i} : SP1ConstraintList (Fin KB) := ` (operation call sites in chip bodies — separate `FuncDecl` shape) |
| `crates/hypercube/src/ir/func.rs:75-79` | `to_output_lean_type()` (the live one for chip-level emission): `SP1ConstraintList` → `SP1ConstraintList (Fin KB)` for both `Shape::Unit` and tuple cases |

**Changes in this repo**: removed the post-splice regex rewrite from
`update_constraints.py`. The upstream is now self-sufficient.

**Verification**: full regen across all 48 `Constraints.lean` files via
`SP1_DIR=… python3 update_constraints.py` produces **zero byte diff** against
the existing tree (compared via `md5sum`). `lake build` clean.

**Discovery during execution**: there are **two** `FuncDecl` types in the SP1
upstream — `compiler/src/ir/ast.rs` (operations) and an unnamed analogous
struct in `hypercube/src/ir/` (chips). The compiler's `to_output_lean_type`
and `to_lean_type` are dead-coded for our chip path; the hypercube versions
are the live ones. Updated both for safety so future operation paths that
exercise the compiler's strings don't silently emit broken Lean.

## Sub-phase B — Step 1/2 attempt (2026-04-26)

**Outcome**: ad-hoc `ZMod` instances landed; `.val` rephrase and parametric
Word.lean lift attempted and reverted. Detailed below for future sessions.

### What landed

`SP1Foundations/Field.lean`:
```lean
namespace ZMod
instance instLT (p : ℕ) [NeZero p] : LT (ZMod p) where
  lt x y := x.val < y.val
instance instMod (p : ℕ) [NeZero p] : Mod (ZMod p) where
  mod x y := ((x.val % y.val : ℕ) : ZMod p)
end ZMod
```

These instances dispatch via `.val` projection. At `p := KB`,
`ZMod KB = Fin KB` definitionally, and these instances agree with
`Fin.instLT` / `Fin.instMod`. They unblock the future lift of
`toProp`/`toStateProp` to `SP1Constraint (ZMod p)` from needing the `.val`
rephrase that the original design called for.

### What failed and why

**Attempt 1**: `.val`-rephrase in `Constraint.lean` (the design's "Step 1").
Edited `toProp` line 68 from `pc0 % 4 = 0` to `pc0.val % 4 = 0`. Updated
matching Reader iff RHS in 4 reader files, plus `Branch/Constraints.lean:248`
and `JalChip.lean:65` to consume the new shape. Build attempted.

- `Branch/Constraints.lean`, `JalChip.lean` and the 4 readers built clean.
- All four Store chips (`StoreByteChip`, `StoreDoubleChip`, `StoreHalfChip`,
  `StoreWordChip`) **failed to elaborate within 10 minutes** (vs ~5s
  baseline). The slowdown came from chip-side `simp [SP1Constraint.toProp,
  ITypeReaderImmutable.constraints, ...]` calls (e.g. `StoreByteChip.lean:60`)
  that consume the program-interaction predicate. Some downstream simp lemma
  reacts pathologically to the `.val % 4 = 0` shape.
- Resource impact: each Store chip consumed ~18 GB RAM and 96% CPU during
  the spin. Parallel `lake build` exhausted system memory.
- **Reverted.** Adopted the design doc's "Alternative" path: ad-hoc instances
  on `ZMod p` (above).

**Attempt 2**: Parametric Word.lean lift — change `Word.isU64` from
`Word (Fin KB) → Prop` to `{p : ℕ} [NeZero p] (Word (ZMod p)) → Prop`. Other
callers stay at `Fin KB`; rely on `ZMod KB = Fin KB` definitional equality
+ unification to solve `?p := KB`.

- ~50 internal Word.lean lemmas broke with errors like
  `Application type mismatch: argument w has type Word (Fin 2130706433) but
  is expected to have type Word (ZMod ?m.3)`.
- Lean's unifier does **not** solve `Fin KB ≟ ZMod ?p` for `?p` even though
  `ZMod KB = Fin KB` definitionally. The unifier treats this as a
  higher-order pattern it can't invert without a hint. Direct annotation
  `@Word.isU64 KB _ w` works but every call site would need this.
- Symmetric test: `lean_run_code` confirmed that direct application
  `Vector_isU16 w` (no dot notation) DOES unify `?p := KB` from `w : Vector
  (Fin KB) 4`. The failure is specific to dot notation in lemma proofs that
  call other dot-notation lemmas in chains.
- **Reverted.**
- Workarounds for a future session:
  - Rewrite all dot-notation uses as explicit `@` calls (high churn).
  - Introduce `class HasNatVal (F : Type*)` with `outParam` and instances
    for `Fin n` and `ZMod p`, generalize Word.lean over the class instead
    of `ZMod p`. Adds typeclass resolution cost.
  - Lift only signatures from `Fin KB` to `ZMod KB` (specific, not
    parametric). This works but achieves nothing semantically — it's a
    rename. Worth doing only if it improves discoverability for future
    BabyBear instantiation.

### Verified facts to preserve for future sessions

- `ZMod KB = Fin KB` is a **reducible** definitional equality (mathlib's
  `ZMod` is `def ZMod : ℕ → Type | 0 => ℤ | n+1 => Fin (n+1)`).
- `KoalaBear.Fact_BBPrime` (`Field.lean:51`) and `KoalaBear : NeZero KB`
  (`Field.lean:52`) are root-scope, so `[Fact (Nat.Prime KB)]` and
  `[NeZero KB]` synthesize automatically.
- The `LT`/`Mod` instances above don't conflict with `Fin.instLT`/`Fin.instMod`
  at `p := KB` because they're on different (but definitionally equal)
  types — synthesis dispatches to `Fin.*` for `Fin n` queries and to the
  new `ZMod.*` for `ZMod n` queries.
- The 11 high-priority `Fin KB` arithmetic instances at `Field.lean:63-72`
  are unaffected by the `ZMod` instances and continue to dominate dispatch
  for `Fin KB`-typed expressions.

## Sub-phase B — Step 3 attempt: global `Fin KB` → `ZMod KB` rename (2026-04-26, REVERTED)

**Outcome: rename is structurally infeasible as a pure surface-level
substitution.** The "achieves nothing semantically — it's a rename" framing
above (line 549–552) was wrong. `Fin KB` and `ZMod KB` have **different
typeclass instance graphs in mathlib**, and the difference breaks `simp`
and `rw` discrimination-tree matching even though the underlying types are
definitionally equal.

### What was attempted

Atomic rename of `Fin KB` → `ZMod KB` in three files (lockstep, since the
high-priority `Fin KB` instances at `Field.lean:80-89` intercept literal
elaboration and produce `HAdd (ZMod KB) (Fin KB)` mismatches if Constraint
moves alone):

1. `SP1Foundations/Constraint.lean` — all `Fin KB` → `ZMod KB` in
   `toProp`/`toStateProp`/`allHold`/`initialState` signatures + 2 simp
   lemmas.
2. `SP1Foundations/Field.lean` — 12 instances + 38 bridge lemmas + docstring.
3. `SP1Operations/Compare/IsZeroOperation/Operation.lean` — pilot file.

### What broke and why

**Issue 1: Missing `HShiftLeft (ZMod KB)` instance.** Lean core registers
`Fin.instHShiftLeft : HShiftLeft (Fin n) Nat (Fin n)` but no analogue on
`ZMod`. The 4 `shiftl_*BB_eq_one` lemmas (`Field.lean:108-111`) — which use
`(literal : Fin KB) <<< n = 1` — fail to elaborate after the rename
(`failed to synthesize instance of type class HShiftLeft (ZMod KB) ℕ ?m`).

These 4 lemmas have **zero callers** (no chip auto-gen produces `<<<` on
field elements; `<<<` only appears on `Nat`/`BitVec` in `LoadDoubleChip`
and `ShiftLeft/Constraints.lean`). They could be deleted, but that's
papering over the underlying instance-graph divergence.

**Issue 2 (the showstopper): `inv_mul_eq_one₀` doesn't unify on `ZMod p`.**
The 4 `inv_mul_*BB_eq_iff` proofs (`Field.lean:134-141`) all do:

```
rw [inv_*BB_eq', inv_mul_eq_one₀ (by decide), eq_comm]
```

After the first rewrite the goal is `4⁻¹ * x = 1 ↔ x = 4`. The pattern
`?a⁻¹ * ?b = 1` from `inv_mul_eq_one₀` then **fails to match** with error
"Did not find an occurrence of the pattern". Confirmed via `lean_run_code`
on raw mathlib — the failure is **not specific to our custom instances**.
Root cause from the error message:

- `(4 : ZMod p) ≠ 0` elaborates with `Zero` from
  `MulZeroClass.toZero` of `NonUnitalNonAssocSemiring` of `NonUnitalCommRing`
  of `CommRing`.
- `inv_mul_eq_one₀` expects `Zero` from `MulZeroClass.toZero` of
  `MulZeroOneClass` of `MonoidWithZero` of `GroupWithZero`.
- These are two different paths to the same `Zero (ZMod p)` synthesized
  value. They are *not* unifiable by Lean's discrimination tree.

The same lemmas worked on `Fin KB` because the registered
`Field (Fin KB) := ZMod.instField KB` routes the `Fin KB` instance
synthesis through the `ZMod` instance graph, but the consumer reaches
`Inv`/`Zero` through the `Field`-derived path that *does* match
`GroupWithZero`'s normal form. When the type is nominally `ZMod p`,
mathlib's `CommRing`-first instance graph wins for `OfNat (ZMod p) n`
and routes `Zero` through the wrong path.

**Issue 3: `aesop` can't close `inv_16BB_zero_or_one`.** The lemma
(`Field.lean:155`) closes by `aesop` on `Fin KB` but the same tactic
can't close it on `ZMod KB` — same instance-graph divergence makes the
internal lemmas aesop reaches for non-applicable.

### Conclusion

The current `Fin KB`-as-canonical-surface architecture is actually
well-designed for the typeclass-graph concerns. `Field (Fin KB) :=
ZMod.instField KB` threads the `ZMod p` algebraic structure through the
`Fin n` carrier in a way that aligns with mathlib lemma normal forms.
Switching the carrier to `ZMod KB` directly hits mathlib's dual-path
problem on every bridge lemma and likely on hundreds of chip proofs.

**Recommendation: do not pursue the rename.** For a future BabyBear
instantiation, follow the existing recipe (parallel `Fin <NewPrime>`
instance block + bridges per "How to instantiate at a different prime
field" near the bottom of this doc). Don't try to switch to `ZMod` as
the surface type.

### Verified-fact correction

The 2026-04-26 fact "lift only signatures from Fin KB to ZMod KB ... works
but achieves nothing semantically — it's a rename" (line 549–552) is
**incorrect**. The rename does NOT type-check end-to-end because the
mathlib instance graph for `ZMod p` reaches `Zero`/`MulZeroClass` through
a different path than the `Field`-derived one that bridge lemmas like
`inv_mul_eq_one₀` use. Future sessions: ignore that line; consult this
section instead.

### Path forward (if anyone revisits)

The only viable rename strategy would be to define every bridge lemma
with explicit `Field`-instance routing (not via mathlib's `inv_mul_eq_one₀`
etc.) so that the discriminator path is uniform. That's a from-scratch
rewrite of all 14+ bridges and any chip simp call that depends on them.
Cost dominates the value. Recommend not doing it.

## Sub-phase B — Design (deferred; not implemented this session)

Sub-phase B would lift the auto-gen output from `Fin KB`-typed to fully
`F`-typed, with chip and operation files declaring `variable {F : Type*}
[Field F]` (plus extras) and instantiating `F := Fin KB` at the top-level
`correct_*` theorem layer. This would deliver true field-genericity at the
auto-gen layer, completing what the hybrid scope deferred.

The work breaks into three independent design questions, each of which has a
recommended answer below.

### B.1: Use `ZMod p` directly (mathlib-canonical)

Investigated 2026-04-26. The right abstraction is mathlib's `ZMod p`, not a
new `PrimeFieldFin` typeclass. `Field.lean:54` already carries the TODO
comment `-- dt: Wouldn't need this if ZMod was the fundamental object for us`,
and `instance : Field (Fin KB) := ZMod.instField KB` is already routing
through `ZMod`. Sub-phase B can complete that direction.

**What `ZMod p` gives us out-of-the-box**:

- `ZMod p = Fin p` *definitionally* when `p > 0` (mathlib's definition).
- `Field (ZMod p)` via `ZMod.instField` with `[Fact (Nat.Prime p)]`.
- `CharP (ZMod p) p`, `Fintype (ZMod p)` (with `NeZero`), `DecidableEq`,
  `NeZero`, `NoZeroDivisors` (via `Field → IsDomain → NoZeroDivisors`).
- `ZMod.val : ZMod p → ℕ` (the natural-number representative, replaces `Fin.val`).
- `ZMod.val_lt : ∀ x, x.val < p` (requires `[NeZero p]`).
- `ZMod.val_injective`, `ZMod.cast`, etc.

**What's missing and how to fix it** (verified via `lean_run_code`):

- `LT (ZMod p)` and `Mod (ZMod p)` do **not** synthesize for generic `p`.
  Mathlib intentionally omits these because `ZMod 0 = ℤ` and `ZMod (n+1) =
  Fin (n+1)` have different ordering semantics, so a uniform instance would
  be misleading.

  **Fix (preferred): rephrase `toProp`/`toStateProp` to use `.val`-level
  comparisons.** The current `op_a < 32` and `pc0 % 4 = 0` checks are
  semantically about the *natural-number representation* of the field
  element, not about a field-level order (which doesn't exist meaningfully on
  a finite field). Replace:

  ```lean
  -- Before (Fin KB-level)
  ∧ op_a < 32
  ∧ pc0 % 4 = 0

  -- After (Nat-level via ZMod.val)
  ∧ op_a.val < 32
  ∧ pc0.val % 4 = 0
  ```

  Mathematically equivalent (both check the natural representation), but more
  explicit and avoids any non-canonical typeclass instance. Verified via
  `lean_run_code`: this form elaborates over generic `[NeZero p]` `ZMod p`
  with no extra instances needed.

  **Alternative (if proof-tactic compatibility forces it): ad-hoc instances**.
  Only consider if the rephrasing breaks too many existing chip proofs:

  ```lean
  namespace ZMod
  instance instLT (p : ℕ) [NeZero p] : LT (ZMod p) where
    lt x y := x.val < y.val
  instance instMod (p : ℕ) [NeZero p] : Mod (ZMod p) where
    mod x y := ((x.val % y.val : ℕ) : ZMod p)
  end ZMod
  ```

  Both options preserve `Fin KB` semantics at the `p := KB` instantiation,
  since `ZMod KB = Fin KB` definitionally and `(x : Fin KB).val = (x : ZMod KB).val`.

**Recommended parameterization shape**:

```lean
section
variable {p : ℕ} [hp : Fact (Nat.Prime p)] [NeZero p]

-- Auto-gen lives here, references ZMod p as the field type
@[irreducible] def constraints (Main : Vector (ZMod p) N) :
    SP1ConstraintList (ZMod p) := ...

end
```

`toStateProp` uses `ZMod.val` directly (instead of `.val`):

```lean
def toStateProp (cstr : SP1Constraint (ZMod p)) (s : SailState) : Prop :=
  match cstr with
  | .send (.memory _ _ addr0 ...) mult => mult ≠ 0 →
      if h_addrs : addr0.val < 32 ∧ ... then  -- ZMod.val, not Fin.val
        s.get_reg? (BitVec.ofNatLT addr0.val ...) = ...
      else ...
  ...
```

Top-level `correct_*` instantiates at `p := KB`:

```lean
theorem correct_add (Main : Vector (ZMod KB) 33) ... := by ...
```

Since `ZMod KB = Fin KB` definitionally, all existing proofs that use
`Fin KB` syntax still elaborate after the migration — the type-checker treats
them as identical.

**No new typeclass needed.** `[Fact (Nat.Prime p)] + [NeZero p]` is sufficient
for the field instance; the ad-hoc `LT` + `Mod` are the only additions.

`ByteOpcode.constrain` and `Opcode.trusted_instr` would need to be lifted to
`ZMod p` too (currently `Fin KB`-typed). This is a mechanical change since
their bodies are typically just `<`, `=`, `Bool` checks — all of which work
generically once the `LT`/`Mod` instances are in place.

### B.2: Compiler emits symbolic `(2^k : F)⁻¹` instead of literal

Current behavior: compiler emits `2130673921` for `(2^16 : Fin KB)⁻¹`.
**Decision (chosen by user)**: change the compiler to emit `(65536 : F)⁻¹`
(or equivalently `(2^16 : F)⁻¹`) symbolically.

Implementation in `../sp1`:

- In `crates/core/compiler/src/ir/builder.rs` (or wherever the inverse-of-`2^k`
  values are computed), replace the literal-emission path with a symbolic
  emission. Something like emitting `"((2 ^ 16 : F)⁻¹)"` instead of the
  precomputed numeric value.
- The 4 inverse families currently used: `(2^2)⁻¹`, `(2^3)⁻¹`, `(2^8)⁻¹`,
  `(2^16)⁻¹`. The compiler probably has a switch over the `k`. Update each.

Implementation in this repo:

- The 14 KB-literal bridges in `Field.lean` (`inv_16BB_eq'` etc.) become the
  per-field simp normal-form lemmas: at the `Fin KB` instantiation, simp
  rewrites `(65536 : Fin KB)⁻¹` to `2130673921` (or vice versa) so existing
  proof tactics keep working.
- The 5 operation files that use `simp [..., inv_16BB_eq']` no longer need
  the bridge — the auto-gen and the iff lemma RHS would both use `(65536)⁻¹`
  directly.

Performance caveat: every `(65536 : F)⁻¹` reference in the auto-gen will
require simp to dispatch. The performance impact depends on how often the
inverse appears (the audit shows ~150 places use literals across the
`Constraints.lean` files). May want to mark the bridge lemmas with high simp
priority to avoid regressions in the slow-built chips (ShiftLeft 307s,
ShiftRight 363s, DivRem 268s).

### B.3: Chip files declare `variable {F : Type*} [Field F]`

Each `<Chip>Chip.lean` and `<Operation>.lean` file would add a section-level
`variable {F : Type*} [PrimeFieldFin F]` (or `[Field F]` + extras), and the
`@[irreducible] def constraints` from the auto-gen lives inside that section.

The top-level `correct_*` theorems instantiate at `F = Fin KB`:

```lean
theorem correct_add (Main : Vector (Fin KB) 33) ... := by ...
```

The body of `correct_*` would invoke the field-generic operation iff lemmas
(e.g. `AddOperation.allHold_constraints_iff` now stated `∀ {F} [Field F] ...`)
which the type system would unify at `F = Fin KB`.

**Risk**: the operation iff lemmas currently rely on KB-specific simp
behavior implicitly. After lifting, the proofs may need typeclass annotations
sprinkled in (e.g. `[Fact (Nat.Prime p)]` for invertibility). This is the
"per-operation tactical fixup" cost — likely 30-60 min per operation × 19
operations = roughly a week of work, plus the per-chip fixup which is
similar.

### Migration plan for sub-phase B

1. **Set up the typeclass.** Add `class PrimeFieldFin` to
   `SP1Foundations/Field.lean`, instance it for `Fin KB`, prove the projection
   lemmas (mostly `rfl`).
2. **Lift `toProp`/`toStateProp`/`allHold`/`initialState`** to take
   `[PrimeFieldFin F]`, restating the math via `PrimeFieldFin.toNat`. Verify
   `lake build` clean (existing chips unchanged because they instantiate at
   `Fin KB`).
3. **Update upstream** to emit `F`-typed annotations and symbolic inverses.
   Drop the `Fin KB` strings from `main.rs` / `ast.rs` / `func.rs`. Regen +
   verify byte-diff is exactly the type-annotation change (with a
   `s/Fin KB/F/g`-style substitution).
4. **Add `variable {F : Type*} [PrimeFieldFin F]`** to one operation file as
   a pilot (e.g. `IsZeroOperation.lean` — already structurally generic, no
   KB bridges per Phase 3 audit). Verify `correct_<chips that use IsZero>`
   still close.
5. **Sweep remaining operations**, simplest-first (per Phase 3 audit:
   `IsZero` → `IsZeroWord` → `IsEqualWord` → `U16Compare` → `BitwiseU16` →
   `U16MSB` → `LtUnsigned` → `LtSigned` → `Add` → `Sub` → `AddrAdd` →
   `Addw` → `Subw` → `U16toU8Safe`).
6. **Sweep chips**, simplest-first. Most should "just work" if their
   operations are now generic; the three KB-bridge-using chips
   (`BranchChip`, `JalrChip`, `LoadByteChip`) need targeted attention.
7. **Audit residual `Fin KB` references** in hand-written code. Anything
   left should be in `correct_*` statements (intentional KB instantiation)
   or in `Field.lean` instances (intentional concrete-field surface).

**Estimated cost**: ~1 week of focused work, with `lake build` checkpoints
after each operation/chip migration. Risk-mitigated by the type system —
either it elaborates or it doesn't.

**Open questions to resolve before starting B**:

- ~~**Q1**: Does mathlib already have a class equivalent to
  `PrimeFieldFin`?~~ **Resolved 2026-04-26**: yes, `ZMod p` with
  `[Fact (Nat.Prime p)] + [NeZero p]` is sufficient. No new class needed.
  Rephrase `<`/`%` uses to `.val < c` / `.val % c = 0` (Nat-level) to avoid
  non-canonical `LT (ZMod p)` instance.
- **Q2**: How does the `[OfNat F n]` instance interact with the
  high-priority `Fin KB` instances in `Field.lean:46`? The perf-critical
  instances must keep firing for `Fin KB` (= `ZMod KB` definitionally), so
  the existing block should still apply at `p := KB`. Generic `OfNat (ZMod p) n`
  comes from mathlib via the field's `Nat`-cast — should not compete with
  the high-priority `Fin KB` ones at the concrete instantiation, but worth
  re-running the perf profile during the migration to confirm no regression
  in `ShiftRight` (current 363 s, the worst).
- **Q3**: ~~For the `pc0 % 4 = 0` modular check, what's the right
  generalization?~~ **Resolved 2026-04-26**: rephrase as `pc0.val % 4 = 0`
  (Nat-level), per Q1's resolution.
- **Q4 (new)**: Should `ByteOpcode.constrain` and `Opcode.trusted_instr` be
  lifted from `Fin KB` to `ZMod p`? Their bodies are `<`, `=`, `Bool` checks
  — mechanical to lift once the parameterization is in place. Add to the
  migration sequence between steps 2 and 3 of the plan above.

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
