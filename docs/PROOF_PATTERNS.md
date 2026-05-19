# Proof patterns, anti-patterns, and landmines

A single reference for the proof-author who has hit a wall — slow
builds, mysterious failures after apparently-successful elaboration,
tactics that don't scale, or `lake env lean` reporting success when
nothing actually built. Five sections, ordered by how a reader is most
likely to arrive here.

For toolchain-specific quirks (Lean 4.29, Sail v4 renames), see
`LEAN_AND_SAIL_NOTES.md`. For chip-shape regeneration cascades, see
`CONSTRAINT_REGEN.md`. For the polymorphic-proof tactical recipes
that drive `_poly` companion proofs over `ZMod p`, see
`FIELD_GENERIC.md` "Polymorphic proof patterns".

## 1. Performance wins

Techniques that produced measurable wins during the PR #92 upgrade.
The PR description quotes "~40% speedup in DivRem and ShiftRight";
this is what's behind that number, plus a few smaller wins worth
knowing.

### High-priority arithmetic instances

**Symptom**: instance synthesis dominates `lake build` profiles.
`lean_profile_proof` shows hundreds of seconds in `synthInstance`
calls. Goals contain large numbers of `Fin KB` operations (chip
constraints can have thousands).

**Why**: default instance search for `Fin KB` arithmetic fans out to
5–9 candidates per operation. The lemma elaborator then has to
disambiguate per call site.

**Fix**: declare the arithmetic instances at high priority.
`SP1Foundations/Field.lean` does:

```lean
@[instance 10000] instance : Add (Fin KB) := ...
@[instance 10000] instance : Mul (Fin KB) := ...
-- ditto Sub, Neg, Pow
```

**Impact**: ShiftRight cumulative synthesis time dropped from ~779s
to negligible. This single change is the single biggest contributor
to the "40%" headline figure.

**Reuse**: any time you introduce a hot type that participates in
large generated terms, do this immediately. Cheap, idempotent, easy
to undo if it ever causes ambiguity.

### Break large `obtain` chains

**Symptom**: a single `obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ :=
h_cstrs` near the top of a chip proof takes seconds and produces a
goal Lean takes seconds more to render.

**Why**: wide destructuring patterns force the elaborator to
type-check each component against the full hypothesis shape
simultaneously. Some elaboration paths are exponential in
depth × width.

**Fix**: prefer stepwise `rcases` or intermediate `have`s that
destructure two or three components at a time:

```lean
rcases h_cstrs with ⟨h1, h_rest⟩
rcases h_rest with ⟨h2, h_rest⟩
-- continue
```

**Impact**: ShiftRight went 836 → 161 lines and visibly snappier;
DivRem ~40% faster on its own. Commits `27a52d0` (mild perf) and
`f58d7cd` (more perf) are the canonical examples.

**Tradeoff**: more lines of proof code, but each step is linear
rather than exponential. Net win in both speed and readability.

### Avoid case-bashing on shift amounts

**Symptom**: a SailM right-shift proof manually case-splits on the
shift amount (`> 63`, `= 64`, etc.) with hand-rolled `mod`
arithmetic. Each branch needs separate closure.

**Why**: the v2 SailM API didn't expose a clean lemma for the "shift
amount mod width" identity. Hand splits filled the gap but were slow.

**Fix**: use the dedicated Sail v4 normalization. Once
`Sail.BitVec.toNatInt` is in your simp set, the right rewrite is:

```lean
simp [shift_bits_right_arith, Sail.BitVec.toNatInt]
congr 1
-- close residue
```

**Impact**: replaced multi-branch proofs with three-line discharges.
Commit `bf58f5c`.

**Reuse**: any time you find yourself case-splitting on a numeric
parameter of a Sail operation, check if there's a dedicated lemma.
Sail v4 added several since v2.

### `maxHeartbeats` discipline

**Pattern**: `set_option maxHeartbeats N in <decl>` is the right
granularity in 99% of cases — only the one declaration that needs
more budget pays.

**Layout requirement** (from the linter): the comment line explaining
*why* the bump is needed must sit *between* the `set_option ... in`
and the declaration, like:

```lean
set_option maxHeartbeats 800000 in
-- 6-arm case split on the operand encoding makes the simp call deep
theorem correct_branch ... := by
  ...
```

Not before the `set_option`, not trailing on the same line — both
forms trip the `emptyLine` linter. See `LEAN_AND_SAIL_NOTES.md` or
`CLAUDE.md`'s "Build" section for the linter wording.

**File-wide bumps** (rare): need a preceding `set_option
linter.style.setOption false` line on its own. Use only when the
whole file genuinely needs the budget. `MemChecks.lean` and
`SailM.lean` are the load-bearing examples.

**Anti-pattern**: don't bump `maxHeartbeats` to mask a slow tactic.
Find the slow tactic. Common offenders: a `simp` set containing
redundant lemmas (use `simp?` to trim), a `decide` over a large
finite type (try `omega` or a structured rewrite), or a `simp_all`
doing more than needed (target it).

### Factored polynomial identities

**Pattern**: when proving a polynomial identity with many terms
sharing a common factor (e.g. `+ (carry_terms) * 2^128` in
`core_mul_poly`'s 16-limb identity), prove the equation **directly
in factored form** rather than expanded.

**Why**: `linear_combination` / `ring` close both shapes equivalently
*over ℤ*, but at the `BitVec` bridge step, the factored form lets
`Nat.add_mul_mod_self_right` apply directly. The expanded form needs
a heavyweight final `ring` rewrite that compounds with everything
else in scope.

**Impact**: `core_mul_poly` went from 30+ minutes (never finished) to
341s after this restructuring. See commits `416ddb6` /
`be52c86`.

**Companion**: don't try `∀ (i j : Fin n)` quantified byte-product
helpers — after `fin_cases i`, the `bw[i.val]` indexing leaves
`↑i < 16` side-conditions that don't auto-close. Inline the byte
bounds.

### Parallel build via `mathlib shake`

**Pattern**: `lake build` parallelism is bounded by the import graph.
`mathlib shake` (commit history references it as a recent addition)
tightens imports so independent files can build in parallel.

**Workflow**:

1. Run `mathlib shake` (or the equivalent `lake exe shake` once
   configured) over the project.
2. Apply the suggested import additions / removals.
3. `lake build` should now use more cores.

**Caveat**: shake suggests imports based on what's *used*. It doesn't
know about transitively-required simp lemmas, so always re-run `lake
build` after applying suggestions and revert anything that broke.

## 2. Tactic anti-patterns and what doesn't scale

Tactics that *look* like they should close a goal but break down at
the scale this repo runs at.

### `nlinarith` past ~4 limbs

**Symptom**: `simp [L]; nlinarith` works fine for 4-limb bound checks
(e.g. `core_mulw_poly`, ~100s build) but at 16 limbs
(`core_mul_poly`) it runs 30+ minutes with no termination.

**Why**: `nlinarith` is exponential in `#hypotheses × #products`.
With many byte values in scope and a sum of byte products on the RHS,
each call has to try every multiplication. Doesn't scale.

**Fix**: replace with explicit `Nat.mul_le_mul (by omega) (by omega)`
per byte product, then close with `omega`:

```lean
-- L bound (linear, just carry * 256): omega works
have hL_lt : L < p := by simp [L]; omega
-- R bound (sum of products): explicit byte bounds + omega
have hb_0_k : bw[0].val * cw[k].val ≤ 255 * 255 :=
  Nat.mul_le_mul (by omega) (by omega)
have hb_1_km1 : bw[1].val * cw[k-1].val ≤ 255 * 255 :=
  Nat.mul_le_mul (by omega) (by omega)
... (k+1 such bounds for limb k)
have hR_lt : R < p := by simp [R]; omega
```

For 16 limbs, total byte-product bounds: 1 + 2 + ... + 16 = 136.
Verbose but mechanical, and *fast*.

### `simp_all` cost vs. correctness

**Symptom**: a proof closes via `simp_all` but takes long enough to
feel suspicious, or breaks unrelated downstream lemmas after you
change something tangentially.

**Why**: `simp_all` rewrites every hypothesis simultaneously and can
normalize one hypothesis using another in non-obvious ways. The
leakage workaround in commit `419ee1d` was needed because a
`simp_all` was discharging facts the proof needed to keep available.

**Fix**: prefer `simp [...] at h₁ h₂` (targeted) over `simp_all`.
If you must use `simp_all`:

1. Read the resulting goal carefully — make sure nothing critical
   was rewritten away.
2. If the closure is non-obvious, leave a one-line comment explaining
   what `simp_all` is doing.
3. Consider replacing with a small lemma so the closure is reusable.

**Related landmine**: `simp_all` strips `[Fact (...)]` instances if a
local hypothesis would discharge them — e.g. if `hp17 : 131072 < p`
is in scope, `simp_all` collapses `Fact (2^17 < p)` to `Fact True`.
Down-stream tactics that need the original `Fact` then fail. Fix:
re-derive the unfolded bound AFTER `simp_all`, not before. (See also
`FIELD_GENERIC.md`'s polymorphic proof patterns.)

### `bv_decide` on `↑↑` cast residue

**Symptom**: `bv_decide` reports "potentially spurious counterexample"
with `BitVec.ofNat 128 ↑↑(...).toNat` listed as opaque variables. The
double-cast `ℕ → Fin KB → ℕ` is introduced when a literal `ℕ` flows
into a `Vector (Fin KB) n` slot.

**Fix**: strip the cast first using `Fin.val_cast_of_lt` (when you
can prove the value `< KB` — byte slices give `< 256`, etc.), then
call `bv_decide`. Canonical site: `byte_decomp_128` in
`SP1Foundations/Word.lean`.

(After the migration to `Vector (ZMod p) n` slots this round-trip no
longer arises; the workaround stays documented in case any chip is
reverted.)

### `bitVec_sshiftright_eq` simp normalization trap

**Symptom**: a chip proof does `simp [bitVec_sshiftright_eq]` and
then later tries `apply bitVec_sshiftright_eq` — the `apply` fails
because `simp` has already normalized the LHS away.

**Why**: `simp` on `BitVec.setWidth (BitVec.extractLsb …)` rewrites
to `BitVec.ofNat _ (… .toNat >>> _)`, which is the form
`bitVec_sshiftright_eq` produces but not what its LHS pattern matches.

**Fix**: pick one strategy. Either rewrite once with the lemma and
close with the unfolded equation (see
`exec_RTYPEW_pure_bv_to_w_poly`'s SRAW case in
`SP1Foundations/SailM.lean`), or simp into the new normal form with
`simp [BitVec.extractLsb, BitVec.setWidth_eq, BitVec.extractLsb',
BitVec.toNat_setWidth]` and reason from there.

### `grind` on free `Fin KB` variables

**Symptom**: `grind` on a goal over `Fin KB` reports "error while
initializing `grind ring` operators: instance for `NatCast.natCast` …
is not definitionally equal to the expected one
`Lean.Grind.Semiring.natCast`".

**Why**: `grind` eagerly initializes ring machinery on `Fin KB`, but
the `Field` instance comes from `ZMod.instField KB` and its `NatCast`
is not reducibly definitionally equal to
`Lean.Grind.Semiring.natCast`.

**Fix**: `intros; subst_vars; grind`. Substituting the numeral
through the goal sidesteps `grind ring` entirely. Works when the
remaining `Fin KB` terms are structure fields / indexed vector
entries (not further arithmetic unknowns). Doesn't help when the
goal genuinely needs ring reasoning over free `Fin KB` variables —
that case needs a proper `Lean.Grind.CommRing (Fin KB)` instance or a
hand-written closure.

### Aggressive `simp_all` adoption

Tried in this PR; rolled back. The convenience win loses to the
correctness risk and the per-call cost. Default: targeted simp;
reach for `simp_all` only when you've audited what it changes.

### Bulk file-wide `set_option maxHeartbeats`

Tried in some chip files; reverted in favor of per-decl bumps. The
file-wide form interacts with the `setOption` linter and bumps every
declaration including ones that don't need it. Keep budget bumps
scoped to the single decl that needs them.

## 3. Kernel and elaboration landmines

Failures that come *after* the elaborator declares success, or that
look like elaboration failures but are really kernel-level type
re-check failures. These cost the most because the symptoms appear
divorced from the cause.

### Kernel deep-recursion on `2^N` inside `Int.toNat (... % ...)`

**Symptom**: `(kernel) deep recursion detected` during the kernel's
final type-check pass on an otherwise-elaborated proof. The kernel
pass is independent from elaboration heartbeats, so increasing
`maxHeartbeats` doesn't help — the proof appears to elaborate fine
and then fails *after*.

**MWE** — the canonical 2-line reproducer (smallest standalone case,
suitable for an upstream Lean issue):

```lean
example (b n : ℕ) :                                  -- elaborates fine
    ((b : ℤ) % n).toNat = b % n := by rfl

example (b n : ℕ) :                                  -- (kernel) deep recursion
    ((b * 2 ^ 64 : ℤ) % n).toNat = (b * 2 ^ 64) % n := by rfl
```

**Trigger threshold**: any `2 ^ N` with `N ≥ 15` planted inside an
`Int.toNat (... % ...)` shape blows the kernel's stack during `rfl`
re-check. The kernel tries to fully unfold `2 ^ N` definitionally;
once N crosses ~32k succ applications, it dies.

Production proofs hit this through `BitVec.ofInt n i = (i % 2 ^
n).toNat`, which is what `BitVec.signExtend` reduces to. So any
proof term whose type or body mentions `BitVec.signExtend N _` with
`N ∈ {64, 128}` is a candidate, as is any `Sail.BitVec.toNatInt`-
derived shape with a literal modulus.

**Historical workaround**: `set_option debug.skipKernelTC true in
<decl>` disables the kernel re-check for that declaration. Does
**not** introduce new axioms (`lean_verify` confirms the standard
axiom set unchanged), but removes a verification layer. As of
2026-05-15 the build is `skipKernelTC`-free; treat the option as a
last resort, not a production fix.

**Diagnostic**: if you suspect a kernel trip, grep the failing proof
term for `Int.toNat`, `BitVec.signExtend`, or
`Sail.BitVec.toNatInt`. Any one is enough to instantiate the
substrate. The repo helper `lean_profile_proof` (MCP) will localize
which sub-call carries the expensive term once the option is added
back temporarily.

#### Remediation playbook (try in order)

1. **Helper application** — if the trigger is a literal `((↑b : ℤ) %
   n).toNat = b % n` step, replace the `omega`/`aesop` discharge
   with `Int.toNat_natCast_emod_natCast`
   (`SP1Foundations/Misc.lean`) or `BitVec.toNat_ofInt_natCast`
   (`SP1Foundations/BitVec.lean`). Both route through
   `Int.toNat_emod` + `Int.toNat_natCast` and never expose `2 ^ N`
   to definitional reduction. Canonical site:
   `SP1Foundations/SailM.lean` `exec_RTYPEW_pure_bv_to_w_poly`
   (SRAW arm).

2. **Bare-`BitVec 64` lift** — when the trigger lives inside an
   `aesop`/`bv_decide` proof term over a polymorphic carrier (`Word
   (ZMod p)`, `BWord (ZMod p)`), factor sub-goals that don't depend
   on the carrier into `private` helpers stated at the bare `BitVec
   64` level. The polymorphic instance graph never appears in the
   helper's proof term, so the kernel can re-check it. Canonical
   helpers in `SP1Foundations/SailM.lean`:
   `zero_extend_zopz0zI_s_eq`, `zero_extend_zopz0zI_u_eq`,
   `shift_bits_right_arith_setWidth_6_eq`. Bisecting which arm is
   the dominant trigger is worth the few minutes — it's often `.SRA`.

3. **Inline-derivation lift** — for chip-side bodies whose
   `omega`-built proof terms expose `BitVec.signExtend N imm`, lift
   the relevant `have h_*_eq : ... := by ...` block to a top-level
   lemma. The kernel walks the trigger once instead of inline at
   every call site. Canonical lifts:
   `Branch.branch_addr_eq_poly` in
   `SP1Chips/Branch/Constraints.lean` (replaces a 6×-inlined
   macro); `Jalr.jalr_target_mod4_poly`,
   `Jalr.jalr_unmasked_eq_masked_plus_poly`,
   `Jalr.jalr_target_eq_poly` in `SP1Chips/JalrChip.lean`.

4. **Simp-set swap** — when the lifted helper *itself* still trips,
   the final lever is a simp set that produces a different proof-
   term shape:
   - `BitVec.add_def` (the bare definition `x + y = ⟨…⟩`) does not
     introduce `% 2 ^ w` syntactically into the proof term.
     `BitVec.toNat_add` does — and that `2 ^ w` then compounds with
     literals like `2 ^ 16/32/48` from `Word.toNat_def` to produce
     the trigger shape during omega-certificate construction.
   - `Word.toNat` (which routes through the opaque `toNat_aux.1`
     handle, unfolded automatically by `@[simp] toNat_aux_def`) is
     kernel-friendlier than `Word.toNat_def`. Both unfold to the
     same limb sum on the goal, but the proof terms differ.
   - The `Branch.branch_addr_eq` body in `SP1Chips/BranchChip.lean`
     is the canonical fix; the simp set is
     `simp [BitVec.add_def, Word.toBitVec64, Word.toNat,
     ← BitVec.toNat_inj]`.

#### Cross-references

- Helpers:
  `SP1Foundations/Misc.lean` — `Int.toNat_natCast_emod_natCast`;
  `SP1Foundations/BitVec.lean` — `BitVec.toNat_ofInt_natCast`.
- Bare-`BitVec` lifts:
  `SP1Foundations/SailM.lean` (`exec_RTYPE_pure_bv_to_w_poly`,
  `exec_RTYPEW_pure_bv_to_w_poly`).
- Chip-side lifts:
  `SP1Chips/Branch/Constraints.lean` (`branch_addr_eq_poly`),
  `SP1Chips/JalrChip.lean` (`jalr_target_mod4_poly`,
  `jalr_unmasked_eq_masked_plus_poly`).
- Tactic: `SP1Foundations/Tactics.lean` — `bv_amicus_kerneli` is a
  kernel-friendly normalization pass for `BitVec`s; complements the
  helpers above when you need `Nat`-side reasoning without exploding
  the kernel.

#### When to revisit

If a future Lean toolchain bump is suspected to have fixed the
kernel's `2 ^ N` reduction, the cheapest re-test is to delete every
`set_option debug.skipKernelTC true in` line, run `lake build`, and
re-add only the lines whose declarations newly fail.

### Fin KB ↔ ZMod KB defeq gap in `+++` distribution

**Symptom**: a chip proof using `(constraints Main).allHold_poly
(p := KB)` displays cleanly but `simp [..., List.forall_append, ...]`
leaves `+++` un-distributed. Inspecting with `set_option pp.explicit
true` reveals `List.Forall (SP1Constraint (ZMod KB))` over an
`HAppend (List (SP1Constraint (Fin KB)))` term.

**Why**: the chip's auto-gen returns `SP1ConstraintList (Fin KB)`;
the outer goal is at `SP1ConstraintList (ZMod KB)`. Definitionally
equal, but `simp`'s pattern matcher only does defeq-modulo-
reducibility and doesn't bridge the parameter position.

**Fix**: don't pursue this approach. The structural resolution is
chip-level parametric emission via `update_constraints.py`'s
`PARAMETRIC_CHIPS` dict — the chip's auto-gen then returns
`SP1ConstraintList F` over `(F : Type) [Field F]` and the
destructure works naturally. See `FIELD_GENERIC.md` "Track C1" and
`CONSTRAINT_REGEN.md` for the regen mechanics.

## 4. Build validation gotchas

The bugs in this section let you ship "passing" work that doesn't
actually pass.

### `lake env lean` exits 0 on Lean stack overflow

**Rule**: `lake env lean SP1Chips/Foo.lean` is **not reliable** for
verifying that a file compiles. When Lean's elaborator hits an
internal stack overflow ("Stack overflow detected. Aborting."), the
lake wrapper still returns exit code 0, and grep checks for embedded
errors (e.g. `grep -cE '^(error|warning):'`) miss the failure because
Lean error lines start with the file path
(`SP1Chips/Foo.lean:line:col: error:`), not with `error:`. Combined
with the pre-existing `.lake/build/lib/lean/.../foo.olean` cache
from before the edit, downstream `lake env lean` checks see the
stale olean and report "success" on what is actually a broken file.

**Discovered**: 2026-05-14 during DivRem `_poly` phase 1.2–1.4 work.
Multiple successive "builds completed exit 0, no errors" reports for
`spec.divuw_poly` / `spec.remuw_poly` / `spec.divw_poly` /
`spec.remw_poly` / `spec.div_poly` / `spec.rem_poly` were all
stack-overflow false-positives. A single `lake build
SP1Chips.DivRemChip` exposed the truth: errors at line 1401 of
`DivuwRemuw.lean` and similar elsewhere — the closer chains never
actually closed.

**How to apply**:

- For honest validation, run `lake build <Module>` (e.g. `lake build
  SP1Chips.DivRemChip`). It respects exit codes, surfaces
  dependency-graph failures, and uses ✔/✖ markers per module.
- If using `lake env lean <file>`, **always** also `tail -5` the log
  and look for `Stack overflow detected. Aborting.` AND `grep ':
  error:'` (the colon-prefixed form). Don't trust the exit code
  alone, don't trust an `error:`-anchored grep.
- The build cost of `lake build` is roughly the same as `lake env
  lean` if dependencies are cached (Lake's replay is fast). The
  extra confidence is worth it.
- Per-file `lake env lean` is fine for fast iteration during proof
  writing — just **always** finish with a `lake build` validation
  before claiming a phase done.

### Zero errors *and* zero warnings is the pass bar

`lake build` is considered "passing" only when both `^error:` and
`^warning:` counts are zero (`grep -cE '^(error|warning):'
build.log`). The mathlib standard linter set is enabled via
`weak.linter.mathlibStandardSet = true` and the repo has driven
warnings to zero; a green build that emits new warnings is a
regression. See `CLAUDE.md`'s "Build" section for the common fix
patterns (`show` → `change`, `.` → `·`, blank-line in `by`-block,
etc.).

### Build concurrency / RSS limits

Heavy chips (`SP1Chips.DivRem.Constraints` etc.) take 17–40 min and
consume 5–15 GB RSS each. Before starting any new `lake build`,
**either let the running build finish or kill it explicitly** (`pkill
-f "lake build"` / `pkill -f "lake env lean SP1Chips"`). Hard cap:
**2–3 builds at once, full stop** — never start a fourth speculative
build. A `run_in_background` build whose parent shell died gets
reparented to init and survives session boundaries; check with `ps
-ef | grep -E "lake|lean" | grep -v lsp` before spawning a new one.

## 5. Mechanical refactor scripts

When the constraint compiler drops a column from a chip, every
`Main[k]` index above the cutoff shifts down. Hand-editing 50+
occurrences per chip × 17 chips is the wrong shape; mechanical Python
+ `stop`-marker is faster and lower-risk.

The "shift + stop" recipe lives in `CONSTRAINT_REGEN.md`. Reproduced
here as a one-glance reference:

```python
import re
removed_idx = 25   # from `git show <commit>^:.../Constraints.lean | grep is_trusted`
shift = 1
text = re.sub(r', is_trusted := Main\[\d+\]', '', text)
def sub(m):
    k = int(m.group(1))
    return f"Main[{k - shift}]" if k > removed_idx else m.group(0)
text = re.sub(r"Main\[(\d+)\]", sub, text)
```

For an inserted column, `shift` is negative and the comparison flips
to `>= insert_idx`. After applying, inject `stop` at the start of
every broken proof body (with `have _ := Main; have _ := cstrs;
have _ := h_is_X` first if the body uses `variable`-bound names only
after the `stop`). File-wide `set_option linter.unusedVariables
false` if most lemmas in the file are stopping early.

This pattern was applied successfully to 17 chips in one session
during the `is_trusted` cascade. See `CONSTRAINT_REGEN.md` "Stop-
marker fallback" for the full procedure.

## Profiling tools

When chasing perf, profile *before* changing anything. The high-
priority arithmetic instance fix in §1 was found by noticing
instance synthesis dominated a profiler trace, not by guessing.

- `lake env lean -DmaxHeartbeats=N <file>` to find the actual
  bottleneck declaration. (But finish with `lake build` — see §4.)
- `set_option profiler true in <decl>` for a tactic-by-tactic
  breakdown.
- `lean_profile_proof` MCP tool (slow but precise — only run on a
  single declaration you've already isolated).
- `time lake build SP1Chips` for whole-library wall time.
