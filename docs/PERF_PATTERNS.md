# Proof performance patterns

Concrete techniques that produced measurable wins during the PR #92 upgrade. The PR description quotes "~40% speedup in DivRem and ShiftRight"; this doc captures the actual moves behind that number, plus a few smaller wins worth knowing.

## High-priority arithmetic instances

**Symptom**: instance synthesis dominates `lake build` profiles. `lean_profile_proof` shows hundreds of seconds in `synthInstance` calls. Goals contain large numbers of `Fin KB` operations (chip constraints can have thousands).

**Why**: default instance search for `Fin KB` arithmetic fans out to 5–9 candidates per operation. The lemma elaborator then has to disambiguate per call site.

**Fix**: declare the arithmetic instances at high priority. `SP1Foundations/Field.lean` does:

```lean
@[instance 10000] instance : Add (Fin KB) := ...
@[instance 10000] instance : Mul (Fin KB) := ...
-- ditto Sub, Neg, Pow
```

**Impact**: ShiftRight cumulative synthesis time dropped from ~779s to negligible. This single change is the single biggest contributor to the "40%" headline figure.

**Reuse**: any time you introduce a hot type that participates in large generated terms, do this immediately. Cheap, idempotent, easy to undo if it ever causes ambiguity.

## Break large `obtain` chains

**Symptom**: a single `obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h_cstrs` near the top of a chip proof takes seconds and produces a goal Lean takes seconds more to render.

**Why**: wide destructuring patterns force the elaborator to type-check each component against the full hypothesis shape simultaneously. Some elaboration paths are exponential in the depth × width.

**Fix**: prefer stepwise `rcases` or intermediate `have`s that destructure two or three components at a time:

```lean
rcases h_cstrs with ⟨h1, h_rest⟩
rcases h_rest with ⟨h2, h_rest⟩
-- continue
```

**Impact**: ShiftRight went 836 → 161 lines and visibly snappier; DivRem ~40% faster on its own. Commits `27a52d0` (mild perf) and `f58d7cd` (more perf) are the canonical examples.

**Tradeoff**: more lines of proof code, but each step is linear rather than exponential. Net win in both speed and readability.

## Avoid case-bashing on shift amounts

**Symptom**: a SailM right-shift proof manually case-splits on the shift amount (`> 63`, `= 64`, etc.) with hand-rolled `mod` arithmetic. Each branch needs separate closure.

**Why**: the v2 SailM API didn't expose a clean lemma for the "shift amount mod width" identity. Hand splits filled the gap but were slow.

**Fix**: use the dedicated Sail v4 normalization. Once `Sail.BitVec.toNatInt` is in your simp set, the right rewrite is:

```lean
simp [shift_bits_right_arith, Sail.BitVec.toNatInt]
congr 1
-- close residue
```

**Impact**: replaced multi-branch proofs with three-line discharges. Commit `bf58f5c`.

**Reuse**: any time you find yourself case-splitting on a numeric parameter of a Sail operation, check if there's a dedicated lemma. Sail v4 added several since v2.

## `maxHeartbeats` discipline

**Pattern**: `set_option maxHeartbeats N in <decl>` is the right granularity in 99% of cases — only the one declaration that needs more budget pays.

**Layout requirement** (from the linter): the comment line explaining *why* the bump is needed must sit *between* the `set_option ... in` and the declaration, like:

```lean
set_option maxHeartbeats 800000 in
-- 6-arm case split on the operand encoding makes the simp call deep
theorem correct_branch ... := by
  ...
```

Not before the `set_option`, not trailing on the same line — both forms trip the `emptyLine` linter. See `docs/LEAN_4_29_AND_SAIL_V4.md` (or CLAUDE.md "Build" section) for the linter wording.

**File-wide bumps** (rare): need a preceding `set_option linter.style.setOption false` line on its own. Use only when the whole file genuinely needs the budget. `MemChecks.lean` and `SailM.lean` are the load-bearing examples.

**Anti-pattern**: don't bump `maxHeartbeats` to mask a slow tactic. Find the slow tactic. Common offenders: a `simp` set containing redundant lemmas (use `simp?` to trim), a `decide` over a large finite type (try `omega` or a structured rewrite), or a `simp_all` doing more than needed (target it).

## `simp_all` cost vs. correctness

**Symptom**: a proof closes via `simp_all` but takes long enough to feel suspicious, or breaks unrelated downstream lemmas after you change something tangentially.

**Why**: `simp_all` rewrites every hypothesis simultaneously and can normalize one hypothesis using another in non-obvious ways. The leakage workaround in commit `419ee1d` was needed because a `simp_all` was discharging facts the proof needed to keep available.

**Fix**: prefer `simp [...] at h₁ h₂` (targeted) over `simp_all`. If you must use `simp_all`,:

1. Read the resulting goal carefully — make sure nothing critical was rewritten away.
2. If the closure is non-obvious, leave a one-line comment explaining what `simp_all` is doing.
3. Consider replacing with a small lemma so the closure is reusable.

**Reuse**: this is mostly a correctness pattern, but in this repo `simp_all` is also often slower than targeted simp (because it has to canonicalize the whole local context).

## Parallel build via `mathlib shake`

**Pattern**: `lake build` parallelism is bounded by the import graph. `mathlib shake` (commit history references it as a recent addition) tightens imports so independent files can build in parallel.

**Workflow**:

1. Run `mathlib shake` (or the equivalent `lake exe shake` once configured) over the project.
2. Apply the suggested import additions / removals.
3. `lake build` should now use more cores.

The PR description mentions this lightly. The actual win depends on your machine; on an 8-core box this PR brought clean-build wall time down meaningfully.

**Caveat**: shake suggests imports based on what's *used*. It doesn't know about transitively-required simp lemmas, so always re-run `lake build` after applying suggestions and revert anything that broke.

## What didn't work / wasn't worth it

A few moves were tried during the PR and rolled back:

- **`grind` for ring closures.** `grind` is fast on simple ring goals but its `Lean.Grind.Semiring.natCast` initialization fails on free `Fin KB` variables. Workaround pattern (per memory `feedback_grind_ring_finkb.md`): `intros; subst_vars; grind`. Or just use `omega` / `norm_num`.
- **Bulk file-wide `set_option maxHeartbeats`.** Tried in some chip files; reverted in favor of per-decl bumps because the file-wide form interacts with the `setOption` linter and bumps every declaration including ones that don't need it.
- **Aggressive `simp_all` adoption.** See above — convenience win, correctness risk, often slower in practice.

## Profiling tools

- `lake env lean -DmaxHeartbeats=N <file>` to find the actual bottleneck declaration.
- `set_option profiler true in <decl>` for a tactic-by-tactic breakdown.
- `lean_profile_proof` MCP tool (slow but precise — only run on a single declaration you've already isolated).
- `time lake build SP1Chips` for whole-library wall time.

When chasing perf, profile *before* changing anything. The instance-priority fix above was found by noticing instance synthesis dominated a profiler trace, not by guessing.
