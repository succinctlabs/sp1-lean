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

5. **Drop `Nat.zero_mul, Nat.add_zero` from simp_only after the limb
   expansion + extract `omega` into a bare-`ℕ` helper** — this is the
   primary recipe that cleared 21 of 26 sites in the 2026-05-17 batch.
   For `_poly` carry-chain proofs in `Word (ZMod p)` carriers (AddrAdd,
   Branch helpers, Load* chip downstreams), the spec body typically
   has:
   ```
   rw [← BitVec.toNat_inj, BitVec.toNat_add,
       Word.toBitVec64_poly_toNat_poly _, Word.toNat_poly_def, ...]
   simp only [..., h_zero_val, Nat.zero_mul, Nat.add_zero]  -- drop these
   ...
   omega                                                     -- extract
   ```
   The `Nat.zero_mul + Nat.add_zero` simp rewrites add `Eq.mpr`
   operations that compound with the omega certificate's `% 2 ^ 64`
   exposure, pushing the kernel re-check over its stack limit. Drop
   them from the simp_only, then move `omega` into a `private` helper
   at the bare-`ℕ` level whose conclusion accepts the un-simplified
   `+ 0 * 2 ^ 48` form. The helper's `omega` certificate sees `% 2 ^
   64` *in isolation* (no polymorphic `ZMod p` instances surrounding
   it) and the kernel passes. Canonical examples:
   `AddrAddOperation.close_addr_add_nat` and
   `Branch.close_branch_addr_nat` / `close_pc_plus_4_nat`. Often the
   spec body's `omega` becomes `exact close_*_nat _ _ ... hv0' hv1'
   hv2' n0 n1 n2 n3` (or its `.symm`). For chip-level `correct_*`
   theorems with no helper-lift available (e.g. LoadDoubleChip,
   LoadX0Chip), the in-place simp_only edit alone suffices because
   the trigger is the simp_only itself, not surrounding omega.

6. **Quick "stale comment" check — try just removing the line
   first.** Many `skipKernelTC` lines were added defensively and
   stayed after the underlying issue was fixed elsewhere. Both
   `MulOperation.core_mul_poly` and `core_mulw_poly` cleared in the
   2026-05-17 batch this way: just delete the `set_option` line and
   rebuild. Cost: one build cycle per site (11min for MulOperation).
   Cheap to test, often the right answer.

7. **Replace `omega` over `BitVec.toInt` with explicit Int lemmas.**
   When the kernel-tripping `omega` is closing a `BitVec.toInt`
   inequality (the omega certificate brings in `2 ^ 64` via `Int.toNat
   ((... % 2^64)...)`), substitute the explicit lemma directly:
   - `Int.not_lt.mpr : b ≤ a → ¬ a < b`
   - `Int.not_le.mp : ¬ a ≤ b → b < a`
   - `Int.not_le.mpr : b < a → ¬ a ≤ b`

   The function-application proof term is shallow; the kernel passes.
   Canonical fix: `correct_bge` in `SP1Chips/BranchChip.lean`.

8. **Split a bulk `simp only` to isolate a `rfl`-based BitVec lemma.**
   When the trigger is a single rfl-based simp lemma (e.g.
   `BitVec.toNat_ushiftRight x i := rfl`, which at `BitVec 64` plants
   the underlying `2 ^ 64` from `BitVec.ushiftRight`'s `@[expose]`
   body), pull that one lemma out of the simp set and apply it as a
   bare `rw`. The fused-simp proof term combines the rewrite's motive
   with the surrounding context's implicit type ascription; the
   separate `rw` produces a chain of shallow `Eq.mpr` motives that
   the kernel walks without compounding.

   Canonical fix: `spec.srl_common_poly` in
   `SP1Chips/ShiftRight/Srl.lean` (2026-05-18). Before:
   ```
   simp only [execute_RTYPE_pure_w_poly, BitVec.ushiftRight_eq',
              BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
              Nat.shiftRight_eq_div_pow]
   ```
   After:
   ```
   simp only [execute_RTYPE_pure_w_poly]
   rw [BitVec.ushiftRight_eq']
   rw [BitVec.toNat_ushiftRight]
   simp only [BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
   ```
   Sorry-bisect to pinpoint the rfl-trigger first — the cost is one
   build cycle per bisect step but the fix is surgical when it lands.
   Diagnostic: the surviving `BitVec 32` analogs (Srlw) use the same
   simp set without tripping, so the trigger is the bit-width, not
   the lemma.

9. **Push a `% 2^w` rewrite into the chip's close-helpers.** When the
   trigger is the cumulative `% 2 ^ 64` in N call-sites of a close-
   helper (Sll's 4×16 case-tree calls `sll_close_cb4cb5_*_case`
   helpers whose conclusion is `... <<< shift % 2 ^ 64`), rewrite
   each helper's conclusion to a `% 2^w`-free shape
   (`(... <<< shift).toNat` instead of `... <<< shift % 2^w`) and
   move the `rw [BitVec.toNat_shiftLeft]` step into the helper's body
   as its first tactic. The helper's olean now walks `% 2^w` once;
   the chip's many call-sites carry a `% 2^w`-free type, so the
   kernel walk over the chip's proof term doesn't compound.

   Canonical fix: `sll_close_cb4cb5_{zero,one_one,zero_one,one_zero}_case`
   in `SP1Chips/ShiftLeft/Common.lean` + `spec.{sll,slli}_poly` in
   `SP1Chips/ShiftLeft/Sll.lean` (2026-05-18). The chip's prep chain
   drops `rw [BitVec.toNat_shiftLeft]` (now lives in helper) and the
   `change` block is restated without `% 2 ^ 64`. The shift=0 sub-case
   needs `BitVec.shiftLeft_zero` in place of `Nat.shiftLeft_zero` plus
   removal of the `Nat.mod_eq_of_lt` step.

   When recipe 8 isn't enough: recipe 9 applies when the surviving
   trigger is in close-helper conclusion *types*, not in a simp
   lemma. Identify by reading each helper's conclusion — if it
   contains `% 2 ^ w` for w ≥ 64, that's the trigger.

   Recipe 9 fails for DivRem cores (2026-05-18 attempt): even with
   the omega lifted into a polymorphic-`n` bare-ℕ helper using
   `Nat.add_mod` + `Nat.add_mul_mod_self_right` (avoiding omega's
   certificate), the chip's proof term containing `2 ^ 128` still
   trips. The DivRem trigger is structurally different — the chip
   itself carries `2 ^ 128` in its post-`simp` goal type, not in any
   single helper conclusion. Tried: bare-ℕ helper with `omega`
   (helper trips), explicit-rewrite helper with `decide` bridge
   (decide trips), polymorphic-`n` helper with `native_decide`
   bridge (chip still trips). Open problem.

#### Empirical findings (2026-05-19 evening)

**Store* and Jal/Jalr triggers are the default simp set.** Sorry-
bisect of `StoreByteChip.correct` (~31s/cycle) pinpointed the trigger
to the first bullet after `rw [run_vmem_write_of_width_1' ...]` at
line 152: `simp [sp1_sb, h_imm_c, imm_c, Sail.ConcurrencyInterfaceV1.
write_ram, PreSail.write_ram, PreSail.writeBytes, PreSail.writeByte]`.
The bisect narrowed further: `simp only [imm_c]` (no defaults) *passes*
kernel; `simp [imm_c]` (with defaults) *trips*. Even default `simp`
alone (no added lemmas) trips on this goal. So the trigger is not any
particular added lemma — it's the default simp set running on a
BitVec-heavy EStateM goal. Same pattern in `SP1JAL_correct` at line
154 (`simp [Std.ExtDHashMap.get_insert, read_pc]`). The goal at these
points has dozens of `Word.toBitVec64_poly` instances and the default
simp set's `BitVec.toNat_*` / monadic normalization lemmas compound
into a kernel-tripping proof term.

**Why `simp only` alone isn't enough as a fix.** Replacing
`simp [...]` with `simp only [...]` clears the kernel trip but
under-normalizes the goal, so downstream `constructor` /
`rw [jump_to_of_mod4_eq_zero ...]` fail to apply. The default simp
does work the chip's structure depends on (e.g., reducing
`Register.nextPC == Register.PC` to `false` via the `BEq` decidable
instance, monadic bind/pure rewrites, BitVec literal evaluation).

**What didn't work for Jal (2026-05-19):**
- `simp (config := { decide := true }) only [...]` — same downstream
  rewrite failure as plain `simp only`. The decide-config doesn't
  trigger the needed match-on-decidable reduction.
- `simp only [...]; dsimp only` — `dsimp` makes no progress; the
  if/dite reductions aren't pure definitional.
- Adding `have h_pc_ne : (Register.nextPC == Register.PC) = false :=
  by decide` and including `h_pc_ne, dite_false, reduceCtorEq` in
  the `simp only` set — re-trips kernel. The `by decide` proof term
  itself trips (the `BEq` on `Register` walks through BitVec).

**Recipe-4 swap is the documented path but unverified for these.**
The full chip body (~120 lines for SP1JAL_correct, ~200 for
JALR_correct, ~120 each for Store*) has many `simp` calls; each
contributes to the cumulative proof term. A bare-`simp only` swap on
the single triggering call isn't enough — the chip's surrounding
simps may *also* contribute. A complete recipe-4 swap would replace
every `simp [...]` in the body with a hand-tuned `simp only [...]`
plus targeted `rw` / `dsimp` chains, matching what default simp does
*minus* the kernel-tripping rewrites. Each chip is a multi-hour
investment with no proven shortcut.

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
`set_option debug.skipKernelTC true in` line, run **`lake build`**
(not `lake env lean` — see the "`lake env lean` exits 0 on Lean stack
overflow" section), and re-add only the lines whose declarations
newly fail.

As of the **2026-05-17 evening sweep** there were 11 such lines. The
**2026-05-18 sweep** cleared 3 of those (Sll's `spec.sll_poly` +
`spec.slli_poly` and Srl's `spec.srl_common_poly`) via two new
patterns documented below. Current count: **8 load-bearing sites in
6 files**. The earlier recipe-6 (stale-comment delete + rebuild)
remains fully exhausted on this branch — all 8 surviving sites
reproduce `(kernel) deep recursion detected` on plain deletion.

- `SP1Chips/DivRem/DivRem.lean` — `div_rem_poly` core (signed 64-bit
  DWord 8-limb)
- `SP1Chips/DivRem/DivuRemu.lean` — `divu_remu_poly` core
- `SP1Chips/Store{Byte,Half,Word,Double}Chip.lean` — all 4 `correct`
  theorems
- `SP1Chips/JalChip.lean` — `SP1JAL_correct`
- `SP1Chips/JalrChip.lean` — `JALR_correct`

Cleared during the 2026-05-17 sweep (kept removed):
`AddrAddOperation.spec_of_constraints_poly`,
`MulOperation.core_mul_poly` + `core_mulw_poly`, all
`Branch/Constraints.lean` helpers, all `Load*Chip.lean` correct
theorems, the BranchChip `correct_*` family (6 theorems), DivRem
wrappers (`spec.div_poly`/`spec.rem_poly`/`spec.divu_poly`/etc. —
only the *cores* still trip), all `DivuwRemuw`/`DivwRemw`
cores+wrappers, `ShiftRight/{Sra,Sraw,Srlw}` common bodies plus
`Srlw`'s local `Word.isU64` helper.

Cleared during the **2026-05-18 sweep**: `spec.sll_poly`,
`spec.slli_poly` (`SP1Chips/ShiftLeft/Sll.lean`), and
`spec.srl_common_poly` (`SP1Chips/ShiftRight/Srl.lean`) — see new
recipes 8 and 9 below.

#### Empirical findings (2026-05-17 evening)

**DivRem and DivuRemu 64-bit cores vs. wrappers.** The `*_poly` core
lemma trips the kernel but the thinner `spec.*_poly` wrappers that
`specialize` into the core do NOT. The wrapper's proof term is just a
function application referencing the core's already-checked olean —
kernel sees a shallow term. Lesson: don't assume "if the core needs
`skipKernelTC`, the wrappers do too." Test each independently.

**Store* chips have multiple compounding triggers.** Lifting
`h_addr_eq` (the `(reg + signExt(imm)).toNat = addr_low_limbs`
bridge) into a `Word.toBitVec64_poly_addr3_toNat_eq` top-level helper
in `SP1Foundations/Word.lean` roughly halves elaboration time (~103s
→ ~51s on StoreByteChip) but **kernel still trips** — multiple
compounding triggers (`h_offset_eq`, `h_in_range`,
`Word.toBitVec64_poly_lowLimb_add_nat`, default-`simp`-via-`write_ram`).
A single lift is not enough; recipe 2 (bare-`BitVec` helper covering
the *whole* addr-bridge + width-specific write monadic chain) is the
documented path but costs 2–3h per chip with no single-lift shortcut.

**Sll/Srl 64-bit shifts vs. the passing Sra/Sraw/Srlw.** The
`spec.sll_poly`, `spec.slli_poly`, and `spec.srl_common_poly` proofs
are structurally identical to the passing
`spec.sra/sraw/srlw_common_poly` proofs — same prologue, same 4-way
byte-shift split, same close-helpers. The differentiator is invisible
at the tactic-source level. The passing Sra has an outer `rcases
h_msb_b` that splits the proof term into two arms; the failing
Sll/Srl have no analogous outer split. Hypothesis: adding an outer
split (recipe 3 applied at the byte_shift level — lift each of the 4
byte_shift branches into a separate helper, dispatcher just does
`rcases b_cb5 ... ; rcases b_cb4 ...`) may break the kernel walk into
shallower chunks. Not yet verified.

**Jal/Jalr remaining triggers.** The `word_four_eq_bitvec_four`
helper extracted in commit `62b65cf` (recipe 3 inline-derivation
lift) is insufficient on its own. Remaining triggers are likely
`hmod4` (15-line block with `Word.toBitVec64_poly` chains), the
`AddOperation.spec_poly` results (`h_add'` / `h_add_pc'` — whose body
contains `BitVec.toNat_add`), and the multiple default `simp
[spec_jal, sp1_jal, execute_JAL, ...]` calls. Each is a candidate for
further recipe-3 lifting.

**JalrChip deep-dive (sorry-bisection, 5 build cycles).** The trigger
is the single `simp [spec_jalr, sp1_jalr,
run_readReg_of_isInitialized _ _ hs, EStateM.Result.map, cond,
execute_JALR, op_a, op_b, op_c, sp1_op_a, sp1_op_b, sp1_op_c,
read_op_a, read_op_b, ← h_imm_signExtend]` call at
`SP1Chips/JalrChip.lean:258-261`. Verified via sorry-truncation:
truncating BEFORE this simp passes kernel TC; truncating AFTER still
trips. Fixes tried that **don't** work: splitting into chained `simp
only` (second simp can't apply its lemmas because default simp's
implicit monad lemmas are needed); moving `← h_imm_signExtend` to a
separate `rw` (trigger shifts but still trips); replacing `simp` with
`simp only [explicit list]` (can't reproduce default simp's monad-
bind normalization with explicit lemma list); `--tstack=2000000` (5×
current — still trips, **not borderline depth**, this is
pathologically deep recursion). Fix path: write a `JALR_correct`-
shaped helper at the `EStateM`/Sail level that produces the same
post-simp goal form WITHOUT relying on the default simp set, or lift
the entire post-simp goal manipulation chain (lines 256–317) into a
helper whose conclusion is the original theorem statement. Both are
multi-hour investments per chip. Same pattern almost certainly
applies to `SP1JAL_correct` in `JalChip.lean` since it uses the
analogous `simp [spec_jal, sp1_jal, execute_JAL, ...]` at line 124.

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
