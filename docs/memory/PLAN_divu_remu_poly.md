# Plan: Port `divu_remu` (Fin KB) → `divu_remu_poly` (ZMod p)

## Status checkpoint — 2026-05-05 mid-session

**Where the code is** (`SP1Chips/DivRem/Constraints.lean`, lines ~2455–2793):

- ✅ **Stage 1 (upfront prep) — landed**
  - Lemma scaffold (`set_option maxHeartbeats 32000000 in
    set_option debug.skipKernelTC true in lemma divu_remu_poly ...`)
    with all 113 hypotheses lifted to `ZMod p`.
  - Upfront `have`s: `h01, h21, h65535_val, h32768_val, h1v, h0v`,
    plus `hcv0..hcv7 : cry_i.val ≤ 1` derived BEFORE any `simp_all`
    runs (so `Fact (2^17 < p)` doesn't collapse to `Fact True`).
- ✅ **Blocker 1 (opening rcases) — landed**
  - The `obtain ⟨z_div, z_rem, z_divw, z_remw, z_divuw, z_remuw⟩`
    block is now an explicit 4-way case split using `h01` / `h21`
    instead of `simp_all`. The (0,0) and (1,1) cases close via
    `exfalso` + the literal Prop hypotheses; the (0,1) and (1,0)
    cases destructure `sop4` / `sop2` directly. Beware: `sop4`'s
    conclusion order is `is_div ∧ is_divu ∧ is_rem ∧ ...` (slot
    `.2.2.1 = is_rem = 0`, NOT `is_remu`), distinct from `sop2`
    which has `is_div ∧ is_rem ∧ is_remu ∧ ...`.
- ✅ **Blocker 2 (c=0 branch all-65535 closure) — landed**
  - Closes via `simp [Word.toBitVec64_poly_toNat_poly is_U64_b];
    simp [Word.toBitVec64_poly, Word.toNat_poly, h65535_val, h0v];
    push_cast [ZMod.cast_eq_val]; rfl`. The `.cast` form in the
    pretty-printed goal is **`Nat → ℤ` cast** (not `ZMod.cast`),
    and the `.toNat` is **`Int.toNat`** — `push_cast [ZMod.cast_eq_val]`
    pushes both through and `rfl` closes.
- ✅ **c≠0 branch through `bv_ctqr` "have" arm — landed**
  - The first arm of the suffices (the BV side that uses bv_ctqr)
    closes via the literal port: `Word.lt_cases_of_isU64_poly` calls,
    `eq_eb`/`eq_er`, `Word.extend_false_is_setWidth_poly`,
    `BitVec.toNat_setWidth`, `Word.toBitVec64_poly_toNat_poly`,
    final `Nat.mod_eq_of_lt (by nlinarith)`.
- 🟡 **Blocker 3 (8-way `b_cry3` carry-chain end-game) — in progress, `sorry` at line ~2793**
  - The 8 `rw [div_mod_decomposition_w_poly (by omega)
    (by omega : cry_i.val < 2)] at nof_eq_ctqpr_i` calls are in place.
    (Note: I had `hcv0..hcv7 : cry_i.val ≤ 1` upfront, but
    `div_mod_decomposition_w_poly` wants `< 2`, so each call passes
    an explicit `(by omega : cry_i.val < 2)` deriving `<` from `≤`.)
  - The `conv => lhs; simp [DWord.toBitVec128_poly, DWord.toNat_poly];
    simp [nof_eq_ctqpr0.1, ...]` block is in place.
  - The `joins`/`divs` Nat-side helpers + `j1, j2, j3, d1, d2, d3`
    are in place. `simp at *; rw [j1, d1, j2, d2, j3]` is in place.
  - `simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]; repeat rw
    [BitVec.toNat_add]; iterate 2 rw [DWord.toBitVec128_poly_toNat_poly
    (by apply DWord.isU128_of_cases_poly <;> simp [h0v] <;> omega)];
    simp [DWord.toNat_poly, h0v]; ring_nf` is in place.
  - **Sorry placeholder** is the final 8-way `rcases b_cry3 with of |
    nof <;> subst cry3 <;> simp at *` end-game (lines 2416–2442 of
    Fin KB original). Needs the patches noted in
    `feedback_divrem_core_port_blockers.md` Blocker 3 — each
    `have : ctq_i = 0` / `ctq_i = 65535` clear/grind step needs
    Nat-side bounds derived from `nof_eq_ctqpr_i.2` (the cry's
    div-by-65536 form, since after `div_mod_decomposition_w_poly`
    the conclusion is at the `.val` level, not the field level).

**Outstanding gotcha at the boundary** (last seen before user
interruption): the LSP timed out trying to verify diagnostics after
the `cry_i.val < 2` patch landed. The build status of the file
between line 2767 and 2793 was not re-verified at that moment, so
the next session should:

1. Run `lake env lean SP1Chips/DivRem/Constraints.lean` to confirm
   only the `sorry` at line ~2793 remains (no `< 2` typing issues).
2. If the `cry_i.val < 2` form trips elsewhere (e.g., the conv block
   uses `nof_eq_ctqpr*.1` / `.2` projections that may have changed
   shape), simp-fix locally.
3. Then port the 8-way end-game with the cry_i.val ≤ 1 facts in
   scope (already provided as hcv0..hcv7).

## Context

This is the heavy gating work for **Phase 3b** of the DivRem chip
`_poly` migration. It is the simplest of 4 cores (`divu_remu`,
`div_rem`, `divuw_remuw`, `divw_remw`) and validates the recipe for
the other three. Once this lands, the remaining 3 cores follow the same
pattern, then **Phase 3c** (8 thin `spec.<variant>_poly` wrappers) and
**Phase 4** (8 `correct_<variant>_poly` chip theorems) become mechanical.
DivRem is the third-to-last chip (with ShiftLeft / ShiftRight) blocking
the field-genericization effort declaring 22 chips.

A prior session attempted this and pulled back —
`feedback_divrem_core_port_blockers.md` documents three specific tactical
landmines. This plan addresses each upfront so the port can be done in
one focused 2–3h block.

The aux lemma `div_mod_decomposition_w_poly` already landed (commit
`ab6def6`, line 1143 of `SP1Chips/DivRem/Constraints.lean`). All
`Word.<helper>_poly` companions (`extend_*_poly`, `lt_cases_of_isU64_poly`,
`isU64_of_cases_poly`, `toBitVec64_poly_toNat_poly`,
`toNat_reconstruct_poly`, `toNat_poly_lt_of_isU64_poly`) and
`combine_MUL_MULHU_poly` already exist in `SP1Foundations/`.
`tdiv_tmod_unique_full_nat` (line 1180) is field-agnostic — usable as-is.

## Critical files

- `SP1Chips/DivRem/Constraints.lean` — add `divu_remu_poly` immediately
  after `divu_remu` (line 2442). Local helpers go just above.
- Reference: `divu_remu` Fin KB body at lines 2134–2442 (310 lines).
- Reference: `div_mod_decomposition_w_poly` recipe at lines 1143–1178
  (showcases `val_sub_cases` + `Fact (2^17 < p)` pattern).

## Proof structure

`divu_remu_poly` will mirror the Fin KB body verbatim with three
upfront-prep `have` blocks resolving the blockers, plus mechanical
substitutions throughout.

### Stage 1 — Upfront prep (resolve all 3 blockers before starting)

Add these `have`s right after `intro divu_remu` and before the `obtain`:

```lean
have h01 : (1 : ZMod p) ≠ 0 := one_ne_zero
have h21 : (2 : ZMod p) ≠ 1 := by
  intro h
  have : ((2 : ℕ) : ZMod p).val = ((1 : ℕ) : ZMod p).val := by push_cast; rw [h]
  rw [ZMod.val_natCast_of_lt (by have : 2^17 < p := Fact.out; omega),
      ZMod.val_natCast_of_lt (by have : 2^17 < p := Fact.out; omega)] at this
  omega
have h65535_val : ((65535 : ℕ) : ZMod p).val = 65535 :=
  ZMod.val_natCast_of_lt (by have : 2^17 < p := Fact.out; omega)
have h32768_val : ((32768 : ℕ) : ZMod p).val = 32768 :=
  ZMod.val_natCast_of_lt (by have : 2^17 < p := Fact.out; omega)
-- Lift each carry bit's `cry_i = 0 ∨ cry_i = 1` to a `.val ≤ 1` form
-- BEFORE simp_all can collapse the Fact (2^17 < p) instance.
have hcv0 : cry0.val ≤ 1 := by rcases b_cry0 with h | h <;> simp [h]
have hcv1 : cry1.val ≤ 1 := by rcases b_cry1 with h | h <;> simp [h]
-- ... hcv2..hcv7 likewise
```

These resolve **Blocker 1** (the (1,1)/(0,0) `simp_all` cases),
**Blocker 2** (the all-65535 `rfl` closure in c=0 branch), and
**Blocker 3** (cry_i.val ≤ 1 lifting needed before omega in 8-way
end-game). Putting them BEFORE any `simp_all` keeps `Fact (2^17 < p)`
from collapsing to `Fact True`.

### Stage 2 — Mechanical Fin KB → ZMod p substitutions

Walk the 310-line body and apply (sed-like) substitutions:

| Fin KB | ZMod p |
| --- | --- |
| `Word.isU64` | `Word.isU64_poly` |
| `Word.toBitVec64` | `Word.toBitVec64_poly` |
| `Word.toNat` | `Word.toNat_poly` |
| `Word.toBitVec64_toNat` | `Word.toBitVec64_poly_toNat_poly` |
| `Word.toNat_reconstruct` | `Word.toNat_reconstruct_poly` |
| `Word.toNat_lt_of_isU64` | `Word.toNat_poly_lt_of_isU64_poly` |
| `Word.lt_cases_of_isU64` | `Word.lt_cases_of_isU64_poly` |
| `Word.isU64_of_cases` | `Word.isU64_of_cases_poly` |
| `Word.extend_false_is_setWidth` | `Word.extend_false_is_setWidth_poly` |
| `combine_MUL_MULHU` | `combine_MUL_MULHU_poly` |
| `DWord.toBitVec128` | `DWord.toBitVec128_poly` |
| `DWord.toBitVec128_toNat` | `DWord.toBitVec128_poly_toNat_poly` |
| `DWord.isU128_of_cases` | `DWord.isU128_of_cases_poly` |
| `Fin.val_add` | (drop; use step-by-step `ZMod.val_add_of_lt`) |
| `Fin.val_mul` | `ZMod.val_mul` |
| `Fin.ext_iff` | (drop; use `ZMod.val_injective` |
| `Nat.mod_eq_of_lt (b := 2130706433)` | (drop; the `_poly` helpers don't introduce `% p`) |
| `div_mod_decomposition_w` | `div_mod_decomposition_w_poly` |

### Stage 3 — Targeted patches at the three blocker sites

**Blocker 1 site (line 2317)** — replace
```lean
rcases b_is_divu <;> rcases b_is_remu <;> simp_all
```
with
```lean
rcases b_is_divu <;> rcases b_is_remu <;>
  first
    | simp_all
    | (exfalso; rw [show (1 + 1 : ZMod p) = 2 from by ring] at divu_remu; exact h21 divu_remu)
    | (exfalso; exact h01 divu_remu.symm)
```

**Blocker 2 site (lines 2326–2329)** — replace
```lean
subst c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3
simp [Word.toBitVec64_toNat is_U64_b]
simp [Word.toBitVec64, Word.toNat]
rfl
```
with
```lean
subst c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3
simp [Word.toBitVec64_poly_toNat_poly is_U64_b, Word.toBitVec64_poly,
      Word.toNat_poly, h65535_val]
-- Now goal is BitVec arithmetic over Nat; close with bv_decide or rfl
rfl
```

**Blocker 3 site (lines 2402–2442)** — the `Nat.mod_eq_of_lt (b := 2130706433)`
calls become unnecessary because `ZMod.val_add_of_lt` produces `Nat`-side
sums directly without `% p` residue. Replace
```lean
simp [Fin.val_add]
iterate 4 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
```
with `ZMod.val_add_of_lt`-driven rewrites that produce the same shape:
```lean
-- Lift each (a + b - c * 65536 + d).val to a.val + b.val - c.val * 65536 + d.val
-- using a chain of ZMod.val_add_of_lt + val_sub_cases + val_mul.
```

The 8-way `b_cry3` rcases at lines 2417–2442 become straightforward
once `hcv0..hcv7` are in scope:
```lean
rcases b_cry3 with of | nof <;> subst cry3 <;> simp at *
· have : ctq4 = 0 := by clear *- nof_eq_ctqpr4 is_U64_ctqh hcv4
                         obtain ⟨_, h⟩ := nof_eq_ctqpr4; clear h
                         apply ZMod.val_injective; rw [ZMod.val_zero]; omega
  -- ... (mirror Fin KB structure with hcv4..hcv7 in scope for omega)
```

### Stage 4 — Build configuration

```lean
set_option maxHeartbeats 32000000 in
set_option debug.skipKernelTC true in
lemma divu_remu_poly ...
```

The 32M heartbeats matches the Mul precedent (`core_mul_poly`); the
`skipKernelTC` bypasses kernel deep-recursion on `% 2^N` (precedent:
`AddrAddOperation`).

### Stage 5 — Iterative debug

Do **NOT** try to write all 310 lines in one shot. Instead:
1. Write the upfront prep (Stage 1).
2. Write the literal port body (Stage 2 substitutions).
3. Run `lean_build` or use `lean_diagnostic_messages` repeatedly,
   fixing one error at a time. The mid-proof states reveal which simp
   lemmas/literal `.val` bridges are missing.
4. After every 10–15 lines that compile, snapshot context — kernel
   timeouts get worse as the proof grows.

## Available helpers (already landed, just need to reference them)

In `SP1Foundations/Field.lean`:
- `val_sub_cases` (line 301) — branches on whether subtraction wraps
- `Fact (2^17 < p)` instance for KB (line 319), `Fact (2^24 < p)` (line 327)

In `SP1Foundations/Word.lean`:
- `Word.{toBitVec64_poly_toNat_poly, toNat_reconstruct_poly,
  toNat_poly_lt_of_isU64_poly, lt_cases_of_isU64_poly,
  isU64_of_cases_poly, extend_false_is_setWidth_poly}` —
  all are direct mirrors of their Fin KB counterparts.
- `DWord.isU128_of_cases_poly`, `DWord.toBitVec128_poly_toNat_poly`

In `SP1Foundations/SailM.lean`:
- `combine_MUL_MULHU_poly` (line 1015) — bridges MUL+MULHU to a 128-bit
  product equation.

In `SP1Chips/DivRem/Constraints.lean`:
- `div_mod_decomposition_w_poly` (line 1143) — replaces
  `div_mod_decomposition_w` 1:1 at the `.val =` level. Note the
  result is `a.val = b.val % 65536 ∧ c.val = b.val / 65536`
  (Nat-form), not the Fin KB `a = b % 65536 ∧ c = b / 65536`
  (Fin-form). Subsequent rewrites must adapt — when the original
  rewrites `at nof_eq_ctqpr*` and projects `.1` / `.2`, the new
  versions are at the `.val` layer and the Fin KB-style
  `simp [nof_eq_ctqpr0.1, ...]` becomes a simp on `Nat`-side
  equalities.
- `tdiv_tmod_unique_full_nat` (line 1180) — pure ℕ/ℤ. **Use as-is**.

## Verification

After the lemma compiles:

```bash
# 1. File-local elaboration check
lake env lean SP1Chips/DivRem/Constraints.lean

# 2. Full build to confirm no upstream regression and zero linter
#    warnings (repo policy: warnings count as errors)
lake build 2>&1 | tee build.log
grep -cE '^(error|warning):' build.log   # must be 0

# 3. Confirm the lemma is reachable via lean MCP:
#    mcp__lean-lsp__lean_verify with declaration name
#    SP1Chips.DivRem.Constraints.divu_remu_poly
```

Commit message: `divrem aux _poly: divu_remu_poly (Phase 3b first core)`.

## Risk & checkpoints

- **Highest risk**: Stage 3 (the 3 blocker sites). If after 2 hours
  any blocker is still open, **stop and commit a `sorry`-marked
  partial** with a checkpoint comment, update
  `feedback_divrem_core_port_blockers.md` with the new sticking point,
  and surface to the user before continuing. Don't extend the session.
- **Heartbeat-tuning hazard**: if `32M` is insufficient, try `64M`
  before considering structural simplification. Don't lower
  `skipKernelTC`.
- **Out-of-scope**: do NOT touch `div_rem`, `divuw_remuw`, or
  `divw_remw` in this PR. They follow once `divu_remu_poly` is the
  validated template.
