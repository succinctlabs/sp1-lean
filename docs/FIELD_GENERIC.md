# Field-genericization effort

A running document for the multi-phase effort to lift this formalization off the
`Fin KB` (KoalaBear) field and onto an arbitrary prime field. Updated at every
phase boundary. The implementation roadmap is in
`~/.claude/plans/make-a-plan-to-soft-aho.md`.

## Current state — 2026-05-01 (Track A complete)

The additive `_poly` strategy is the chosen architecture: keep the existing
`Fin KB` definitions/lemmas in place and add `_poly` siblings parameterized
over `{p : ℕ} [Fact (Nat.Prime p)]` (often plus `[Fact (2^17 < p)]`). Zero
chip-side churn; the polymorphic surface exists for future reuse. Foundation
is complete; **operations layer is complete** — all 5 outstanding `_poly`
lemmas have landed (LtUnsigned/LtSigned cluster + BitwiseU16 cluster). The
chip layer has not been migrated. No second concrete prime field has been
instantiated yet — BabyBear / Mersenne31 remain forward-guidance.

**Track A progress (2026-05-01)**:
- ✅ `LtOperationUnsigned.spec_poly` (BitVec form) — closes via
  `spec.nat_poly` + `execute_RTYPE_pure_w_poly` (already in `SailM.lean`)
  with explicit `ZMod.val_one` / `ZMod.val_zero` discharge for
  `BitVec.ofNat 64 (1:ZMod p).val = 1#64` etc.
- ✅ `LtOperationSigned.spec.signed_poly` (the formerly "failed"
  natural-form lemma) — landed via structured `.val` arithmetic. Two
  helper lemmas inside the proof: (1) `(b3 + 32768 - 65536 * msb).val < 65536`
  case-split on `b3.val ≥ 32768` using `val_sub_cases` + `ZMod.val_add_of_lt`,
  (2) `((b3 + 32768 - 65536 * msb).val : ℤ) = b3.val + 32768 - (if b3.val ≥ 32768 then 65536 else 0)`.
  Then bridge `shifted_b.toNat_poly < shifted_d.toNat_poly ↔
  b.toInt_poly < d.toInt_poly` via the algebraic identity
  `shifted_w.toNat_poly = w.toInt_poly + 32768 * 2^48`. Heartbeats 4M.
- ✅ `LtOperationSigned.spec.branch_poly` — landed via two private
  helpers (`branch_helper_eq_iff_unsigned_poly` / `branch_helper_eq_iff_signed_poly`)
  that prove the `b = d ↔ all flags 0` iff for `is_signed = 0` and
  `is_signed = 1` separately. The `is_signed = 0` helper uses the fact
  that `h_msb_b_eq` / `h_msb_d_eq` force `cols.{b,c}_msb.msb = 0` so all
  shifts vanish; the proof then reduces to the standard 16-way flag-bool
  case-split with `linear_combination + val_k_ne_zero` discharging impossible
  cases. The `is_signed = 1` helper additionally handles the limb-3 shift
  case-split on `b[3].isNegative_poly`/`d[3].isNegative_poly` (4 sub-cases:
  2 give `b[3] = d[3]` directly via `linear_combination`, 2 are contradictions
  discharged via `val_sub_cases` + `ZMod.val_add_of_lt`). The `b ≠ d ↔
  flag-sum = 1` iff is derived contrapositively from the eq-iff plus the
  sum constraint. The if-then-else conclusion comes from `spec.unsigned_poly`
  / `spec.signed_poly`. Heartbeats 16M / 32M.
- ✅ `BitwiseU16Operation.spec.{and,or,xor}_poly` (3 lemmas) — **landed**.
  Required helper cascade landed in `SP1Foundations/Word.lean` and
  `SP1Operations/Operation/U16toU8OperationSafe.lean`:
  - `Word.{and,or,xor}_toBWord_poly` — trivial via
    `Word.toBitVec64_poly_toBWord_poly`.
  - `U16toU8OperationSafe.u16_to_u8_decomposition_poly` (private helper)
    + `spec.unsafe.return_poly` — closes via `mul_inv_cancel₀ val_256_ne_zero`
    + `ZMod.val_add_of_lt`/`val_mul_of_lt` for the byte-decomposition,
    then `(ZMod.natCast_zmod_val _).symm` to bridge byte vector equality.
  - The 3 spec lemmas follow the same recipe as the `Fin KB` versions:
    extract byte vectors via `spec.unsafe.return_poly`, peel off the 8
    byte-AND/OR/XOR equations, normalize byte values via
    `Nat.mod_eq_of_lt` (no Fin wrapping needed for ZMod p), set byte
    abbreviations, push through `BitVec.ofNat_{add,mul,and,or,xor}` simps,
    and close with `bv_decide`. OR/XOR additionally need
    `(1 : ZMod p).val = 1` / `(2 : ZMod p).val = 2` helpers (re-derived
    after `simp_all` strips the Fact instances). Heartbeats elevated to
    64M for each of the 3 spec lemmas.

### What is done

**Foundation (`SP1Foundations/`) — complete.** 736 `_poly` occurrences
across 7 files. Every signature consumed by the generic side has a `_poly`
sibling.

- `Constraint.lean`: `toProp_poly`, `toStateProp_poly`, `allHold_poly`,
  `initialState_poly`.
- `ByteOpcode.lean`: `constrain_poly` + 7 simp lemmas.
- `Assumptions.lean`: 5 `*_type_constraints_poly` + `Opcode.trusted_instr_poly`.
- `Word.lean`: `_poly` defs + ~50 `_poly` lemma companions across all 6
  namespaces (HWord/Word/DWord/BHWord/BWord/BDWord).
- `BitVec.lean`: Word-section `_poly` lemma counterparts.
- `SailM.lean`: 18 `_poly` execute/exec bridge lemmas (RTYPE, RTYPEW, ITYPE,
  SHIFTIOP, SHIFTIWOP, MUL, MULW + the `combine_*` helpers).
- `Field.lean`: polymorphic inverse-bridge primitives —
  `mul_inv_{4,65536}_eq_one_iff_poly`, `inv_{4,65536}_zero_or_one_poly`,
  `val_{2,3,4,8,256,65536}_ne_zero`, `val_sub_cases`, `small_nat_eq_zmod`,
  `val_ne_of_inv_mul_eq`, `CoeHead (Fin n) ℕ` / `CoeHead (ZMod p) ℕ` instances.

**Operations (`SP1Operations/`) — substantially complete.** All 21 ops in
`update_constraints.py`'s `PARAMETRIC_OPS` dict have **struct + auto-gen
Constraints** lifted to `(F : Type)` / `(F : Type*)`; the post-processor
preserves the lift across regens. Hand-written iff_poly companions landed
for:

- 5 reader iff_poly: `CPUState`, `RTypeReader`, `ITypeReader`, `JTypeReader`,
  `ALUTypeReader` (CPUState also has `_is_real_poly`).
- 6 bridge-coupled iff_poly: `AddOperation`, `SubOperation`, `AddwOperation`,
  `SubwOperation`, `AddrAddOperation`, `U16toU8OperationSafe`.
- 5 spec_poly: `IsZeroOperation`, `IsZeroWordOperation`,
  `IsEqualWordOperation`, `U16CompareOperation`, `U16MSBOperation` (+
  `spec.U64_poly`, `spec.gen_poly`).
- `LtOperationUnsigned`: `allHold_constraints_iff_poly`, `cl_are_U16_poly`,
  `spec.nat_poly`, `spec.nat.gen_poly`.
- `LtOperationSigned`: `allHold_constraints_iff_poly`, `spec.unsigned_poly`.

**Build health.** No `sorry`, no `stop`, no TODO/FIXME comments in
`SP1Foundations/`, `SP1Operations/`, or `SP1Chips/`. `lake build` was clean
(0 errors, 0 warnings, 8508 jobs) at the B.11 boundary 2026-04-28.

### What is not done

**0 deferred `_poly` lemmas remain** — all 5 outstanding ones from the
pre-Track-A list landed (LtUnsigned/LtSigned cluster + BitwiseU16 cluster).
Foundation + Operations are **complete**.

**Chip layer not migrated.** All 47 chip files still consume `Fin KB`-side
iff/spec lemmas. This is Track B — see "Recommended next steps" below.

**0 chips migrated to `_poly`.** All 47 chip files still consume
`Fin KB`-side iff/spec lemmas. No `correct_*` theorem has been re-stated.
The 2026-04-28 investigation revised this from a 1-session task to **4–6
sessions** and flagged that chip-level auto-gen `<Chip>/Constraints.lean`
remains `SP1ConstraintList (Fin KB)`-bound (chip-level parametric emission
was deemed out of scope).

**No second concrete field instantiated.** BabyBear / Mersenne31
instantiation remains stretch-goal forward guidance — see "How to
instantiate at a different prime field" near the bottom of this doc.

**`Fin KB` deletion sweep not started.** The original "fully agnostic" goal
was to delete the `Fin KB` versions in `SP1Foundations/` after migrating
consumers. Per the 2026-04-28 investigation, this is the same 4–6 session
blocker: each iff_poly migration is non-mechanical because of RHS-shape
divergence between `SP1Constraint.toProp` and `toProp_poly` post-simp.

### Recommended next steps

Three independent tracks, ordered by effort/value:

**Track A — Complete (landed 2026-05-01).** All 5 outstanding `_poly`
lemmas closed:

1. ✅ `LtOperationUnsigned.spec_poly` (BitVec form).
2. ✅ `LtOperationSigned.spec.signed_poly` (structured `.val` arithmetic
   via `val_sub_cases` + `ZMod.val_add_of_lt`).
3. ✅ `LtOperationSigned.spec.branch_poly` (16-way flag-bool + 4-way
   msb sub-case-split via two private helpers).
4. ✅ `BitwiseU16Operation.spec.{and,or,xor}_poly` (3 lemmas) — closed
   via `Word.{and,or,xor}_toBWord_poly` + `U16toU8OperationSafe.spec.unsafe.return_poly`
   + `u16_to_u8_decomposition_poly` helper cascade, then `bv_decide`
   over byte abbreviations.

End state achieved: zero deferred op `_poly` lemmas. Foundation +
Operations are **fully complete**.

**Track B — Pilot chip-side migration (2–3 sessions, validates the design).**
Migrate ONE simple chip end-to-end to `_poly` consumption:

1. Pick `SubChip` (smallest, uses one bridge-coupled op with iff_poly
   landed) or `AddiChip`.
2. Use the cleaner ascription idiom from the 2026-04-28 investigation:
   `(constraints Main).allHold_poly (p := KB)` instead of the verbose
   `(constraints Main : SP1ConstraintList (ZMod KB))` form.
3. Document the canonical migration template in this doc.

Outcome decides Track C scope: if mechanical given the iff_poly foundation,
fan out to all 23 chips. If the chip auto-gen `(Fin KB)` shape forces
ascription gymnastics in every proof, pivot to upstream chip-level
parametric emission or acknowledge the strategic shift.

### Track B preparation notes (handoff from Track A — 2026-05-01)

**Available iff_poly inventory** (everything chip proofs would consume):

- **Reader iff_poly**: `CPUState.allHold_constraints_iff{,_is_real}_poly`,
  `RTypeReader.allHold_constraints_iff_poly`,
  `ITypeReader.allHold_constraints_iff_poly`,
  `JTypeReader.allHold_constraints_iff_poly`,
  `ALUTypeReader.allHold_constraints_iff_poly`.
- **Bridge-coupled op iff_poly**: `AddOperation`, `SubOperation`,
  `AddwOperation`, `SubwOperation`, `AddrAddOperation`,
  `U16toU8OperationSafe` — all `allHold_constraints_iff_poly`.
- **Compare op spec_poly / iff_poly**: `IsZeroOperation.spec_poly`,
  `IsZeroWordOperation.spec_poly`, `IsEqualWordOperation.spec_poly`,
  `U16CompareOperation.{allHold_constraints_iff,spec}_poly`,
  `U16MSBOperation.{allHold_constraints_iff,spec,spec.U64,spec.gen}_poly`.
- **Lt op spec_poly cluster**: `LtOperationUnsigned.{allHold_constraints_iff,
  cl_are_U16,spec.nat,spec.nat.gen,spec}_poly` (BitVec form),
  `LtOperationSigned.{allHold_constraints_iff,spec.unsigned,spec.signed,
  spec.branch}_poly`.
- **Bitwise op spec_poly**: `BitwiseU16Operation.spec.{and,or,xor}_poly`.
- **U16toU8Safe spec helper**: `U16toU8OperationSafe.spec.unsafe.return_poly`.
- **SailM bridges**: 18 `_poly` execute/exec for
  RTYPE/RTYPEW/ITYPE/SHIFTIOP/SHIFTIWOP/MUL/MULW + combine helpers.

**Ascription pattern** (verified 2026-04-28 via `lean_run_code`):

```lean
-- Goal in chip proof: invoke the polymorphic allHold/initialState entry
have h_allHold : (constraints Main).allHold_poly (p := KB) := ...
have h_init : (constraints Main).initialState_poly (p := KB) s := ...
-- Then destructure h_allHold the same way h_cstrs.allHold gets used today
```

The named `(p := KB)` argument is what bridges `Vector (Fin KB) N` Main
rows to `(constraints Main : SP1ConstraintList (Fin KB))` consumed at
`p := KB` (since `Fin KB = ZMod KB` definitionally). Without it, Lean's
unifier doesn't solve `Fin KB ≟ ZMod ?p`.

**Chip auto-gen still `Fin KB`-bound.** `<Chip>/Constraints.lean` returns
`SP1ConstraintList (Fin KB)`. Track B works *around* this via the
`(p := KB)` ascription; it does NOT lift chip auto-gen. Lifting chip
auto-gen would require either upstream Rust changes or extending the
Python post-processor in `update_constraints.py` to handle chip-level
parametric emission — defer to Track C if needed.

**Recommended starting chip:** `SubChip` (76 lines, single
bridge-coupled `SubOperation` consumer). Successful pilot would touch:

1. Add `(constraints Main).allHold_poly (p := KB)` ascription in the
   `correct_*` proof body, replacing the current `h_cstrs.allHold` reference.
2. Destructure the polymorphic form, then specialize `SubOperation.allHold_constraints_iff_poly`
   to extract the carry/bit constraints.
3. Apply `CPUState.allHold_constraints_iff_is_real_poly` and the relevant
   reader iff_poly for the register/PC bookkeeping.
4. Bridge through `execute_RTYPE_pure_w_poly` (already in `SailM.lean`)
   for the SUB arm.
5. Watch for the 5 patterns in `feedback_poly_proof_patterns.md`
   (auto-memory): `simp_all` strips Facts; cstrs shadowing for
   `intro x; have x := x`; struct projection `simp only`; field-`<` to
   `.val <` conversion; `(N : ZMod p).val = N` helpers for `ByteOpcode.ofNat`
   reduction.

**Friction signals to watch for** (would suggest pivoting to Track C):
- Heavy `(p := KB)` ascription noise that bloats every proof line.
- `simp_all` cascades that strip critical instances and require manual
  re-derivation in 5+ places per proof.
- Chip auto-gen literals (e.g. `(2130673921 : Fin KB)`) requiring
  symbolic-inverse bridges in many places.

If the pilot is mechanical (~2–3 hr), fan out. If it requires substantial
new infrastructure, re-evaluate whether to lift chip auto-gen too.

**Track C — Strategic decisions to defer until A+B inform them.**

- **Foundation `Fin KB` deletion sweep** (4–6 sessions): only worth doing
  after Track B confirms the migration recipe.
- **Chip-level parametric emission** (cross-repo): extend
  `update_constraints.py`'s post-processor to chip-level structs, mirroring
  the operation-level treatment. Consider only if Track B finds chip
  auto-gen binding is the dominant friction.
- **BabyBear / Mersenne31 instantiation**: with the `_poly` foundation now
  in place, re-evaluate whether the existing `Fin <NewPrime>`-recipe should
  be replaced with a `ZMod <NewPrime>`-based one leveraging the polymorphic
  surface directly.

### Long-term goal

Everything in `SP1Foundations/*` should be agnostic to the prime field —
either generic over `ZMod p` (with specific `Fact` preconditions) or
generic over `(F : Type*) [Field F]` per lemma. `SP1Operations/*` and
`SP1Chips/*` make minimal instantiations needed (typically `F := Fin KB`
or `p := KB`). The user explicitly selected the parallel-additive `_poly`
companion strategy as the path; with Tracks A and B complete, the deletion
sweep in Track C is the final mile to that end state.

The chronological sub-phase log below (Sub-phase A through B.11) is the
historical record of what was tried, what failed, and why. Refer to it for
context on specific blockers; refer to the section above for the current
plan.

## Next session pickup

See "Current state — 2026-05-01" above for the canonical summary. The
chronological log below is preserved for historical context.

**Status as of 2026-04-28**: Phases 0-5 + Sub-phase A + Sub-phase B.2 +
B.3 + B.4 + **B.5b (4-op cascade)** + **B.5c (polymorphic `.val` helpers)**
+ **MemoryConsistency lift** + **Word.lean `_poly` def cascade across
all 6 namespaces (HWord, Word, DWord, BHWord, BWord, BDWord)** + **Word.lean
~50 `_poly` lemma companions** + **BitVec Word section `_poly` lemma
counterparts** + **SailM `_poly` execute_*_pure_w defs** + **Sub-phase B.6
(Foundation `_poly` cascade except MUL/MULW)** + **Sub-phase B.7
(MUL/MULW `_poly` cascade — Word/BWord extend_poly, Word.toBWord_poly,
combine_MUL_*_poly, execute_MUL_pure_bw_poly, execute_MULW_pure_bhw_poly,
exec_MUL/MULW_pure_bv_to_*_poly)** + **low-hanging-fruit sweep
(2026-04-28: removed orphaned `useless_signExtend{,_add}`, dropped unused
`inv_{8,256}BB_eq'` bridges in Field.lean, moved parametric emission for
the 5 hand-edited operations into `update_constraints.py`'s post-processor
so `PARAMETRIC_OPS` is now durable across regens — exclusion list gone)**
+ **Sub-phase B.8 (CPUState reader iff_poly pilot — first reader iff
companion lifted; struct + auto-gen lifted to `(F : Type*) [Field F]`;
both `allHold_constraints_iff_poly` + `_is_real_poly` close cleanly with
the canonical `simp [constraints, toProp_poly, sub_eq_zero, h13,
h0_lt_256, imp_and]`)** + **Sub-phase B.9 (bridge-free op struct +
Constraints lift cascade — `LtOperationUnsigned`, `LtOperationSigned`,
`U16toU8Operation`, `BitwiseOperation`, `BitwiseU16Operation` all lifted
to `(F : Type)` parametric form; `U16MSBOperation.allHold_constraints_iff_poly`
added)** + **Sub-phase B.10 (bridge-coupled op struct + Constraints lift
cascade — `Add`, `Sub`, `Addw`, `Subw`, `AddrAdd`, `U16toU8Safe` all
lifted to `(F : Type)` parametric form; polymorphic inverse-bridge
lemmas added in `Field.lean`; `AddOperation.allHold_constraints_iff_poly`
+ `SubOperation.allHold_constraints_iff_poly`
+ `SubwOperation.allHold_constraints_iff_poly`
+ `AddwOperation.allHold_constraints_iff_poly`
+ `AddrAddOperation.allHold_constraints_iff_poly`
+ `U16toU8OperationSafe.allHold_constraints_iff_poly` landed —
all 6 bridge-coupled iff_polys complete)** + **Sub-phase B.11
(deferred `_poly` cascade — 6 lemmas closed: `U16CompareOperation.spec_poly`,
`U16MSBOperation.{spec_poly, spec.U64_poly, spec.gen_poly}`,
`LtOperationUnsigned.{allHold_constraints_iff_poly, cl_are_U16_poly}`;
plus `Field.lean` primitives `small_nat_eq_zmod`, `val_2_ne_zero`,
`val_3_ne_zero`. Failure point: `LtOperationUnsigned.spec.nat_poly`
needs structured 16-case `.val`-level proof; aesop / linear_combination
recipes don't close it. 7 dependent lemmas deferred)** complete.
Sub-phase B Steps 1-2 (`.val` rephrase, parametric Word.lean lift)
attempted in earlier session, both reverted. `lake build` clean
(0 errors, 0 warnings, 8508 jobs).

**Sub-phase B.11 landed (2026-04-28)** — partial deferred `_poly` lemma
cascade (6 of 14 lemmas closed; 1 failed and 7 deferred):

**Closed (6 lemmas)**:

- `U16CompareOperation.spec_poly` — closes via case-split on
  `cols.bit ∈ {0, 1}` plus `val_sub_cases` for the wrap-around branch
  in `(a - b).val` (impossible when `a.val, b.val < 65536` and
  `p > 2^17`). The `cols.bit = 1` branch uses `ZMod.val_add_of_lt` for
  `(a - b + 65536).val`. Heartbeats elevated to 4M.
- `U16MSBOperation.spec_poly` / `spec.U64_poly` / `spec.gen_poly` —
  same case-split recipe as `U16CompareOperation.spec_poly`, with
  `(2 * a - cols.msb * 65536).val` analyzed via `ZMod.val_mul_of_lt`
  + `val_sub_cases`. The U64 / gen variants are short corollaries.
- `LtOperationUnsigned.allHold_constraints_iff_poly` — closes via the
  same `simp [..., toProp_poly]` recipe as the `Fin KB` version;
  mechanical port.
- `LtOperationUnsigned.cl_are_U16_poly` — 16-way case split on the 4
  boolean flags; the "sum ≤ 1" constraint discards 14 of 16 cases
  via `linear_combination + val_*_ne_zero` (see "Failed" finding below).
  Valid cases (0 or 1 flag = 1) close by `rw [← h_e0]; omega` /
  `rw [← h_e1]; omega`. Heartbeats elevated to 8M.

**Field.lean primitives added** to support this cascade:

- `small_nat_eq_zmod {n m : ℕ} (hn : n < 2^17) (hm : m < 2^17)` —
  `((n : ZMod p) = (m : ZMod p)) ↔ n = m`. Bridges field-level
  small-literal equalities to `ℕ`-level for `omega`.
- `val_2_ne_zero` / `val_3_ne_zero` — siblings of the existing
  `val_4_ne_zero` / `val_8_ne_zero` family, needed for the
  `(2/3 : ZMod p) ≠ 0` discharges in `cl_are_U16_poly`.

**Retry with `grind` + helper lemmas landed (2026-04-28)**: replaced
`aesop` with `grind` and added a `val_ne_of_inv_mul_eq` helper
(`not_eq_inv * (a - b) = 1 → a.val ≠ b.val`) to bridge the
field-level inequality from the constraint encoding to the Nat-level
inequality `grind` can use. The proof closes via 32-way case split
(16 flag combos × 2 sum-disjuncts × 2 inv-disjuncts), with
`grind` handling all valid cases. The `linear_combination + val_k_ne_zero`
recipe still discharges impossible flag-sum cases.

**Cascade landed via the unblocked `spec.nat_poly`**:

- `LtOperationUnsigned.spec.nat_poly` — 32-way case split, grind +
  optional `val_ne_of_inv_mul_eq` hint.
- `LtOperationUnsigned.spec.nat.gen_poly` — short corollary
  (`subst is_real; exact spec.nat_poly`).
- `LtOperationSigned.allHold_constraints_iff_poly` — mechanical port
  via `simp [..., toProp_poly]`.
- `LtOperationSigned.spec.unsigned_poly` (natural form, not BitVec) —
  with `is_signed = 0`, the msb constraints force
  `cols.{b,c}_msb.msb = 0`, so the `LtOperationUnsigned.spec.nat_poly`
  applies on the same `b, d` (zero msb-adjustment).

**Still failed mechanically (1)**:

- `LtOperationSigned.spec.signed_poly` (natural form, not BitVec) —
  the proof requires structured `.val` arithmetic for
  `(b[3] + 32768 - 65536 * cols.b_msb.msb).val < 65536` boundary cases:
  when `b` is negative (`b[3].val ≥ 32768`), the adjusted limb's val
  is `b[3].val + 32768 - 65536 ∈ [0, 32767]`; when positive, the val
  is `b[3].val + 32768 ∈ [32768, 98303]` — but neither case is
  decidable by `grind` without explicit `ZMod.val_add_of_lt` /
  `val_sub_cases` invocations. Estimated ~50–80 lines of manual proof.

**Deferred (5 lemmas)**:

- `LtOperationUnsigned.spec_poly` (BitVec form): bridges from the
  natural-form `spec.nat_poly` to BitVec via
  `BitVec.ofNat 64 cols.bit.val = execute_RTYPE_pure_w b d .SLTU`;
  needs polymorphic execute_RTYPE bridges.
- `LtOperationSigned.spec.branch_poly`: depends on `spec.signed_poly`
  (failed) and uses heavy BitVec rcases over flag combinations.
- `BitwiseU16Operation.spec.{and,or,xor}_poly` (3): proofs end in
  `bv_decide` after extensive setup using `Fin.val_add`, `Fin.val_mul`,
  `Nat.mod_eq_of_lt (b := 2130706433)` (KB literal!), `Fin.div_val`,
  etc. The `bv_decide` itself works on BitVec, but the setup requires
  polymorphic Fin → ZMod migration of the val arithmetic.

**Final B.11 tally**: 10 lemmas closed (was 6 in the initial round,
added 4 in the retry), 1 failed (spec.signed_poly), 5 deferred. The
critical insight that unblocked progress was using `grind` instead of
`aesop` plus the `val_ne_of_inv_mul_eq` helper to bridge field-level
inequality to Nat-level.

**Sub-phase B.10 landed (2026-04-28)** — bridge-coupled op cascade
(struct + Constraints lifts for all 6 ops; first bridge-coupled
`_poly` iff lemma landed):

**`Field.lean` polymorphic inverse bridges added** (under
`{p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]`):

- `mul_inv_65536_eq_one_iff_poly` — `x * (65536 : ZMod p)⁻¹ = 1 ↔ x = 65536`,
  via `mul_inv_eq_one₀ val_65536_ne_zero`.
- `mul_inv_4_eq_one_iff_poly` — same for `(4 : ZMod p)⁻¹`.
- `inv_65536_zero_or_one_poly` — disjunctive form for carry binarity.
- `inv_4_zero_or_one_poly` — disjunctive form for `(4 : ZMod p)⁻¹` carries.

**Critical**: NOT `@[simp]`. The polymorphic versions would fire on
`Fin KB` shapes (since `Fin KB = ZMod KB` definitionally) and shadow
the existing `mul_inv_16BB_eq_one_iff` family, breaking `Fin KB`-side
proofs that depend on the specific `(by trivial)` proof shape (confirmed
by SubOperation timing out under `@[simp]` poly attribute). Invoked
explicitly in `_poly` proof bodies instead.

**Lifted (struct + Constraints to `(F : Type)` parametric form)** — all
6 bridge-coupled ops:

- `AddOperation` — `value : Word F`. Iff lemmas ascribed
  `AddOperation (Fin KB)`. **`_poly` iff companion landed**
  (`allHold_constraints_iff_poly` closes via bare
  `simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly]` — the
  shape happens to be syntactically equal after simp normalization).
- `SubOperation` — same struct shape. **`_poly` iff companion landed**
  via a structured carry-bridging proof: pose both the borrow-form
  carries `d_i` (matching auto-gen) and the natural-form carries `c_i`
  (matching the iff RHS), prove `d_i = 1 - c_i` inductively via
  `linear_combination` against `inv_mul_cancel₀ val_65536_ne_zero`,
  show the borrow-form iff via bare `simp` (the `d_i` shape matches
  auto-gen verbatim), then bridge each carry-binary clause via the
  private `carry_swap_iff_poly` helper (`x = 1 - y → (x ∈ {0,1} ↔ y ∈ {0,1})`).
  Heartbeats elevated to 4M; well below the maximum.
- `AddwOperation` — embeds `U16MSBOperation F` (already lifted in B.9).
  Iff lemma ascribed `AddwOperation (Fin KB)`. **`_poly` iff companion
  landed** via bare `simp + tauto` — Add-style carries, U16MSB chain
  preserved verbatim in iff RHS via `List.Forall SP1Constraint.toProp_poly`.
- `SubwOperation` — same composite shape (2 carry limbs + embedded
  `U16MSBOperation` chain). **`_poly` iff companion landed** via the
  same carry-bridging recipe as Sub: `linear_combination` over
  `inv_mul_cancel₀ val_65536_ne_zero` for `d_i = 1 - c_i`, bare-simp
  borrow-form iff, then `carry_swap_iff_poly` per clause. Embedded
  `U16MSBOperation.constraints` chain is preserved verbatim in the
  iff RHS (uses `List.Forall SP1Constraint.toProp_poly` to mirror the
  `Fin KB` version's `List.Forall SP1Constraint.toProp`).
- `AddrAddOperation` — `value : Vector F 3`. Iff lemma ascribed
  `AddrAddOperation (Fin KB)`. **`_poly` iff companion landed** via
  bare `simp` — Add-style carries; the auto-gen carry shape matches
  the iff RHS verbatim. (`is_u48_sum` / `cols_is_a_sum_b` poly variants
  are not yet needed; the iff_poly suffices for chip-side migration
  when ready.)
- `U16toU8OperationSafe` — Constraints-only lift (no struct of its own;
  uses `U16toU8Operation F` from B.9). The hand-written iff lemma in
  `U16toU8OperationSafe.lean` consumes Constraints at `Fin KB`. The
  BV-decomposition lemmas (`u16_to_u8_decomposition_*` family) stay
  intentionally `Fin KB`-bound by design. **`_poly` iff companion
  landed** via `simp` plus a `(0 : ZMod p) < 256` helper (the U8Range
  opcode produces field-level `<`, the `0 < 256` term needs to be
  discharged explicitly because the `Fin KB` version sees it as
  `decide`-true automatically).

**`update_constraints.py` `PARAMETRIC_OPS` extended** with 6 entries
(all `("Type", False)` — no auto-gen call to `Opcode.ofNat` /
`ByteOpcode.ofNat`, so no `[CoeHead F ℕ]` injection needed).

**Downstream consumer pinning**: `AddressOperation.Operation.lean` had
`addr_operation : AddrAddOperation` → patched to
`addr_operation : AddrAddOperation (Fin KB)`. No other chip-side
fallout — chip auto-gen propagates `F := Fin KB` via constructor
inference on `Vector (Fin KB) N` Main rows.

**Verification**:

- `lake build` clean (0 errors, 0 warnings, 8508 jobs) post-cascade.
- `AddOperation.allHold_constraints_iff_poly` smoke-tested at `p := KB`
  and `p := 131101` (smallest prime > 2^17, primality via
  `native_decide`); both close via the same proof body.

**Outstanding work** (priority order, post-B.10):

1. ~~**Bridge-coupled `_poly` iff lemmas**~~ — all 6 landed (Add, Sub,
   Addw, Subw, AddrAdd, U16toU8Safe). Add/Addw/AddrAdd/U16toU8Safe
   close via bare `simp` (Add-style carries match auto-gen verbatim);
   Sub/Subw need the structured carry-bridging recipe
   (`linear_combination` + `carry_swap_iff_poly` helper) for the
   borrow-form ↔ natural-form sign-flip. U16toU8Safe needs an explicit
   `(0 : ZMod p) < 256` helper for the U8Range opcode's first arg.
2. **8 deferred `_poly` lemmas from B.5b/B.9** (was 14 — see B.11
   below). The remaining 8 are: `LtOperationUnsigned.spec.nat_poly` /
   `spec_poly` / `spec.nat.gen_poly`, all 4 `LtOperationSigned` `_poly`,
   and all 3 `BitwiseU16Operation.spec_*_poly`. Each requires
   structured `.val`-level case analysis that doesn't close via
   mechanical `aesop` or `linear_combination`. `val_sub_cases` from B.6 isn't
   yet exercised in a closed `_poly` proof.
3. **Foundation `Fin KB` deletion sweep** — 4-6 sessions per the
   2026-04-28 investigation block.

**Sub-phase B.9 landed (2026-04-28)** — bridge-free op cascade
(struct + Constraints lifts; mechanical-only `_poly` lemmas):

Per the plan, scope was the 5 bridge-free ops (`U16Compare`, `U16MSB`,
`LtUnsigned`, `LtSigned`, `BitwiseU16`) under "mechanical first, defer
tricky" stance — try `simp [constraints]; grind` for `_poly` lemmas;
defer per-lemma if the `(a-b).val` / `(2*a).val` Range-constraint
case-split blocks `grind`.

**What lifted (struct + Constraints to `(F : Type)` parametric form)**:

- `LtOperationUnsigned` — struct + auto-gen Constraints lifted; `Operation.lean`
  embeds `U16CompareOperation F`, `Word F`, `Vector F 2`. Iff lemmas
  ascribed `LtOperationUnsigned (Fin KB)` (no `_poly` companions added —
  proofs depend on `U16CompareOperation.spec_poly`, which gaps mechanically).
- `LtOperationSigned` — struct + auto-gen lifted; embeds
  `LtOperationUnsigned F` and `U16MSBOperation F`. Iff lemmas (`spec.unsigned`,
  `spec.signed`, `spec.branch` plus `spec.branch.def`) ascribed
  `LtOperationSigned (Fin KB)`. No `_poly` companions (depend on
  bridge-coupled `LtUnsigned` / `U16MSB.spec_poly`).
- `U16toU8Operation` (in `U16toU8OperationUnsafe/Operation.lean`) +
  `U16toU8OperationUnsafe/Constraints.lean` — leaf-op lift required for
  `BitwiseU16Operation`. `MulOperation` / `U16toU8OperationSafe` consumers
  pinned to `U16toU8Operation (Fin KB)`.
- `BitwiseOperation` + `BitwiseOperation/Constraints.lean` — leaf-op lift.
  `BitwiseChip` / `Bitwise/Constraints.lean` consume via call-site
  inference (no struct ascription needed).
- `BitwiseU16Operation` + auto-gen — embeds the 2 lifted leafs.
  `BitwiseU16Operation.lean` iff lemmas (`spec.and`, `spec.or`, `spec.xor`)
  ascribed `BitwiseU16Operation (Fin KB)`. No `_poly` companions
  (proofs use `bv_decide` over `Fin KB`-specific carry / shift arithmetic).

**`update_constraints.py` `PARAMETRIC_OPS` extended** with 5 entries:
`("Lt", "LtOperationUnsigned"): ("Type", False)`,
`("Lt", "LtOperationSigned"): ("Type", False)`,
`("Bitwise", "U16toU8OperationUnsafe"): ("Type", False)`,
`("Bitwise", "BitwiseOperation"): ("Type", True)`,
`("Bitwise", "BitwiseU16Operation"): ("Type", True)`. Future regens
preserve all lifts. `BitwiseOperation` / `BitwiseU16Operation` need
`[CoeHead F ℕ]` for `ByteOpcode.ofNat opcode` (mirroring the
program-using readers' precedent).

**`_poly` lemma companions added** (1 lemma):

- `U16MSBOperation.allHold_constraints_iff_poly` — landed. The Range
  constraint emits `.val < 65536` shape via `SP1Constraint.toProp_poly`,
  so the iff RHS states `(2 * a - cols.msb * 65536).val < 65536` at the
  `ℕ` level. Closes mechanically with `simp [constraints]; grind`.

**`_poly` lemmas attempted and deferred** (mechanical close blocked):

- `U16CompareOperation.spec_poly` — `simp [constraints]; grind` gaps on
  `(a - b + cols.bit * 65536).val ≤ 65535` Range case-split. Adding
  `val_sub_cases` to the simp set doesn't help — `grind` doesn't
  unfold the `if`-shape and apply the wrap-around branch. ~25 lines
  of structured `.val`-arithmetic + omega would close it.
- `U16MSBOperation.spec_poly` / `spec.U64_poly` / `spec.gen_poly` —
  same blocker on `(2 * a - cols.msb * 65536).val ≤ 65535`. Needs
  `ZMod.val_mul_of_lt` + `val_65536_ne_zero` plus case analysis on
  `cols.msb ∈ {0, 1}` to close.
- All 5 `LtOperationUnsigned` `_poly` lemmas — depend on
  `U16CompareOperation.spec_poly` (above) plus custom `.val` arithmetic
  for `cl_are_U16_poly`.
- All 4 `LtOperationSigned` `_poly` lemmas — depend on `LtUnsigned` /
  `U16MSB` `_poly` lemmas above.
- All 3 `BitwiseU16Operation.spec_*_poly` lemmas — proofs end in
  `bv_decide` over `Fin KB`-specific arithmetic; `_poly` form needs
  `_poly` versions of `Word.toBitVec64_toNat`, `Nat.lift_lt`, plus
  the `BitVec.ofNat_*` simp family already exists for both. Material
  work, not mechanical.

**Outstanding work** (priority order):

1. **Bridge-coupled op cascade** (6 ops: `Add`, `Sub`, `Addw`, `Subw`,
   `AddrAdd`, `U16toU8Safe`). Need polymorphic `inv_4BB_eq'` /
   `inv_65536BB_eq'` analogues in `Field.lean` first — likely
   `mul_inv_cancel₀ (h : (2^k : ZMod p) ≠ 0)` from `[Fact (Nat.Prime p)]`
   + the existing `val_*_ne_zero` family. Then struct + Constraints lift.
2. **Push the 14 deferred `_poly` lemmas** (U16Compare/U16MSB/LtSigned/
   LtUnsigned/BitwiseU16). Each is 20-40 lines of custom `.val`
   arithmetic; not mechanical.
3. **Foundation `Fin KB` deletion sweep** — 4-6 sessions per the
   2026-04-28 investigation block.

**Sub-phase B.8 landed (2026-04-28)** — all 5 reader iff_poly companions:

CPUState (the simple no-`program`/`memory`/`Word` reader) plus the four
`program`/`memory`/`Word`-bearing readers (RTypeReader, ITypeReader,
JTypeReader, ALUTypeReader). Closes the doc's "5 missing reader
iff_poly companions" gap.

**Per-file changes:**

- **CPUState** struct lifted to `(F : Type*)`. Auto-gen + 2 iff_poly
  lemmas. Closes via the simple `simp [..., h13, h0_lt_256, imp_and]`.
- **RTypeReader / ITypeReader / JTypeReader / ALUTypeReader** structs
  lifted to `(F : Type)` (Type, not Type*, because they carry `Word F`
  and `MemoryAccessInSharedCols F` which are `Type 0`-bound). Auto-gens
  hand-ported to `{F : Type} [Field F] [CoeHead F ℕ]`. Each `.lean` got
  one `allHold_constraints_iff_poly` companion (no `_is_real_poly`
  variant — the `Fin KB` versions of those use `simp_all` / `aesop` over
  the iff and we don't need separate `_poly` corollaries until a chip
  consumer demands them).
- **`SP1Foundations/Field.lean`**: added `CoeHead (Fin n) ℕ` and
  `CoeHead (ZMod p) ℕ` instances, plus `coeHead_zmod_eq_val` /
  `coeHead_fin_eq_val` simp lemmas. These let `Opcode.ofNat opcode`
  (which expects `ℕ`) elaborate against generic `F` for readers with
  `program` clauses, and let simp normalize `CoeHead.coe x` → `x.val`
  inside the iff_poly proof goals.
- **`update_constraints.py`**: PARAMETRIC_OPS schema extended to
  `Tuple[universe, needs_coe_head]`. Readers with `program` clauses
  get `[CoeHead F ℕ]` injected into the auto-gen def signature
  during regen.
- **`SP1Operations/Reader/ITypeReaderImmutable/Constraints.lean`**:
  added `(cols : ITypeReader (Fin KB))` ascription (was bare
  `ITypeReader`). Required because `ITypeReader` is now parameterized;
  consumer pinned to `Fin KB`. ITypeReaderImmutable itself is not
  lifted (no `_poly` consumer needed).
- **Zero chip-side fallout** in any of the 23 chip files. Chip-level
  `Vector (Fin KB) N` Main rows propagate `F := Fin KB` through reader
  `constraints` calls via type inference. The `[CoeHead (Fin n) ℕ]`
  instance synthesizes for `F := Fin KB` and `[CoeHead (ZMod p) ℕ]`
  synthesizes for `F := ZMod p` with `[NeZero p]`.
- **Smoke tests**: all 6 `_poly` lemmas (CPUState ×2 + RType + IType +
  JType + ALUType ×1 each) elaborate at `p := KB` and at
  `p := 131101` (smallest prime > 2^17, primality via `native_decide`).

**Two canonical reader iff_poly proof shapes** (from B.8):

**Shape A** — for simple readers (CPUState only, no `program`/`memory`
clauses): pure `simp` close.
```
lemma allHold_constraints_iff_poly ... := by
  have hN : (N : ZMod p).val = N := ZMod.val_natCast_of_lt (by ...)
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val; simp
  simp [constraints, SP1Constraint.toProp_poly, sub_eq_zero,
    hN, h0_lt_256, imp_and]
```

**Shape B** — for readers with `program`/`memory` clauses (RType, IType,
JType, ALUType): structured proof mirroring the original `Fin KB`
version. The pure `simp; tauto` doesn't close in lake build (despite
appearing to in `lean_run_code` due to env discrepancies — the test
harness is more lenient).

```
lemma allHold_constraints_iff_poly ... := by
  have h16 : (16 : ZMod p).val = 16 := ...
  have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := ...
  have h0_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := ...
  simp [constraints, sub_eq_zero, SP1Constraint.toProp_poly,
    h16, h0_lt_256, h0_lt_65536]
  intros h_is_real
  rcases h_is_real with h | h
  · simp [h]
    by_cases ha0 : cols.op_a_0 = 0
    · simp [ha0]
    · tauto
  · simp [h]
    by_cases hop_a_0 : cols.op_a_0 = 0
    · simp [hop_a_0]; aesop
    · simp [hop_a_0]; aesop
```

Notes for fan-out / future readers:
- **RHS-shape convention**: `Range`-opcode bounds appear as
  `.val`-level Nat comparisons after simp (since `constrain_poly_Range`
  produces `a.val < 2 ^ b.val`); state these in `.val < N` form.
  `U8Range`-opcode bounds and `program`-clause bounds (`< 32`,
  `< 65536`) stay field-level (since `constrain_poly_U8Range` and
  `toProp_poly`'s program arm yield field `<`).
- **`(1 : ZMod p)` ascription needed** in the iff RHS to avoid
  `HSub (ZMod p) ℕ` synthesis failure when literals back-propagate.
- **`hN`-style helpers**: `(N : ZMod p).val = N` for any small literal
  `N` not in `Field.lean`'s `val_*_zmod_p` family (currently 2, 4, 8,
  16, 32, 256, 65536). The 4 program-using readers all use `16`.
  CPUState uses `13`.
- **`attribute [-simp] Opcode.trusted_instr_poly`** required at
  module level for the 4 program-using readers — otherwise simp
  unfolds the giant `match`-on-Opcode body and the proof times out.
  CPUState doesn't use `program` so doesn't need this.
- **`imp_and` simp lemma**: only used in Shape A. Shape B's structured
  proof handles the implication shape via `intros` + `rcases`.

**2026-04-28 investigation (no code landed)**: piloted the Foundation
consumer migration toward "delete `Fin KB` versions" (item 2 in the
priority list below). Findings that re-shape the remaining work:

1. **Cleaner ascription idiom found.** The doc's verbose form
   `SP1ConstraintList.allHold_poly (p := KB) (constraints Main : SP1ConstraintList (ZMod KB))`
   is unnecessary. Dot notation with named arg works:
   `(constraints Main).allHold_poly (p := KB)` and similarly
   `(constraints Main).initialState_poly (p := KB) s`. The named arg fixes
   `p := KB` before the unifier sees the dot-notation argument, so the
   `Fin KB ≟ ZMod ?p` step succeeds via definitional `ZMod KB = Fin KB`.
   Verified at the LSP level via `lean_run_code` against `SP1Chips.Sub.Constraints`.

2. **Missing iff-lemma layer in `SP1Operations`.** Of 19 hand-written
   iff lemmas (Phase 3 audit), only 3 have `_poly` companions
   (`IsZeroOperation.spec_poly`, `IsZeroWordOperation.spec_poly`,
   `IsEqualWordOperation.spec_poly`). The remaining **16** must be added
   before chip-side migration is possible:
   - 5 Reader iff lemmas: `RTypeReader`, `ITypeReader`, `ALUTypeReader`,
     `JTypeReader`, `CPUState`.
   - 11 Operation iff lemmas: `LtOperationSigned`, `LtOperationUnsigned`,
     `U16CompareOperation`, `U16MSBOperation`, `BitwiseU16Operation`,
     `AddOperation`, `SubOperation`, `AddwOperation`, `SubwOperation`,
     `AddrAddOperation`, `U16toU8OperationSafe`.

3. **Iff-lemma RHS shape divergence.** The naive port (substitute
   `SP1Constraint.toProp_poly` for `SP1Constraint.toProp` in the LHS,
   keep RHS verbatim) does NOT close with the original `simp + tauto`.
   `simp [..., toProp_poly]` reduces to `.val`-level Nat comparisons
   (e.g. `ZMod.val ((cols.clk_0_16 - 1) * 8⁻¹) < 2 ^ ZMod.val 13`)
   while the original iff RHS uses field-level comparisons
   (e.g. `(cols.clk_0_16 - 1) * 8⁻¹ < 8192` with `Fin.instLT`/`ZMod.instLT`).
   These are definitionally equal at `p := KB` but not syntactically;
   `tauto` cannot close. **Confirmed on `CPUState.allHold_constraints_iff_poly`**:
   the simplest possible iff_poly attempt; `tauto` gap requires
   per-case `.val`-arithmetic massage. Each iff_poly is therefore
   a non-trivial proof, not a mechanical port.

4. **Keystone bridge `toProp_poly (p := KB) = toProp` requires recursive
   bridges.** Attempting a single Foundation-level lemma to identify the
   two `toProp` flavors at `p := KB` gets stuck in the `program` case:
   `trusted_instr_poly` and `trusted_instr` are different functions
   sharing structure, so `cases` + `rfl` doesn't close. The recursion
   continues: `trusted_instr_poly = trusted_instr` needs
   `*_type_constraints_poly = *_type_constraints` for each of 5 readers,
   and the `Word.isU64_poly = Word.isU64`, `Word.toBitVec64_poly = Word.toBitVec64`
   leaves. The "leaves" eventually bottom out in the `Fin.instLT`/`ZMod.instLT`
   discrepancy from finding 3, so even the leaves aren't pure `rfl`.
   Conclusion: there's no shortcut bridge that obviates per-iff work.

5. **Cross-repo chip auto-gen still `Fin KB`-bound.** The auto-gen
   `SP1Chips/<Chip>/Constraints.lean` files return
   `SP1ConstraintList (Fin KB)` (no parametric emission for chips —
   only operations got it via `update_constraints.py`'s post-process).
   The chip-side migration tolerates this via `(p := KB)` named arg
   (finding 1), but a strict reading of "Foundation agnostic, chips
   instantiate" would also lift the chip auto-gen. That requires
   either upstream Rust changes (the path Sub-phase A took for the
   `(Fin KB)` annotation, or B.2 took for inverse literals) or an
   extension of the Python post-processor to handle chip-level structs
   (currently `PARAMETRIC_OPS` is operation-keyed). Neither is in scope
   per existing decisions.

**Implication for the migration plan.** The original 3-5 hr estimate
in `~/.claude/plans/make-a-plan-to-shiny-biscuit.md` (Phase B alone
"~220 ascription rewrites") materially undercounted because:

- **Per-iff_poly cost ≈ 1-3 hr** for non-trivial readers/ops (per
  finding 3) × 16 = **16-48 hr**, not minutes per chip.
- **Per-chip migration cost** depends on how many internal lemmas the
  chip's proof body invokes; each one (e.g. `RTypeReader.allHold_constraints_iff_is_real`,
  `CPUState.allHold_constraints_iff_is_real`, `SubOperation.spec`)
  needs its `_poly` companion present.
- **Bridge-coupled operations** (`Add`/`Sub`/`Addw`/`Subw`/`AddrAdd`/`U16toU8Safe`)
  also need polymorphic `inv_*BB_eq'` analogues: e.g.
  `(65536 : ZMod p) ≠ 0` from `[Fact (Nat.Prime p)]` + `[Fact (65536 < p)]`,
  and the corresponding `ZMod`-side simp lemmas mirroring `inv_4BB_eq'`
  / `inv_65536BB_eq'`. B.6 added the *primitives* (`val_4_ne_zero`,
  `val_65536_ne_zero`, `val_sub_cases`); the bridge lemmas using them
  are not yet written.

**Revised effort estimate**: 4-6 sessions to complete consumer
migration + Fin KB deletion across `SP1Foundations/` (vs the prior
1-session plan).

**Recommended sequencing for the next session**:

1. Pick ONE simple reader (CPUState — only 2 facts in RHS, no
   bridge-coupled inverses) and write `allHold_constraints_iff_poly` +
   `allHold_constraints_iff_is_real_poly` with explicit `.val`-level
   RHS shape (matching simp's output). Land green build.
2. Pick ONE simple chip that uses ONLY CPUState (e.g. UTypeChip's
   simpler `correct_*` if any) — migrate it end-to-end as the canonical
   chip-side migration template. Note any extra simp dispatch needed.
3. Write up the canonical template patterns in this doc (chip
   prologue ascription pattern, iff_poly RHS-shape conventions,
   downstream destructure pattern) so subsequent sessions can fan out
   the cascade mechanically.

**Stated end goal (2026-04-27)**: everything in `SP1Foundations/*` should
be agnostic to the prime field — either generic over `ZMod p` (with
specific `Fact` preconditions) or generic over `(F : Type*) [Field F]`
per lemma. `SP1Operations/*` and `SP1Chips/*` make minimal instantiations
needed (typically `F := Fin KB` or `p := KB`). The user explicitly
selected path (a) — parallel-additive `_poly` companions — as the
strategy, with scope expanded as needed.

**Sub-phase B.7 landed (2026-04-28)** — MUL/MULW `_poly` cascade
(the explicit "except" in B.6's scope):

- **`Word.lean`** added `_poly` companions for:
  - `DWord.isU128_of_cases_poly`, `BDWord.isU128_of_cases_poly`
    (sibling-of-cases bound-construction lemmas).
  - `Word.extend_poly` + `Word.extend_U64_U128_poly` +
    `Word.extend_true_is_signExtend_poly` +
    `Word.extend_false_is_setWidth_poly` (sign/zero-extension to 128 bits).
  - Same four lemmas for `BWord.extend_poly`.
  - `Word.toBWord_poly` + `toBWord_poly_toU64` + `toNat_poly_toBWord_poly`
    + `isNegative_poly_toBWord_poly` + `toBitVec64_poly_toBWord_poly`
    (cross-namespace Word→BWord conversion).
  - `BWord.low_as_setWidth_poly`.
- **`SailM.lean`** added `_poly` companions for:
  - `combine_MUL_MULH_poly`, `combine_MUL_MULHU_poly` (the heavy
    `bv_decide`-based DWord-pair recombination lemmas).
  - `execute_MUL_pure_bw_poly` (def) + `exec_MUL_pure_bv_to_bw_poly`
    (BV→BWord bridge for MUL).
  - `execute_MULW_pure_bhw_poly` (def) + `exec_MULW_pure_bv_to_bhw_poly`
    (BV→BHWord bridge for MULW).
- **Three key technique findings**:
  1. The `extend_true_is_signExtend_poly` proof initially failed via the
     `BitVec.toInt_inj` route because `simp_all [isNegative_poly]`
     normalized `(w[i].val : ℤ)` to `w[i].cast` (the `ZMod p → ℤ`
     algebraic-cast), which doesn't unify with the rest of the proof
     state. The fix: route the proof through `BitVec.toNat_signExtend`
     instead — a Nat-level bridge that avoids `.cast`.
  2. `Word.toBWord` uses `% 256` and `/ 256` on `Fin KB`. For `ZMod p`,
     `Mod` is custom (Field.lean) and works via `.val`, but `Div` is
     field-division (multiply-by-inverse) — semantically wrong for byte
     extraction. The polymorphic `toBWord_poly` lifts to `ℕ` via `.val`,
     does the arithmetic in `ℕ`, then casts back to `ZMod p`.
  3. Cross-namespace BV↔Word conversion lemmas (the
     `exec_*_pure_bv_to_*_poly` family) originally needed
     `set_option debug.skipKernelTC true in` to bypass kernel deep
     recursion, matching the precedent from B.6. **Superseded
     2026-04-30**: cleared in pass 3 of the kernel-TC audit by lifting
     SLT/SLTU/SRA arms to bare-`BitVec 64` private helpers in
     `SP1Foundations/SailM.lean`. See `docs/GOTCHAS.md` for the
     remediation playbook.

**Smoke tests passed** at `p := KB` for all six SailM bridge lemmas:
`combine_MUL_MULH_poly`, `combine_MUL_MULHU_poly`,
`exec_MUL_pure_bv_to_bw_poly`, `exec_MULW_pure_bv_to_bhw_poly`.

**Sub-phase B.6 landed (2026-04-27)** — Foundation `_poly` cascade:

- **`Field.lean`**: added `val_sub_cases` (case-split helper for
  `(a - b).val` over `ZMod p` under `[NeZero p]`) plus polymorphic
  non-zero bridges `val_4_ne_zero`, `val_8_ne_zero` (mirroring
  `val_65536_ne_zero` / `val_256_ne_zero`).
- **`Word.lean` BWord cross-namespace**: previously deferred lemmas
  `BWord.toNat_poly_toWord_poly`, `BWord.toWord_poly_U64_poly`,
  `BWord.toWord_poly_toBitVec64_poly` now landed. Plus the BWord low/high
  cluster: `isU64_low_isU32_poly`, `setWidth_eq_low_poly`,
  `isU64_high_isU32_poly`, `setWidth_rshift_eq_high_poly`. The blocker
  was per-limb `(a + b * 256).val` decomposition; resolved via a private
  `val_byte_combine` helper using `ZMod.val_add_of_lt` /
  `ZMod.val_mul_of_lt` under `[Fact (2 ^ 17 < p)]`.
- **`Word.lean` toNat_reconstruct_poly**: lifted, sibling of
  `Word.toNat_reconstruct`. Reconstructed vector uses
  `((N : ℕ) : ZMod p)` natural-cast literals; closes via
  `ZMod.val_injective` + `ZMod.val_natCast_of_lt` + `omega`.
- **`Word.lean` `BWord.toWord_poly`**: instance requirement weakened
  from `[Field F]` to `[CommRing F]` since the body only uses ring
  ops + `OfNat`. Avoids unnecessary `[Fact (Nat.Prime p)]` propagation
  through downstream lemmas.
- **`SailM.lean` bridge cascade**: all 5 `exec_*_pure_bv_to_w_poly`
  bridge lemmas landed (`RTYPE`, `RTYPEW`, `ITYPE`, `SHIFTIOP`,
  `SHIFTIWOP`). The kernel "deep recursion" blocker on RTYPE/RTYPEW
  was initially worked around via `set_option debug.skipKernelTC true
  in` (matching the existing `exec_RTYPE_pure_bv_to_bw` precedent);
  this guard was retired in pass 3 of the kernel-TC audit
  (2026-04-30) by lifting the SLT/SLTU/SRA arms to bare-`BitVec 64`
  private helpers — see `docs/GOTCHAS.md`. SHIFTIOP/SHIFTIWOP use
  `Word.isU64_of_cases_poly` + `Nat.mod_eq_of_lt` to discharge the
  `(shamt.toNat : ZMod p).val < 2^16` side condition.
- **Smoke tests passed** at `p := KB` and `p := 7` (small-prime
  wrap-around branch of `val_sub_cases`). All five new SailM bridge
  lemmas elaborate at `ZMod KB`.

**Remaining work toward that goal** (order = recommended priority):

1. ~~**BitVec.lean `useless_signExtend*` theorems**.~~ **Done
   (2026-04-28)** — both deleted; zero external call sites confirmed
   pre-deletion.
2. **Migrate Foundation consumers and delete `Fin KB` versions**
   (~3-5 hr). For each function with both `Fin KB` and `_poly` versions
   in `Constraint.lean`, `ByteOpcode.lean`, `Assumptions.lean`,
   `Word.lean`, `SailM.lean`, etc., change chip/op callers to use the
   generic version, then remove the `Fin KB` version. End state: those
   files reach the user's "fully agnostic" goal. ~57 chips to touch
   (mechanical but bulk). Caveat: per B.6 finding, the unifier
   sometimes fails on chip-side complex terms — explicit ascription
   needed (`SP1ConstraintList.allHold_poly (p := KB) (constraints Main : ...)`).
3. **Operation/chip `_poly` cascade for ops with byte-opcode `Range`
   constraints** — **partially unblocked by B.6**. The `val_sub_cases`
   primitive now lands in `Field.lean`, providing the missing
   `(a-b).val` case-split. Per the prior B.5b finding, `grind` couldn't
   close `spec_poly` for U16Compare / U16MSB / Add / etc. without it.
   Next attempt: pilot `U16CompareOperation.spec_poly` using
   `val_sub_cases` + the existing `val_*_zmod_p` simp family. If `grind`
   still gaps, add a tactic-friendly forward rule (`from
   (a - b).val < N with N < p/2 derive b.val ≤ a.val ∧ a.val - b.val < N`).
4. ~~**Cross-repo upstream parametric emission**.~~ **Done (2026-04-28)**
   — implemented in `update_constraints.py` instead of upstream Rust. The
   script now ships a `PARAMETRIC_OPS` map keyed by `(chip, operation)`
   with universe annotation, plus an `apply_parametric_post_process`
   helper that rewrites `Fin KB` → `F`, injects `{F : <universe>} [Field F]`
   on the `def constraints` line, and parameterizes the `cols` struct
   type. Verified byte-zero diff vs the 5 hand-edited
   `Constraints.lean` files on `IsZeroOperation`, `IsZeroWordOperation`
   (`Type`), `IsEqualWordOperation` (`Type`), `U16CompareOperation`,
   `U16MSBOperation`. The `update_constraints.py` exclusion list is
   gone. `Type` vs `Type*` split is structural — `IsZeroWord` /
   `IsEqualWord` carry `Word F` parameters and `Word T` is defined
   over `T : Type 0`, so they cannot be lifted to `Type*` without
   first lifting `Word`. Harmonization to `Type*` was attempted and
   reverted.

**Low-hanging-fruit cleanup also landed (2026-04-28)**:

- `Field.lean` `inv_8BB_eq'` and `inv_256BB_eq'` deleted — both had
  zero external call sites. `inv_4BB_eq'` (7 uses in BranchChip) and
  `inv_65536BB_eq'` (9 uses in BranchChip / Sub / Subw) kept. The
  `@[simp]` family (`mul_inv_16BB_eq_one_iff`, `inv_16BB_zero_or_one`,
  `inv_mul_{2,3,8,16}BB_eq_iff'`) kept — load-bearing for chip omega
  proofs per the file's own comment block.

**What was attempted but doesn't currently work** (recorded for future
sessions to avoid re-discovering):

- `_poly` proofs for ops with byte-opcode `Range` constraints
  (U16Compare, U16MSB, etc.) do not close with `simp [constraints];
  grind` even after the `.val` helpers landed. The remaining blocker
  is `(a-b).val` arithmetic — **partially unblocked by B.6's
  `val_sub_cases`** (Field.lean). Next attempt should retry one of the
  deferred ops with `val_sub_cases` rewriting + `omega`.
- ~~`exec_RTYPE_pure_bv_to_w_poly` direct port hits kernel deep recursion
  during `aesop`.~~ **Resolved in B.6**, then cleaned up in pass 3 of
  the kernel-TC audit (2026-04-30): the original `set_option
  debug.skipKernelTC true in` prefix was retired by lifting SLT/SLTU/SRA
  arms to bare-`BitVec 64` private helpers, so the polymorphic instance
  graph never appears in the proof term. All 5
  `exec_*_pure_bv_to_w_poly` bridges land without the option. **For any
  future cross-namespace bridge that hits the same kernel issue, follow
  the playbook in `docs/GOTCHAS.md`** — `skipKernelTC` is no longer the
  recommended workaround and is not present in the build.
- ~~`BWord.toNat_poly_toWord_poly` / `BWord.toWord_poly_U64_poly`
  (BWord→Word cross-namespace conversions) need per-limb
  `ZMod.val_add` / `ZMod.val_mul` decomposition under
  `[Fact (65536 < p)]`. An inlined `aux` helper had unification
  issues during `simp`.~~ **Resolved in B.6**: a private
  `val_byte_combine` helper packaging `ZMod.val_add_of_lt` +
  `ZMod.val_mul_of_lt` under `[Fact (2 ^ 17 < p)]` closes the
  decomposition cleanly. The `simp only` call needs the explicit
  `Vector.getElem_mk` / `List.getElem_*` lemmas to reduce
  `#v[..][i]` indexing.
- **Chip-side migration to `_poly` versions**: Tested in this session.
  Lean's unifier *does* solve `Fin KB ≟ ZMod ?p ⇒ ?p := KB` in
  isolation (e.g. `(cs : SP1ConstraintList (Fin KB)) →
  SP1ConstraintList.allHold_poly cs` elaborates), but **fails when
  applied to chip-side complex terms** like
  `(constraints Main).allHold_poly` for
  `Main : Vector (Fin KB) 33`. The fix that works is an explicit
  ascription: `SP1ConstraintList.allHold_poly (p := KB)
  (constraints Main : SP1ConstraintList (ZMod KB))`. This ascription
  is verbose, and replacing it triggers cascading type mismatches in
  the chip proof body (since downstream lemmas like `spec`,
  `allHold_constraints_iff_is_real` are still `Fin KB`-typed).
  **Conclusion**: migration is technically feasible but non-trivial —
  each chip needs both signature ascription AND a poly-companion
  cascade for every internal lemma it consumes. Recorded as item 4 in
  the recommended next-step list.

**Critical finding from B.5b** (revises the prior claim that the cascade
is "mechanical" with proofs that "carry verbatim"):

The B.4 pilot succeeded specifically because `IsZeroOperation` does only
**pure field-equality reasoning**. For ops whose iff lemmas reference
byte-opcode `Range` constraints (`a.val < 2^b.val`) — including
`U16CompareOperation`, `U16MSBOperation`, `LtOperationSigned`,
`BitwiseU16Operation`, and the bridge-coupled arithmetic ops
(`Add{,w}`/`Sub{,w}`/`AddrAdd`/`U16toU8Safe`) — the `_poly` proof
**does not** carry verbatim from `Fin KB` to `ZMod p`. The blocker:

1. `(16 : ZMod p).val = 16` only when `p > 16`. For small `p`, `2^16.val`
   collapses, and `grind` cannot reason about the bound.
2. `(a - b).val` over `ZMod p` requires case-split on `a.val ≥ b.val`
   (mathlib's `ZMod.val_sub` only fires under that hypothesis); the
   `Fin KB` proof never has to do this case-split because grind has
   `KB`'s concrete value baked in.
3. Even with a strong precondition like `[Fact (131072 < p)]`, the
   `_poly` proof needs custom case analysis using `ZMod.val_sub`,
   `ZMod.val_natCast_of_lt`, etc., and is ~20–40 lines per op rather
   than `simp [constraints]; grind`.

What B.5b actually delivered:

- Struct + auto-gen lift for 4 ops (`U16CompareOperation`,
  `U16MSBOperation`, `IsZeroWordOperation`, `IsEqualWordOperation`)
  to `(F : Type)` / `(F : Type*)` parametric form, mirroring the B.4
  IsZeroOperation pilot template.
- `spec_poly` companions for `IsZeroWordOperation` and
  `IsEqualWordOperation` only (pure field-equality, `simp; grind`
  closes).
- All downstream consumers (`LtOperationUnsigned`, `LtOperationSigned`,
  `MulOperation`, `AddwOperation`, `SubwOperation`) pinned to
  `(Fin KB)` per the IsZeroWord pilot pattern.
- `update_constraints.py` exclusions for the 4 lifted ops, mirroring
  the IsZeroOperation exclusion. Future regens preserve the cascade.

What B.5b explicitly skipped (deferred):

- `spec_poly` for `U16CompareOperation`/`U16MSBOperation` — Range
  constraint `.val`-arithmetic blocker.
- Structural lift for `LtOperationSigned`, `BitwiseU16Operation`,
  `LtOperationUnsigned`, `AddwOperation`, `SubwOperation`,
  `MulOperation`, `U16toU8OperationSafe` — composite ops that embed
  the leaf ops. Lifting them requires either (a) lifting all transitive
  embedded ops simultaneously (high churn), or (b) keeping their
  structs at `Fin KB` while their auto-gen still calls leaf-op
  `constraints` with `F = Fin KB` inferred (the B.5b strategy).
- Bridge-coupled arithmetic op cascade (`Add`, `Sub`, `Addw`, `Subw`,
  `AddrAdd`) — the bridge-free finding above implies the bridge-coupled
  proofs would have the same `.val`-arithmetic blocker.
- All 5 reader `_poly` iff lemmas — same blocker (readers consume the
  Range/program-interaction predicates).

**Outstanding work** for a future session that wants to push this further:

1. **Structural-only lift for remaining ops.** Mechanical, just bigger
   in scope (each leaf op like `AddOperation`, `SubOperation`,
   `AddrAddOperation` is a clean lift; composite ops like `MulOperation`
   need the embedded-op pinning pattern). Delivers fully polymorphic
   auto-gen layer; chip side stays at `Fin KB`. Budget: ~30 min/op × 9
   ops = ~5 hr.
2. **Polymorphic `.val`-arithmetic helpers.** Add to `Field.lean` (or
   a new `Field.Polymorphic.lean`):
   - `(N : ZMod p).val = N` simp lemmas under `[Fact (N < p)]` for
     N ∈ {2, 4, 8, 16, 32, 256, 65536}.
   - `(2^k : ZMod p).val = 2^k` analogues.
   - `ZMod.val_sub` case-split helper packaged as a tactic or
     `aesop`-safe forward rule.
   - Likely `[Fact (2^17 < p)]` is sufficient for everything in scope
     (KB and BabyBear both ≥ 2^31).

   With these in place, the deferred `spec_poly` lemmas become tractable
   (~10–20 lines each instead of ~40).

3. **Cross-repo upstream parametric emission.** `~/Documents/sp1`
   constraint compiler change to emit `{F : Type*} [Field F]` directly
   for operation-level constraints. Eliminates the
   `update_constraints.py` exclusion list and makes the cascade durable
   without manual re-edits after every regen.

4. **Reader `_poly` iff lemma cascade.** Blocked on item 2 (same
   `.val`-arithmetic issue). Once unblocked, mechanical: 5 readers ×
   one iff lemma each.

**Recommendation**: pick up with item 2 (`.val`-arithmetic helpers in
`Field.lean`). Item 1 is mechanical but doesn't unblock anything for
the polymorphism story; item 2 is the missing primitive that the rest
of the `_poly` cascade depends on. Item 3 is cross-repo and orthogonal.

**What landed in Sub-phase B.4 (this session)**:

- **Additive `_poly` strategy chosen over signature replacement.** The
  original plan (in `~/.claude/plans/make-a-plan-to-scalable-emerson.md`)
  proposed lifting `toProp` etc. in place + `_KB` wrappers for chip
  compatibility. Surface-area scoping showed ~1000 chip-side call sites
  to `Word.isU64`/`toBitVec64`/`toNat` — the unifier-failure mitigation
  via `_KB` wrappers would have required churning all of them. Instead,
  added polymorphic `_poly` companions alongside existing `Fin KB`
  versions: zero chip-side churn, the polymorphic surface exists for
  proof reuse, and the existing `Fin KB` instance graph + bridges in
  `SP1Foundations/Field.lean` stay load-bearing.
- `SP1Foundations/Field.lean`: added `instance ZMod.instLE (p : ℕ) [NeZero p]`
  alongside the existing `instLT`/`instMod` — needed for the `b >= 128`
  clause in `ByteOpcode.constrain`.
- `SP1Foundations/ByteOpcode.lean`: added `ByteOpcode.constrain_poly` +
  7 polymorphic `constrain_poly_*` simp iff lemmas under
  `{p : ℕ} [NeZero p]`.
- `SP1Foundations/Word.lean`: added `Word.isU64_poly`, `Word.toNat_poly`,
  `Word.toBitVec64_poly` under `{p : ℕ} [NeZero p]`. Definitions only
  (no companion lemmas yet) — minimum surface to support `toProp_poly`
  and `toStateProp_poly`.
- `SP1Foundations/Assumptions.lean`: added 5 polymorphic
  `*_type_constraints_poly` (i, shift_i, w_shift_i, r, b) +
  `Opcode.trusted_instr_poly`.
- `SP1Foundations/Constraint.lean`: added `SP1Constraint.toProp_poly`,
  `SP1Constraint.toStateProp_poly`,
  `SP1ConstraintList.allHold_poly`,
  `SP1ConstraintList.initialState_poly` over `{p : ℕ} [NeZero p]`.
  Plus polymorphic simp lemmas `toProp_poly_assertZero`,
  `toProp_poly_send_byte`. The `toStateProp_poly` clause for memory
  uses `addr0.val < 32` (Nat-level) rather than `addr0 < 32`
  (field-level) so the `BitVec.ofNatLT` proof witness is directly
  available regardless of `p`'s value.
- `SP1Operations/Compare/IsZeroOperation.lean`: added `spec_poly`
  alongside the existing `Fin KB` `spec`. Both use
  `simp [constraints]; grind` and close cleanly. Smoke-tested at
  `ZMod 7` (a small prime distinct from KB) — elaborates without proof
  changes.
- **No call-site changes anywhere.** All 57 chip `correct_*` theorems
  unchanged. The `_poly` surface is parallel-additive.

**Smoke-test verification** (via `lean_run_code` on the live LSP):

```lean
example {p : ℕ} [Fact (Nat.Prime p)] [NeZero p] (x : ZMod p) :
    (SP1Constraint.assertZero x).toProp_poly ↔ x = 0 := by simp

example (x : ZMod 7) : (haveI : Fact (Nat.Prime 7) := ⟨by decide⟩;
    (SP1Constraint.assertZero x).toProp_poly) ↔ x = 0 := by simp
```

Both close. `IsZeroOperation.spec_poly` applies at the same shape.

**Outstanding work** (deferred — natural cascade now that the
foundation is in place):

1. **Cascade `_poly` to remaining 13 operation iff lemmas.** Per the
   Phase 3 audit (line 412), the candidates are
   `IsZeroWordOperation`, `IsEqualWordOperation`, `U16CompareOperation`,
   `BitwiseU16Operation`, `U16MSBOperation`, `LtSigned`, `LtUnsigned`,
   `Add`, `AddrAdd`, `Addw`, `Sub`, `Subw`, `U16toU8Safe`. Each needs:
   - Struct lift to `(F : Type*)` mirroring `IsZeroOperation` (B.3
     pilot).
   - Auto-gen `Constraints.lean` lift to `{F : Type*} [Field F]`
     (mirroring `IsZeroOperation/Constraints.lean`).
   - `_poly` iff lemma + `_poly` spec lemma where present.
   - Add to `update_constraints.py`'s exclusion list (mirroring the
     `IsZeroOperation` exclusion at lines 55-58).
   - The 5 ops using `inv_*BB_eq'` bridges (`Add`, `AddrAdd`, `Addw`,
     `Sub`, `Subw`, `U16toU8Safe`) need polymorphic bridge equivalents
     in `Field.lean` — likely via `mul_inv_cancel₀` + `(2^16 : ZMod p) ≠ 0`
     hypothesis from `[Fact (Nat.Prime p)]` + `Nat.Prime.two_le`.
2. **Cascade `_poly` to 5 reader iff lemmas.** `RType`, `IType`,
   `JType`, `ALUType`, `CPUState` — these consume the polymorphic
   `*_type_constraints_poly` and `trusted_instr_poly` already in place.
3. **Upstream parametric emission** (cross-repo). The auto-gen
   `Constraints.lean` currently emits `Fin KB`. To productionalize the
   `_poly` cascade, change `~/Documents/sp1`'s emitter to take a
   `field_param: bool` flag and emit `{F : Type*} [Field F]` + `F`-typed
   locals when set. This is the path to a clean BabyBear instantiation.

**Recommendation**: pick up with item 1 (operation iff lemma cascade).
The IsZeroOperation pattern is a few lines of mechanical change per
operation. Start with the bridge-free ones
(`IsZeroWord`, `IsEqualWord`, `U16Compare`, `BitwiseU16`, `U16MSB`,
`LtSigned`, `LtUnsigned`) before the bridge-coupled ones (`Add`,
`Sub`, etc.). Each operation is independent; the cascade can run in
parallel if useful.

**Cascade recipe per operation** (use IsZeroOperation as the canonical
template — its files are the diff template):

1. **Struct** (`SP1Operations/<Group>/<Op>/Operation.lean`): change
   `structure <Op>Operation where … : Fin KB` to
   `structure <Op>Operation (F : Type*) where … : F`. For composite
   fields (e.g. `is_zero_limb : Vector (IsZeroOperation (Fin KB)) 4`),
   propagate to the parameter: `Vector (IsZeroOperation F) 4`.
2. **Auto-gen `Constraints.lean`**: change the def signature from
   `(a : Word (Fin KB)) (cols : <Op>Operation) (is_real : Fin KB)
    : SP1ConstraintList (Fin KB)` to
   `{F : Type*} [Field F] (a : Word F) (cols : <Op>Operation F)
    (is_real : F) : SP1ConstraintList F`, retype all `let CSi`/`let Ei`
   bindings from `Fin KB` to `F`, and update the constructor calls
   (`{ inverse := … }` etc.) to use the parametric struct fields.
3. **Iff lemma** (`SP1Operations/<Group>/<Op>Operation.lean`): add a
   `<lemma>_poly` variant alongside the existing `Fin KB` version,
   parameterized over `{p : ℕ} [Fact (Nat.Prime p)] [NeZero p]` with
   types switched to `ZMod p`. Replace `SP1Constraint.toProp` with
   `SP1Constraint.toProp_poly` in the hypothesis. Keep the proof body
   identical; the same `simp [constraints]; grind` (or
   `simp [constraints]; intros; subst_vars; grind` for `.gen` forms —
   see `feedback_grind_ring_finkb.md`) closes it.
4. **`update_constraints.py` exclusion**: comment out the operation's
   row in the regen list (lines 55-58 region) with a note pointing to
   this doc. Ensures future regens preserve the parametric form.

**Bridge-coupled operations** (`Add`, `Sub`, `Addw`, `Subw`,
`AddrAdd`, `U16toU8Safe`): the iff lemma's RHS uses literals
like `(2^16 : Fin KB)⁻¹` (now `((65536 : Fin KB)⁻¹)` post-B.2). The
poly variant's RHS would have `((65536 : ZMod p)⁻¹)`. The proof
needs `(65536 : ZMod p) ≠ 0` — derivable from `[Fact (Nat.Prime p)]`
when `p > 65536`. Add a polymorphic bridge near `Field.lean`'s
existing `inv_*BB_eq'` lemmas:

```lean
lemma inv_16_eq_inv_65536 {p : ℕ} [Fact (Nat.Prime p)] [hp : Fact (65536 < p)]
    : ((1/65536 : ZMod p) : ZMod p) = (65536 : ZMod p)⁻¹ := by
  rw [one_div]
```

(Or whatever shape the proofs actually need; investigate at the first
bridge-coupled operation.) The `[Fact (65536 < p)]` hypothesis is
synthesized at `p := KB` since `65536 < KB = 2130706433` decides; for
BabyBear etc. the same fact decides on the concrete prime.

**What landed in Sub-phase B.3 (IsZeroOperation pilot, Lean side)**:

- `SP1Operations/Compare/IsZeroOperation/Operation.lean`: struct lifted to
  `structure IsZeroOperation (F : Type*) where inverse : F; result : F`.
- `SP1Operations/Compare/IsZeroOperation/Constraints.lean` (auto-gen):
  `constraints` def lifted to `{F : Type*} [Field F]` with all locals retyped
  `F`.
- `SP1Operations/Compare/IsZeroOperation.lean`: `spec` iff lemma kept at
  `Fin KB` (see "B.3 partial — iff-lemma blocker" below).
- `SP1Operations/Compare/IsZeroWordOperation/Operation.lean`: pinned the
  embedded struct to `Vector (IsZeroOperation (Fin KB)) 4` (one-line change).
- `update_constraints.py`: removed `IsZeroOperation` from the regen list (with
  a comment explaining the manual generic state) so the pilot survives
  future regens until upstream emits parametric output.

**B.3 partial — iff-lemma blocker.** Lifting `IsZeroOperation.spec` to
`{F : Type*} [Field F]` failed at elaboration with "argument `a` has type
`F` but expected `Fin 2130706433`". Root cause: the iff lemma uses
`List.Forall SP1Constraint.toProp (constraints a cols 1)`, and
`SP1Constraint.toProp : SP1Constraint (Fin KB) → Prop` is still
KB-instantiated by Phase 1 design (`SP1Foundations/Constraint.lean:41`).
That fixes the constraint list type to `Fin KB`, which in turn fixes the
operation `constraints` call's `F := Fin KB`, which mismatches `a : F`.
**Implication**: lifting iff lemmas requires lifting `toProp` /
`toStateProp` first. That pulls in:

- `Word.isU64` (parametric Word.lean lift, blocked on dot-notation
  unification — see "Sub-phase B — Step 1/2 attempt" below).
- `Opcode.trusted_instr` (currently `Fin KB`-typed).
- `ByteOpcode.constrain` (currently `Fin KB`-typed).
- `< 32` / `< 65536` / `% 4 = 0` literal comparisons (the ad-hoc
  `LT (ZMod p)` / `Mod (ZMod p)` instances landed in Sub-phase B Step 1/2
  cover these for `ZMod p`; for generic `[Field F]` they need typeclass
  extras).

Recommendation: the IsZeroOperation pilot demonstrated that the auto-gen
`constraints` def + struct can be made parametric without disturbing
chip proofs (the `IsZeroWordOperation` consumer pins `F := Fin KB` and
DivRemChip — which uses IsZero/IsZeroWord deeply — built clean). To
productionalize, the next two milestones are:

1. **Upstream parametric emission** (cross-repo, mirrors Sub-phase A and
   B.2): change `~/Documents/sp1`'s operation-level Lean emitter
   (`crates/core/compiler/src/main.rs:172` + `crates/core/compiler/src/ir/ast.rs:454-685, 921-1142`)
   to emit `{F : Type*} [Field F]` parameter and `F`-typed args/locals.
   This propagates to all operation structs at once, so it should be
   coupled with cascading the struct lift to all 19 operations
   (per `Phase 3 audit` table).
2. **`toProp` / `toStateProp` lift** to enable iff-lemma genericization.
   Bigger surface — pulls in `Word.isU64`, `Opcode.trusted_instr`,
   `ByteOpcode.constrain`. Either uses the ad-hoc `ZMod p`
   `LT`/`Mod` instances (Sub-phase B Step 1/2 landed these) or introduces
   a typeclass for `.val : F → ℕ` projection.

**What landed in Sub-phase B.2** (the focus of this session):

- **Upstream constraint compiler now emits `((N : Fin KB)⁻¹)` instead of
  the precomputed numeric inverse** — e.g. `* ((65536 : Fin KB)⁻¹)` instead
  of `* 2130673921`. Same for the four KB inverse literals (`(2^k)⁻¹` at
  `k ∈ {2, 3, 8, 16}`).
  - `crates/hypercube/src/ir/var.rs`: added `IrVar::InverseConstant
    { base: u32, value: F }` variant + Display + `to_lean`.
  - `crates/hypercube/src/ir/expr.rs`: added `to_lean_string` case.
  - `crates/hypercube/src/ir/expr_impl.rs`: `From<F> for Expr` checks if
    the field value is one of the four known KB inverse literals; if so,
    tags it as `InverseConstant`. The optimizer keeps seeing the eagerly
    computed numeric value; only the Lean output changes.
  - `crates/core/compiler/src/ir/ast.rs`: mirrored variant in the parallel
    AST tree (per Sub-phase A, both trees stay in sync).
- **48 auto-gen `*/Constraints.lean` files regenerated.** Diff is uniform:
  `* 2130673921` → `* ((65536 : Fin KB)⁻¹)` (and analogues for 4/8/256).
- **Hand-written iff lemmas migrated to symbolic form**: Reader files
  (`{RType,ALUType,IType,JType}Reader.lean`, `CPUState.lean`),
  `U16toU8OperationSafe.lean` (kept BV-level decomposition lemmas with
  literal `2122383361` since they prove the inverse value at the BitVec
  layer), and the Load{Byte,Half,Word,Double}/Constraints iff RHSes.
- **Chip proofs migrated**: `BranchChip` (12 `rw [← inv_2BB_eq']` calls
  removed; the `close_branch_addr_eq` macro and inline `simp + omega`
  patterns now apply `simp only [← inv_*BB_eq'] at <hyps>` to convert
  symbolic inverses back to literals before omega), `JalrChip` (literal
  `1598029825` references rewritten to `(4 : Fin KB)⁻¹`,
  `inv_mul_2BB_eq_one` replaced with `inv_mul_cancel₀`), `LoadByteChip`
  (30 occurrences of `2122383361` rewritten to `(256 : Fin KB)⁻¹`).
- **`SP1Foundations/Field.lean` bridges trimmed but not fully removed.**
  Original plan was "delete literal-side bridges, keep symbolic-side simp
  lemmas". In practice, the literal-side `inv_mul_*BB_eq_iff'` family
  (4 lemmas) had to stay `@[simp]` because chip omega proofs need to
  reason about `* (literal : Fin KB) = 1 ↔ ... = 65536` after the
  `← inv_*BB_eq'` symbolic→literal rewrite step. Other literal-side
  bridges (`shiftl_*BB_eq_one`, `inv_mul_*BB_eq_one`, `inv_mul_*BB_eq_iff`,
  `mul_inv_*BB_eq_one`, `inv_*BB_eq`, `inv_*BB_eq[']` for non-16BB) are
  gone. The `inv_*BB_eq'` family is renamed to `inv_*BB_eq'` with the
  same `(literal : Fin KB) = (N : Fin KB)⁻¹` shape (NOT `@[simp]`;
  invoked explicitly via `← inv_*BB_eq'` in proofs).
- **Symbolic-side `@[simp]` lemmas kept**: `mul_inv_16BB_eq_one_iff`,
  `inv_16BB_zero_or_one` (operate on `* (65536)⁻¹` form).

**End state**: zero hand-written occurrences of the four inverse literals
outside `SP1Foundations/Field.lean` (where they appear in the bridge
lemma bodies) and `SP1Operations/Operation/U16toU8OperationSafe.lean` (BV
decomposition lemmas, internal). Auto-gen produces `((N : Fin KB)⁻¹)`
syntactically. Switching to a different prime field would now only
require new bridge lemmas matching the new prime's inverse values; the
auto-gen output is unchanged at the Lean source level.

**Earlier sub-phase B notes** (preserved below for context but superseded
by the B.2 work above):

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
