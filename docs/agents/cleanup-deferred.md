# Deferred work — the owner-decision queue from the 2026-07 cleanup marathon

The `/cleanup-all` marathon (9 waves, 69 batch commits, 310 files, **net −8,396 lines**) ran under
[`cleanup-profile.md`](cleanup-profile.md), which forbids a worker from changing a statement, a name, a
visibility, or a `def` data body, and forbids deleting any declaration. Every duplication a batch found but
could not fix under those rules was logged rather than taken.

**This file is that log, distilled into decisions.** Each item says *what*, *where*, *how big* (measured, not
estimated — several were re-measured downward during the campaign and the corrected figure is what appears
here), *why it was not done*, and *what decision is needed*. Items are grouped by **blocker**, because the
blocker determines who can act.

Nothing here is a defect report. Everything here is intentional, and several items were reached
independently by three or more batches and stopped at each time — see §7.

Provenance: `git log --grep '^Wave:'` (108 commits with machine-parseable trailers). Elaboration-budget
guidance — how to fold a blowup rather than reach for a directive — is in
[`perf-findings.md`](perf-findings.md).

---

## 0. Partially discharged — the redundant-instance class

A post-marathon sweep removed **149 dead `Fact`/`NeZero` locals across 68 files** on this basis:
**`Fact p.Prime` synthesizes both `NeZero p` and `Fact (1 < p)` as instances, while `Fact (2 ^ N < p)`
synthesizes neither** (measured directly). The standard variable block carries `Fact p.Prime`
everywhere, so the `haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩` idiom is
redundant tree-wide. Only 3 sites were kept, all because the local is the sole consumer of the
`2 ^ N` instance and the linter's `omit` fix would change a signature.

**What remains in the same class, measured post-sweep** — no blocker, just unspent effort:

| remaining | count | note |
|---|---:|---|
| single-line `haveI : NeZero p` / `Fact (1 < p)` | **85** | 66 are in 4 files skipped on cost: `ShiftRightChip/Core.lean` (32), `ShiftLeftChip/Core.lean` (28), `DivRemChip/Soundness.lean` (5), `Completeness/Driver.lean` (1). The two shift `Core` files are the heaviest elaborations in the tree; a 32-site bisect is ~35 full re-elaborations, and DivRem-class files must run solo (recorded OOM risk). 10 more are a two-line variant. |
| `have hp : 2 ^ N < p := Fact.out` | **106** in 43 files | A *different* class — these feed a downstream bare `omega`, so expected yield is low but nonzero. Needs its own pass with the same byte-identical-output recipe. |
| `local instance : NeZero p` / `Fact (1 < p)` **declarations** | **68** | Dead by the same argument, but these are *declarations* and §2.3 forbids deleting one. **Owner decision** — retiring them is the clean end-state of this class. |

The recipe and driver tooling are documented in
[`proof-patterns.md`](proof-patterns.md) § "Golf & cleanup discipline". Note the instrument caveat
recorded there: **do not measure this class while a `lake build` is in flight** — it produces
one-directional spurious LIVE verdicts.

---

## 1. Blocked on a shallow shared file (`Math/` or `Model/`)

The dominant class. In each case the fix is *one* new public declaration in a file at depth 0–2, plus a
mechanical substitution at N call sites. A worker cannot do it because the home file is outside any per-file
batch manifest, and a per-file `private` copy would be superseded by the hoist. **Decision needed: schedule a
single round that owns the shallow file plus its call sites.** Subtotal ≈ **−700 lines**.

### 1.1 `interactionsWith_{general,assertion}Subcircuit_eq_nil` — 21 files, ≈ **−250**
*Where:* inline 12–15-line blocks whose entire content is "child *c* declares this channel neither as a
guarantee nor as a requirement, so it contributes no interaction". Counted: `JalChip` 7, `JalrChip` 7,
`UTypeChip` 7, `BranchChip` 6, `DivRemChip` 4 (was 9), 2 each in `Add`/`Addi`/`Addw`/`Sub`/`Subw`/
`Bitwise`/`Lt`/`Mul` `Formal.lean`, plus `Shift{Left,Right}Chip/Defs.lean`,
`Proofs/Operations/Shift{Left,Right}Operation/Core.lean`, `Soundness/TypedProgram.lean`,
`Soundness/TypedMemoryBalance.lean`.
*Home:* `Model/InteractionRecovery.lean`, which already owns the three base `interactionsWith_*Subcircuit_eq_nil`
lemmas; the two wrappers only specialise `ops := []` and apply `interactionsWith_nil`.
*Proof of shape:* W6/b2 extracted both locally in `DivRemChip/Formal.lean` (−41 lines there). Those two local
privates should be **deleted** in favour of the shared pair when it lands.
> ⚠ **Landmine.** With both `circuit` and `channel` implicit in `p`,
> `generalChild_nil Readers.CPUState.circuit programChannel.toRaw …` leaves `p` a metavariable and fails with
> `typeclass instance problem is stuck / FiniteField (ZMod ?m)`. The inline copies dodge this only via their
> explicit `([] : Operations (ZMod p))` argument. Fix: `(Readers.CPUState.circuit (p := p))` at each call site.

### 1.2 `mulPred` forward direction missing from `Math/Gate.lean` — ~50 sites / 20 files, ≈ **−50**
`Math/Word.lean:267` proves only the reverse (`bool_of_mul_pred` : `x * (x - 1) = 0 → x = 0 ∨ x = 1`). The
forward direction is re-derived inline as `rcases h with h | h <;> rw [h] <;> simp` in **~50 places across 20
files**: `ShiftRightChip/Core.lean` ×17, `BranchChip/Core.lean` ×9, `ShiftRightChip/Formal.lean` ×6,
`LoadByteChip`/`JalrChip` ×4, `LoadWordChip`/`LoadHalfChip` ×3, one each in
Add/Addi/Addw/Sub/Subw/Lt/Bitwise/Store{Byte,Half,Word,Double}/LoadDouble/ByteChip `Formal.lean`.
`BranchChip/Core.lean` even names a local copy `mulPred_of_bool` inside `completeness`.
*Home:* `Math/Gate.lean`, next to `bool_val_le` / `bool_eq_ite_of_iff`. A one-line addition.
Found independently by W4/b4 and W5/b5.

### 1.3 `hpcrun` — 41 sites repo-wide, ≈ **−41** *(revised down from −80)*
Every ALU/jump/U-type/Bitwise/Lt bridge opens its core theorem with the identical
`have hpcrun : (LeanRV64D.readReg Register.PC).run s = .ok pc s := by rw [run_readReg, h_pc]`, immediately
consumed by `TryStepReduction.run_bind_of_run`. Verified at **41 byte-identical sites** across all 25
`Proofs/Chips/*/Bridge.lean` (`AluX0Chip` 9, `DivRemChip` 8, `MulChip` 5, `Bitwise` 4, `Lt` 4,
`ShiftRight` 4, `Addw` 2, `ShiftLeft` 2, `Add`/`Addi`/`Subw` 1 each; `BranchChip` and `JalrChip` carry none).
*Home:* `Proofs/Sail/Advance.lean` — **already imported by all 25 bridges**.
*Shape:* the hypothesis is always literally `h_pc`, so the hoisted form wants
`(h_pc : s.regs.get? Register.PC = some pc)` explicit and each call site becomes `run_pc_of_get h_pc` — a
term, not a `have`. That is one full line per site, hence **−41, not the earlier −80 estimate**.

### 1.4 `persist_nextPC` / the `hpc_get` staging preamble — ⚠ **re-measure before acting**
The standing roadmap estimate was ≈−110 across nine `Bridge.lean` files. W5/b4 confirmed 8 inline 14-line
copies (`Load{Byte,Half,Word,Double}`, `Store{Byte,Half,Word,Double}`) and **normalised all eight to be
byte-identical**, so the substitution is mechanical; `LoadX0Chip/Bridge.lean:53` already carries the proved
`private lemma persist_nextPC` of exactly the right shape.
But W6/b2 found the estimate **counted at least one non-site**: `BranchChip/Bridge` carries a *different*
12-line variant (no `hsp_config`, extra `hsp_pc`) that is **not** a `persist_nextPC` call site, and
`DivRem`/`Mul`/`ShiftLeft`/`ShiftRight` carry no preamble at all. Only `JalrChip/Bridge` is a genuine extra
call site (17 lines, full shape).
*Decision:* re-count against the corrected site list, then hoist `persist_nextPC` public into `Model/`.
The name matches no `gen_axiom_probe.py` glob, so publicising it is probe-safe.

### 1.5 `filter_interactions_formalAssertion_eq_nil` preamble — ≈ −20 local / **−100 tree-wide**
A 4-line `heq` preamble repeated ~20 times across the `Faithful/` ALU anchors alone. Same shape as 1.1.
*Note:* also blocked by §2.8 in the `Faithful/` copies (see §4).

### 1.6 `equalityConstraint_mem` — 12 byte-identical private copies, ≈ **−60**
Identical statement and proof in
`Proofs/Chips/{Add,Addi,Addw,Sub,Subw,Lt,Bitwise,LoadByte,LoadWord,LoadHalf,LoadDouble,LoadX0}Chip/Contracts.lean`.
It is a statement about Clean's `Gadgets.Equality` only — nothing chip-specific. Every copy is `private`, so
retiring them later costs nothing outside those files.
*Home:* a shared module (`Model/`-side, or a small `Proofs/Chips/EqualityMembership.lean`).
A **13th and 14th** copy exists as `jalEqualityConstraint_mem` / `uTypeEqualityConstraint_mem` in one file,
`Soundness/Grounding/JTypeChips.lean` (W8/b2 made the second a one-line application of the first).

### 1.7 The `Math/Word.lean` `val_N_zmod_p` family has measured gaps
The single most-cited lever in the campaign is "the lemma already exists, it just is not cited". These are the
places where it *does not* exist:

| missing lemma | sites | note |
|---|---:|---|
| `val_6_zmod_p` | **33 sites / 31 `Faithful/` files** | the highest-multiplicity hand-rolled fact in the campaign; ≈ −60 to −90 lines. Also needs a §2.8 waiver (see §4) |
| `val_5_zmod_p`, `val_65280_zmod_p` | 24 | |
| `val_255_zmod_p` | 3 | hand-rolled in `MulOperation/RawSpec.lean` |
| `val_256_zmod_p`, `val_256_ne_zero` | — | logged as belonging to the family |
| `val_29_zmod_p` | 1 | exists as the private double-primed `Faithful.val_29''` in `AluX0.lean` |

`val_6_zmod_p` is the only one needing owner approval on both halves: (i) a new public `@[simp]` lemma in the
highest-blast-radius file in the tree, and (ii) 33 substitutions inside conservative-only anchors.
Run it as its own gated batch with a full build, like the `sixteen_lt` hoist.

### 1.8 `Math/Gate.lean`'s blanket `Mathlib.Tactic` import blocks its own reuse
`SP1Clean.bool_val_le` is exactly the lemma that 28 hand-rolled
`rcases h with h | h <;> rw [h] <;> simp [ZMod.val_one]` copies in `DivRemChip/Soundness.lean` wanted — and
its docstring says so. But `Math/Gate.lean` blanket-imports `Mathlib.Tactic` at depth 0, which is not in
`DivRemChip/Soundness.lean`'s closure, so importing `Gate` would pull the umbrella into a DivRem-class module.
A private duplicate `bool_val_le_aux` was added instead. **Narrowing `Gate.lean`'s imports** (it needs
`Mathlib.Data.ZMod.Basic` plus a handful of tactics) would let that duplicate be dropped, and the same lever
likely applies to other chips. Related: `Math/Misc.lean` and `Model/Machine/Schedule.lean` also blanket-import
`Mathlib.Tactic` at depth 0, and `Misc.lean` additionally imports `Mathlib.Data.ZMod.Basic`, which that
subsumes. Import minimisation on foundational leaves is a whole-tree rebuild-cost question — owner call.

### 1.9 `loadOpcode_pin_{one,two,four}` want one shared home *(perf, not lines)*
Extracted per-file by W5/b4 into `Load{Byte,Half,Word}Chip/Bridge.lean` because they are a genuine
**performance** root-cause fix — the inline `simp_all` ran against the whole post-`obtain` `advance` context,
and the extraction moved all three sites **FAIL@400000 → PASS@≤40000**. The clean end state is all three
beside `storeOpcode_pin_one` in `Model/Semantics/Decode.lean`, which already owns the store analogue and its
`storeOpcode_{one,two,four,eight}_toNat` family. `loadOpcode` has no `*_pin_*` lemma there — that asymmetry is
the actual defect.

---

## 2. Blocked by §2.1 — needs a statement change

A worker may never change a declaration's statement. These need someone who owns the statement.

### 2.1 `Soundness/WitnessDecode.lean` — two structurally identical inductions, ≈ **−20**
`constraints_of_mem_decodeInstructionTables` and `channelGuarantees_of_mem_decodeInstructionTables`
(lines ~155–175 / ~180–201) share the same `induction aligned with | nil | @cons`, the same
`rw [decodeInstructionTables, List.mem_append]`, the same `obtain ⟨physical, physicalMem, rfl⟩`, the same
`rw [← head.1, ← head.2]`, and differ only in `Table.Constraints` vs `Table.ChannelGuarantees channel`.
Unifying them needs a `(P : Operations → Environment → Prop)`-parameterised induction plus a `Table`-level
"per-row property transports across `component`/`data` equality" premise — a real generalisation of two
**public** statements, not a mechanical hoist.

### 2.2 `Soundness/Grounding/ALUTypeChips.lean` — the two timestamp-bounds theorems, ≈ **−25**
`aluTypeTimestampBounds_of_contract` and `immutableAluTypeTimestampBounds_of_contract` have ~30-line bodies
differing only in `Readers.ALUTypeReader` vs `Readers.ALUTypeReaderImmutable` and in
`binding env constraints` vs `binding env`. Merging changes a statement; a shared private core would have to
be parameterised over a `GeneralFormalCircuit` plus its `timestampSpecs_of_byteGuarantees` lemma.
**Deferred, not refuted.**
*Same file, same blocker:* the eight `consumedMessages_*Six` / `producedMessages_*Six` privates
(**≈ 130 lines**) differ only in the six-element list they are stated at.

### 2.3 `Faithful/MulChip.lean` `u16Value0`..`u16Value7` — eight lemmas, one proof body
`MulChip.lean:824-885`. Eight `private theorem`s over `Extracted.U16toU8OperationSafe.value`, indices 0–7,
each proved by the identical two-line `rw [Extracted.U16toU8OperationSafe.value]; rfl`. The **statements
genuinely differ** (even indices project `cols.low_bytes[k]`, odd ones `(w[k] - cols.low_bytes[k]) * 256⁻¹`),
so collapsing them is a quantified restatement plus a rewrite of ~30 `simp only` call sites — a statement
change *and* a proof-term restructure inside `Faithful/**`. MulChip-local; no sibling carries the family.

### 2.4 `Addw`/`Subw` `spec_populate` — one carry-chain proof written twice
Near-identical proofs in two namespaces (`Proofs/Operations/{Addw,Subw}Operation/Formal.lean`). Same shape
appears in the `Add`/`Sub` `Populate.lean` pair.

---

## 3. Blocked by §2.3 — needs a deletion

The campaign may not delete a declaration. Each of these is a genuine duplicate whose retirement requires one.

| # | what | where | size |
|---|---|---|---|
| 3.1 | Duplicate `HWord` definition — `SP1Clean.ShiftRightMath.HWord` + `.toNat` is byte-identical in body to `SP1Clean.HWord` / `.toNat`. The **sibling** `ShiftLeftChip/Core.lean` already `open`s the shared one, so the two shift cores are inconsistent. Consolidating means deleting and re-pointing `toBitVec32`. | `Proofs/Chips/ShiftRightChip/Core.lean:1638` vs `Math/HWord.lean:19,36` | — |
| 3.2 | `zero_ne_one'` — public copy in `BranchChip/Decision.lean` with a byte-identical **private** twin in `Proofs/Operations/LtOperationSigned/Formal.lean:66`. `Math/Gate.lean` already builds the same `Fact (1 < p)` instance, so hoist + rename is one decision. | two files | −10 |
| 3.3 | `expression_eval_{sub,mul,add}` are pointwise Clean's own `Expression.eval_{sub,mul,add}` (all `@[circuit_norm]`). W7/b2 already cashed the duplication the safe way (kept the local declaration, proved it *by* the real lemma). Deleting the three wrappers and citing Clean at the ~10 use sites is the remaining step. | `Proofs/Chips/LoadX0Chip/Contracts.lean` | −15 |
| 3.4 | A duplicate `@[simp]` declaration with the **same LHS** — simp-set pollution: two `@[circuit_norm]` entries for one fact. Three confirmed instances of this pattern tree-wide. | `FormalModel/Contracts/DivRem.lean` + 2 others | — |
| 3.5 | `ExtDHashMap_insert_insert_self` is the same statement as `Std.ExtDHashMap.insert_insert` in `Math/Misc.lean`, and is also mis-namespaced (root-namespace underscore spelling). Rename and de-duplication are one decision. | `Model/SailWrap.lean` | −5 |
| 3.6 | `InteractionRecovery.interactionsWith_main_snd_eq_nil` — **zero in-tree importers**; its docstring claimed a `@[circuit_norm]` tag it does not carry (claim removed). Tag it, wire it up, or retire it. | `Model/InteractionRecovery.lean` | — |
| 3.7 | Confirmed-dead declarations: one dead `private` in `ShiftRightChip/Populate.lean`; `local instance : NeZero p` in `Soundness/RowEffectDefs.lean:27` (measured dead by deletion + re-elaboration; it is `local`, so no importer sees it, and the file contains no theorem — **not** a §6 counterexample). | 2 files | −8 |

---

## 4. Blocked by §2.8 — `Faithful/**` is conservative-only

`Faithful/**` and `Native/Operations/*/RawSpec.lean` are *syntactic* faithfulness anchors: permitted edits are
dropping `by exact`, dropping a dead `let`, and `from by` → `by`. Restructuring a proof term is prohibited.
Everything below is real duplication or real cost that a normal golf would take.
**Decision needed: a scoped, audited waiver — or an explicit "these stay as they are, forever".**
Subtotal ≈ **−500 lines**, plus the tree's two largest remaining perf leads.

### 4.1 ⚠ The two most expensive anchors in the pillar — a bare-`simp` squeeze
`shiftRightCoreAssertions` (`Faithful/ShiftRightChip.lean:848`) and `shiftLeftCoreAssertions`
(`Faithful/ShiftLeftChip.lean:722`) each bind `let ops := (…).operations` and then run **bare `simp`** over it
three times, floors in (40k, 100k]. §2.6 *permits* `simp` → `simp only`; §2.8 blocks it here. Squeezing them
would very likely take both to ≤40000. **This is the highest value-per-effort item in the whole queue.**

### 4.2 ⚠ `divRemRustAssertionsDecompose` — the tree's highest-value single perf target
`Faithful/DivRemChip/Exact.lean:1128`. Measured floor **(8M, 16M]** — by a wide margin the most expensive
declaration in the pillar, and the one whose cost is best understood. It holds the fully
unfolded `Extracted.DivRemOracle.DivRemCols.asserts` list, rewrites ~80 reconfigure projections through it
with five `simp only` blocks, then runs **twenty consecutive bare `congr 1`** steps to peel a 20-way
`List.append` chain. Textbook cause class 1d.
*This one declaration is worth roughly half of the module's ~260s*, and that module is on the build's critical
path — a fold here would move the whole build. The fix (hide the RHS behind a `private def … : Prop`, or
replace the `congr 1` ladder with one `List.append` congruence helper applied symbolically) is a proof-term
restructure inside `Faithful/**`.

### 4.3 `divRemLower/UpperBackward` — one proof written twice, ≈ **−100**
`Exact.lean:1808` / `:1880`, ~180 lines. The same proof parameterised over `divRemLowerMulInput` vs
`divRemUpperMulInput`: identical `hEvalReal`/`hPlacement'`/`hReal'` preamble, identical
`mulOperation_assertions_backward` application with four byte-identical obligations, identical closing
`simpa only`. `divRemLower/UpperForward` are a second, smaller instance. Both twins measured at the **same**
floor bracket, consistent with being one proof written twice.

### 4.4 `Faithful/DivRemChip.lean` — the four roundtrip proofs' 22-line verbatim tail, ≈ **−66**
`divRem{Header,Comparison,Arithmetic,Result}Blocks_roundtrip` each end with a byte-identical block: twelve
`have hMul := divRemMulOperation_size` … size facts feeding the `omega` side conditions, then an identical
`repeat first | rw [Vector.getElem_append_left …] | rw [Vector.getElem_append_right …]` ladder. The only
per-site variation is the leading `simp only [divRemChipLocals, …]` and the closing
`all_goals try rw [divRem_toElements_*]`.
**Also the file's binding cost:** three of the four are its most expensive declarations, all
failing at `whnf` on their signatures — so an extraction is a genuine perf lead, not only a line win.
(The fourth, `divRemHeaderBlocks_roundtrip`, cleared 40000 and was removed: the header chunk's offsets all
land in the first `Vector` append arm, so its `rw` ladder terminates early.)

### 4.5 `Faithful/DivRemChip.lean` — three near-verbatim `eval_divRem*OfLocals`, ≈ **−70**
`eval_divRemIsC0OfLocals` / `eval_divRemIsOverflowBOfLocals` / `eval_divRemIsOverflowCOfLocals`
(`:685-791`, ~35 lines each). Identical end to end; they differ only in the local offset (159 / 137 / 148),
the `size` fact cited (both `= 11`), the `populatedRowAt_*_eq` lemma rewritten first, and the trailing summand
in the `change`'s index expression. A helper over a loose `(offset : ℕ)` plus a `populatedRowAt` projection
hypothesis retires two of the three. These are cheap to elaborate — a line-count lead only.

### 4.6 The `*_eta` structure-eta family — 8 files, ≈ **−120 to −150**
`vec3_eta` / `vec4_eta` / `vec16_eta` / `cpuState_eta` / `registerAccess_eta` / `rTypeReader_eta` appear as
`private` near-verbatim copies in `Faithful/{Mul,Lt,Jal,Jalr,Branch,ShiftLeft,ShiftRight,UType}Chip.lean`
(`MulChip` carries the largest instance, `:454-615`, ~160 lines). `cpuState_eta` is **statement-identical**
across all eight; only the proof spelling drifts (`rw [vec3_eta]` in MulChip vs `exact <…, vec3_eta _>` in
LtChip). A single shared public family in `Faithful/ChipTactics.lean` retires ~7 copies.
*Two independent blockers:* retiring copies means deleting declarations (§2.3), and the purely additive form
(add the shared lemma, leave all eight privates) nets **zero** lines. Call sites are the
`simp only [… _eta …]` blocks in each file's `*_constraints_faithful` / `*_interactions_*` anchors — 50 `_eta`
mentions in MulChip alone, 22 in LtChip, 12 in BranchChip.
> ⚠ Mind the `ChipTactics.lean` → `Faithful/CPUState.lean` import cycle: `ChipTactics.faithful_chip`
> hard-references `cpustate_constraints_faithful`, so CPUState cannot cite anything hoisted into ChipTactics.
> A partial correct hoist beats a forced general one.

### 4.7 Jal / Jalr / UType private boilerplate, triplicated — ≈ **−120 to −150**
`vec3_eta`, `vec4_eta`, `forallNilIff`, `varFields4`, `equalityMappedAssertions`.
> ⚠ Two same-named `private theorem`s exist in one namespace across the shift anchors
> (`nativeU16MSBAssertionList`, `u16MSBAssertions` in both `Faithful/ShiftLeftChip.lean` and
> `ShiftRightChip.lean`; they do not collide only because both are private and module-mangled). Hoisting would
> change which declaration each chip oracle cites **by name** — this needs care, not just a move.

### 4.8 `val_6_zmod_p` — 33 sites / 31 `Faithful/` files
See 1.7. Listed here too because the second half of the fix is 33 substitutions inside conservative-only
anchors: swapping a hand-rolled `have h6` for a lemma citation *does* restructure a proof term, however
trivially.

### 4.9 ✅ **FIXED at close-out** — a released docstring claimed scoped sorries that do not exist
*Status: this was the one deferred item promoted out of the queue and landed, as its own commit, at the end
of the campaign. It is recorded here because the finding — not the fix — is what a future auditor needs.*

`Native/Operations/MulOperation/RawSpec.lean`, `mulSemantics_of_raw`'s doc-comment **read**:
> "…the four high-half / `MULW` conjuncts are **scoped sorries** (they read further slices off the *full*
> 128-bit `product_reassembly`, deferred to a later pass)."

**This is false.** The file contains zero `sorry`; all five conjuncts are fully proved (MULHU/MULH/MULHSU
through `high_half_eq`, MULW through `product_reassembly` + `toBitVec64_signExtend_word`), and
`#print axioms SP1Clean.MulOperation.mulSemantics_of_raw` is `[propext, Classical.choice, Quot.sound]` —
verified — twice, independently, by the batch that found it and again by the close-out gate. It was a
leftover from a partial landing.

It was **deferred by the batch** because §2.8's conservative-only list does not cover docstring rewrites, and
then **promoted above the usual deferral bar** because the repo's headline claim is that every released
theorem is proof-complete with no `sorryAx`, and this was a released doc-comment on the MUL soundness core
asserting the opposite. An auditor reading `docs/verification-report.md` against the source would reasonably
have concluded MUL's high-half semantics were unproved. The replacement docstring states the true position
and names the axiom set.

**The general rule this establishes:** §2.8 protects *proof terms* in the faithfulness anchors, not prose. A
docstring that contradicts a released soundness claim is an audit-surface defect, and correcting it is never
a golf — it gets its own commit, its own re-verification, and a note in the commit message saying what the
false claim was.
*Same class, lower stakes:* two docstrings in `Native/Readers/RegisterAccessCols.lean` (`:30-32`, `:53`)
describe a witnessing circuit that no longer exists — `main` is an assertion with `localLength _ := 0` and
witnesses nothing, and the in-body comment at `:61-62` says so correctly.

---

## 5. Needs a cross-module round — a dependency *and* its importers together

`private` cannot cross a module boundary, and §4a's "prefer `private`" (which keeps the axiom census stable,
since `gen_axiom_probe.py` skips `private` lines) therefore **forces** duplication. That is an accepted cost
per-batch, but it accumulates. Subtotal ≈ **−560 lines**.

### 5.1 The `GroundingAdapter` + five-importer round — ≈ **−100**
Three confirmed forced duplications, all in `Soundness/Grounding/`:
1. `registerIndexCast` — the 3-line 5-bit register-index round-trip, hand-inlined 13× and now existing as
   **three** per-file `private` copies (`GroundingAdapter.registerIndexCast`,
   `ITypeChips.itypeRegisterIndexCast`, `ControlFlowChips.controlRegisterIndexCast`).
2. The `*Pull_one_signed` / `*Push_one_signed` twins — **5 copies of each** across the layer
   (`ControlFlowChips.immutableItype*`, `ITypeChips.itype*`, `ALUTypeChips.*`), byte-identical in statement,
   ~10 lines each ≈ **100 lines**.
3. `ControlFlowChips.rowAligned_immutableItype`'s four `hlocPrior*`/`hlocRead*` `have`s are
   `GroundingAdapter.locOf_rtypePriorMessage` / `locOf_rtypeReadBackMessage`. *(Re-declaring both helpers
   locally costs ~12 lines to save 8 — net positive, correctly not done.)*

**One wave owning `GroundingAdapter` plus its five Grounding importers could hoist the signed-multiplicity
family and the `locOf` family public and retire ~100 lines at once.** Items 1 and 2 are the concrete payload.

### 5.2 `store{Half,Word}Chip_storeMemoryGroundingData_of_eq` — ≈ **−140**
`Soundness/ChipContracts.lean` (~line 2650 and ~2784). **142 lines each, byte-identical modulo the
`storeHalf`/`StoreHalf` → `storeWord`/`StoreWord` name stem** — verified by a normalised `difflib` diff:
**0 hunks**. `StoreByte` and `StoreDouble` are *not* in the family (StoreByte carries the
byte-guarantee/`is_real` route; StoreDouble drops the prior-value block entirely).
*Blocker:* collapsing them needs a `local macro` that **derives ~12 declaration names from a stem**
(`<stem>Chip_viewOf_decoded`, `<Stem>Chip.circuit`, `<Stem>Chip.rowView`,
`<stem>Chip_immutableRamMemoryInteractionShape`, `<stem>Assumptions_env`,
`<stem>ChipDescriptor_assumptions_iff`, …) inside a `MacroM do` block — and the profile's own economics say
"don't declare a macro you use twice".
*Decision:* worth ≈ −140 to an owner willing to accept the name-derivation machinery.
> ⚠ 4.31: `String.take` returns a `String.Slice`, so `.toUpper` on it fails. Use `String.capitalize`.

### 5.3 The 24 missing `channelsWith*_eq` rfl-lemmas *(perf lead)*
`AGENTS.md`'s own recipe — "every circuit exposes its `channelsWith*` as `@[circuit_norm]` `rfl`-lemmas" — is
honoured by ~20 `Native/Operations/*` gadgets and by `MulChip`, and by **no other chip**.
Consequence: `Soundness/RowSoundness.lean:63 supportedChip_usesSupportedBusChannels` must feed each chip's
whole `circuit` *and* `elaborated` record to `simp`, and is the most expensive declaration in the `Typed*`
grounding family. Measured: squeezing `simp` → `simp only` already moved its floor (200k, 400k] → (100k, 200k]
and the file 8.28s → 5.84s, so **the remaining cost is exactly the record unfolding**. Adding the 24 missing
pairs in `Native/Chips/<Chip>/Defs.lean` should take it comfortably under the default.
*Related:* the same missing-rfl-lemma cause blocks Clean's `SoundEnsemble.addTable` autoParam defaults —
giving each provider circuit a `channelsWith{Guarantees,Requirements}_eq` would let **all 11** hand-written
`addTable` obligation arguments across `ByteChip/Ensemble.lean`, `MemoryProviderEnsemble.lean` and
`ProgramProviderEnsemble.lean` be **omitted**. Needs an owner and a full build (attribute changes were
suspended during parallel editing).

### 5.4 The four bit-op `Contracts.lean` near-clones — ≈ **−280**, cross-layer
`{Lt,Bitwise,ShiftLeft,ShiftRight}Chip/Contracts.lean` each carry the same six-declaration tail
(`physicalCols` / `physicalView` / `physicalView_isReal` / `rowViewOpA0_eq_zero_of_constraints` /
`rowViewSelectorActive_of_constraints` / `rowViewOpCBinding_of_constraints`) — ~330 lines total, ~85%
textually shared, differing only in chip name and selector arity. `Add`/`Sub`/`Subw`/`Addw`/`Addi` carry a
smaller shared triple.
*Blocker:* every one of those names is a **public** statement consumed by `Soundness/ChipContracts.lean` and
the three `Soundness/Grounding/*Chips.lean` modules. A `ChipKind`-parameterised generic is a cross-layer
redesign, not a golf.

### 5.5 `Soundness/TypedTime.lean` register-access descent — ≈ **−38**
Six reader theorems repeat, once per register access (3+2+1+2+3+3 = **14 times**), the same 7-line
`channelGuarantees_subcircuit_of_mem` + `bounds_of_byteGuarantees` block. A macro **cannot** capture it —
`inputX`/`env`/`real`/`readerGuarantees` are caller-local, so macro hygiene blocks the reference. It needs a
§4a `private theorem` over loose variables taking the subcircuit-membership proof as a hypothesis.
*Blocker:* the helper's conclusion must match **three different** `clk_target` spellings
(`input.clk_low + 4/3/2`) character-for-character at 14 `simpa only` call sites — the §9 kernel-safe-dedup
hard constraint. Wants its own solo pass.

---

## 6. Within campaign rules — just not reached

These need no waiver. They are queued side-tasks.

| # | what | scope |
|---|---|---|
| 6.1 | Dead `Fact (1 < p)` / `NeZero p` locals. 49 sites / 26 files; 4 certainly dead by spelling (`Math/Gate.lean:18`, `Shift{Left,Right}Chip/Populate.lean`, `Soundness/Decode.lean:338`); worst files `Model/Semantics/Decode.lean` (12), `DivRemChip/Soundness.lean` (5). **Verify each by `#check` + delete + re-elaborate + `#check`, never by grep** — deleting one can make `Fact p.Prime` newly *used*, silently adding a binder to the signature. | 26 files |
| 6.2 | Section-scope the `unusedSectionVars` suppression. **278** per-declaration copies across 81 files; W4/b1 did 100 in two files for net **−64**. Top five files hold 97 (Populate/Shapes 33, Populate/Euclid 23, Completeness/SubSpecs 20, DivRemOperation/AssertZeros 11, Completeness/CoreComplete 10). **Hard constraint:** wrap only runs where *every* declaration already carries the option — widening the suppression breaks the §6 binder-preservation check. | 81 files |
| 6.3 | Stale docstrings citing the retired `SP1Clean/Foundations/` layout. | ~20 files |
| 6.4 | `Model/Semantics/Decode.lean:39` — `regidxVal_val_lt`'s docstring cites `decodedInROM_rtype_op_bc_lt`, **which does not exist anywhere in the tree**. The real consumer is `Soundness.Target.decodedInROM_rtype_operand_lt` (`Soundness/Decode.lean:279`), which `TypedTime.lean:216` already cites correctly. One-word fix. | 1 line |
| 6.5 | `Model/Semantics/Decode.lean` — `have honezero : (1 : ZMod p) != 0` repeated in 12 proofs; a private file-level lemma cuts ~24 lines. | −24 |
| 6.6 | `Proofs/Chips/ProgramProviderChip.lean:44-53` — `two_pow_sixteen_lt` / `two_pow_five_lt` each carry a 3-line shape that collapses to the one-line idiom validated in `WordRangeCheck.lean` (`have := Fact.out (p := 2 ^ 17 < p); omega`; omega normalises both literals). Zero risk. | −4 |
| 6.7 | Reader `circuit` record field abbreviation — all eleven `Native/Readers/*.lean` spell `Assumptions := Assumptions, Spec := Spec, soundness := soundness, completeness := completeness` where Lean's structure-instance sugar would do (as `main`/`elaborated` already do in the same literal). ~3 lines per file. Wants a **single family sweep** — doing one file of an eleven-file convention is worse than the win. Also wants a ruling on whether structure-instance sugar counts as a §4b `def`-data change (the elaborated term is identical, so no importer can observe it). | −33 |
| 6.8 | `@[simp]` attribute candidates, suspended during parallel editing: `loadOpcode_{one,two,four,eight}` and `storeOpcode_*_toNat` are pure rewrite lemmas re-derived by hand ~40× across the `inv_*` ladders (plausibly a real perf win — it would stop those ladders re-reducing the `word_width = Int` comparison that `storeOpcode_one_toNat`'s own docstring flags as a kernel deep-reduction landmine); `instrToProgramRow'_rtype` is a `:= rfl` guard-transparency bridge. Needs an owner + a full build. | — |
| 6.9 | `linter.style.longLine` fallout. 345 lines >100 chars in the `Faithful/` ALU set alone; `LoadX0Chip/Bridge.lean` has 40 (max 119) against a family house style of ~110. Left alone throughout the campaign under the minimum-value filter, since the linter is not enabled on any pillar lib. Tracked as the remaining linter candidate in `docs/roadmap.md`. | tree-wide |

---

## 7. Deliberately NOT taken

These are **decisions**, not omissions. Each was reached independently by three or more batches and stopped at
each time. Re-litigating them costs a batch.

- **Folding `DivRemCore.CoreSpec` / `ownAsserts`.** It would cut the DivRem `Evidence` cost —
  `compareAssumptionsOfCore`'s cost is exactly the 121-way `obtain` over an unfolded
  `DivRemCore.OwnAssertsHold`, floor (60k, 100k]. But `CoreSpec` is a contract on the
  **audit surface**, and folding it changes what that surface says. Confirmed four times; left as-is.
  > The sibling screen makes the diagnosis cheap and is worth recording: `routedWord`, *in the same file*,
  > runs the identical 121-way destructure at a fraction of the cost — because it stops there, while
  > `compareAssumptionsOfCore` builds eleven `DivRemCompare.Assumptions` conjuncts on top of it. The
  > destructure alone is affordable; the destructure *plus* the downstream work is not.
- **Trading `bv_decide` for line count.** It adds `Lean.ofReduceBool` / `Lean.trustCompiler` to lemmas that
  are currently `[propext, Classical.choice, Quot.sound]`-clean and sit on the audit surface. Declined once
  explicitly on `rv64_subw_eq`. The line saving is never worth widening the trust base of a released theorem.
- **`Soundness/SupportedMachine.lean` stays byte-identical.** It is a 25-entry descriptor table plus
  `supportedChips_length : … = 25 := rfl` and `routeChip` — no proof body to golf, frozen `def` data fields,
  and **the list's order is a public witness-format commitment**. The column alignment is load-bearing for
  review. No reflow either.
- **Promoting a forced `private` duplicate to public, per-batch.** `private` keeps the axiom census stable
  (`gen_axiom_probe.py` skips `private` lines), which matters more than two duplicated lines. The right fix is
  a scheduled cross-module round (§5.1), not a drive-by.
- **`grind` (plugin rules 2.1/2.2)** — a whnf-into-expensive-values risk on circuit goals. Opt-in only.
- **`lia` (2.7/3.3)** — do not mass-rewrite `omega` on a 4.31 toolchain without a spot check.
- **Sub-break-even repetition**, measured and skipped: the 9-site `ChipContracts.lean` roll-call (net ≈ −38,
  but that block *is* the human-readable map from bundle field to proof — collapsing it costs real
  auditability); the 6-site `Addi`/`Addw` routing block (irregular lemma names, no single macro covers both
  shapes); the `Grounding/MemoryChips.lean` families (`*Chip_timestampBounds_env` net −8,
  `*View_opA0` −6, `store*Assumptions_env` −2, `*Spec_of_decoded` **+1**, `*AdvanceReady_of_decoded` −7);
  `CompareComplete`'s duplicated event-gate preamble (line-negative to extract).
- **`Faithful/CoreAIR.lean`, and 13 consecutive `Native/Operations/*/Defs.lean`, returned honest zeros** —
  correctly, not for lack of looking. Do not re-dispatch them.

---

## 8. The rename queue — **40 candidates, none applied**

Profile §11: renames are **queued, never applied**, and queueing is the *terminal* state — a pass, not a
deferral. Renaming here is high-blast-radius: `scripts/nolints.json` is keyed by fully-qualified name;
`scripts/gen_axiom_probe.py` resolves probe targets by regex over source text;
`scripts/check_report_citations.sh` hard-codes 16 file+declaration pairs; `docs/verification-report.md` cites
declarations by name; and `update_extracted.py` regenerates files that reference them.

Exactly **one** entry was ever applied — #14 below, as a user-approved exception.

| # | current | proposed | file | risk / why |
|---|---|---|---|---|
| 1 | `LookupAccessList.isConsistentBalanced_implies_isConsistentOnline` | `…isConsistentOnline_of_isConsistentBalanced` | `Model/InteractionBus.lean` | low — `conclusion_of_hypothesis` convention |
| 2 | `TryStepReduction.get_writeMinstret_ne` | `…get_insert_minstret_increment_of_ne` | `Proofs/Sail/TryStepReduction.lean` | low — statement is get-after-insert-on-a-disjoint-key |
| 3 | `Soundness.Target.decodesADDIW` | `…decodesAddiw` | `Model/Semantics/Decode.lean` | low — all-caps breaks the sibling decode-producer convention; 2 call sites + 2 docstrings |
| 4–5 | `DivRemChip.subChannels{G,R}_map_assert` | `…subcircuitChannelsWith{Guarantees,Requirements}_map_assert` | `Native/Operations/DivRemOperation/OwnAsserts.lean` | low — the ten sibling `circuit_norm` lemmas spell the projection in full |
| 6 | `ShiftRightChip.hword_toNat` | `…hword_toBitVec32_toNat` | `Proofs/Chips/ShiftRightChip/Math.lean` | low — the statement is about `HWord.toBitVec32`, not `HWord.toNat`; collides conceptually with `ShiftRightMath.HWord.toNat` (see §3.1) |
| 7 | `DivRemChip.toNat_lt_2_64` | `…toNat_lt_two_pow_64` | `Proofs/Chips/DivRemChip/Math.lean` | low — `2_64` is ambiguous between `2^64` and `264` |
| 8 | `reg_idx_to_Register` | `regidxToRegister` | `Model/Register.lean` | **high** — the 96 lemmas *about* this def are all `regidxToRegister_*`; root-namespace def used across Model/Proofs/Soundness |
| 9 | `reg_idx_must_64` | `registerType_reg_idx_eq_bitVec64` | `Model/Register.lean` | medium — `must_64` reads as an imperative |
| 10 | `AddrAddOperation.h16p` | `…sixteen_lt` | `Native/Operations/AddrAddOperation/Populate.lean` | low — `h`-prefix on a **public** lemma |
| 11 | `ExtDHashMap_insert_insert_self` | `Std.ExtDHashMap.insert_insert_self` | `Model/SailWrap.lean` | medium — also a duplicate; decide with §3.5 |
| 12 | `bool_bits_forwards_to_if` | `bool_bit_forwards_eq_if` | `Model/SailWrap.lean` | low — the function is singular `bit` |
| 13 | `U16toU8OperationSafe.hn8` | `…two_pow_eight_lt` | `Native/Operations/U16toU8OperationSafe.lean` | low — same class as #10 |
| **14** | `h16p` ×10 | one shared `SP1Clean.sixteen_lt` | `Math/Word.lean` | **APPLIED** — user-approved exception to §2.3/§2.4; all ten copies deleted, every call site (plus four in-proof `have h16p`) repointed |
| 15 | `SP1Clean.kindOf` | `interactionKindOf` | `Model/InteractionProjection.lean` | low — a bare `kindOf` in the top-level namespace for `String → InteractionKind`; all 11 refs are in one file |
| 16–17 | `Readers.{MemoryAccess,RegisterAccessTimestamp}.h16p` | `…sixteen_lt` | `Native/Readers/` | low — subsumed by #14 |
| 18 | `Readers.CPUState.hn13` | `…two_pow_13_lt` | `Native/Readers/CPUState.lean` | low — byte-identical twin at `AddressOperation.hn13` |
| 19 | `BranchChip.zero_ne_one'` | `zero_ne_one_zmod`, hoisted to `Math/Gate.lean` | `Proofs/Chips/BranchChip/Decision.lean` | low — rename and hoist are one decision (see §3.2) |
| 20 | `BranchChip.val_of_bool` | `…val_eq_zero_or_one` | `Proofs/Chips/BranchChip/Decision.lean` | low — `of_bool` reads as a coercion *from* `Bool`; 10 call sites |
| 21 | `Faithful.val_29''` | `…val_29_zmod_p` | `Faithful/AluX0.lean` | low — the `''` is a collision-avoidance artifact; real fix is the §1.7 hoist |
| 22 | `Faithful.alux0cols_constraints_faithful` | `…aluX0cols_…` | `Faithful/AluX0.lean` | low — lone all-lowercase spelling; **matches the `*faithful*` probe glob** |
| 23 | `StoreByteChip.AdvanceReady` | `advanceReady` | `Proofs/Chips/StoreByteChip/Bridge.lean` | low — the `ChipKind` field is lowercase and `LoadX0Chip` agrees; 9 files disagree with 1. Pick one and sweep |
| 24 | `StoreByteChip.extHashMap_get?_insert_self` | `…getElem?_…` | `Proofs/Chips/StoreByteChip/Bridge.lean` | low — the proof immediately rewrites to `getElem?`; `Store{Half,Word,Double}` cite it cross-file |
| 25–26 | `Faithful.{lt,bitwise}_chip_constraints_decompose` | `…{lt,bitwise}Chip_…` | `Faithful/{Lt,Bitwise}Chip.lean` | low — each file mixes snake and camel for one chip prefix. #26 is elaboration-expensive: re-ladder after any edit |
| 27 | `Faithful.jalChipConstraintsFaithful` | `…jalChip_constraints_faithful` | `Faithful/JalChip.lean` | **medium** — whole-family inconsistency, 15+ declarations across 3 files; matches the `*faithful*` probe glob, so `gen_axiom_probe.py` needs regenerating |
| 28 | `Faithful.forallNilIff` | `forall_nil_iff` | `Faithful/JalChip.lean` | low — three private clones of one lemma under two names; the real fix is §4.7 |
| 29 | `ShiftRightChip.resultA_isU64` | `sr_a_isU64` | `Proofs/Chips/ShiftRightChip/Defs.lean` | medium — the sibling names the identical role `sll_a_isU64` (its own docstring says it mirrors it); cited from four split `Soundness/<Op>.lean` files |
| 30 | `unsigned64_word_gate` | `unsigned64_flags_word` | `Proofs/Chips/DivRemChip/Evidence/Unsigned64.lean` | low — W5/b6 added a sibling `unsigned64_flags`; unifying also wants an argument reorder, frozen by §2.1/§2.2 |
| 31–32 | `Faithful.{nativeU16MSBAssertionList,u16MSBAssertions}` | prefix with `shiftLeft` | `Faithful/ShiftLeftChip.lean` | low — same-named privates in one namespace across both shift anchors; they do not collide only because both are module-mangled |
| 33 | `correct_sll_native` binders `op_b_val op_c_val` | `rs1_val rs2_val` | `Proofs/Chips/ShiftLeftChip/Bridge.lean` | low — four sibling bridges use `rs1_val`/`rs2_val`; binder names are signature text, frozen by §2.1 |
| 34 | `DivRemChip.{generalChild_nil,assertionChild_nil}` | `InteractionRecovery.interactionsWith_{general,assertion}Subcircuit_nil'` | `Proofs/Chips/DivRemChip/Formal.lean` | n/a — when §1.1 lands these should be **deleted**, not renamed. Recorded so the shared names are chosen with the DivRem call sites in view |
| 35–37 | `Soundness.{add,sub,subw}InputOpA0_eq_zero_of_mainConstraints` | `Soundness.<Chip>Chip.eval_inputOpA0_…` | `Proofs/Chips/{Add,Sub,Subw}Chip/Contracts.lean` | low — six sibling files use the prefixed form; these three use unprefixed camelCase in the bare namespace |
| 38 | `Soundness.{selectorVars,controlExpressions}` | `Soundness.MulChip.…` | `Proofs/Chips/MulChip/Contracts.lean` | low — Lt and Bitwise declare the same two privates chip-prefixed; no collision today only because all three are private and in different files |
| 39 | `Soundness.{jal,uType}EqualityConstraint_mem` | one `Soundness.equalityConstraint_mem` | `Soundness/Grounding/JTypeChips.lean` | low — byte-identical private twins in **one** file; retirement needs a deletion (see §1.6) |
| 40 | `Soundness.registerIndexCast` (private) + `itypeRegisterIndexCast` (private) | one public `registerIndexCast` in `GroundingAdapter` | `Soundness/GroundingAdapter.lean` | low — new-in-batch declarations, no probe glob, no external citation. Payload of §5.1 |

---

## 9. Tooling notes worth keeping

- **`lean_multi_attempt` appears to INSERT rather than REPLACE** when the target position is a continuation
  line of a multi-line tactic block. Observed independently by two workers: it spliced a snippet into the
  middle of a statement and left the old body behind. Reliable route for multi-line golfs: direct `Edit` +
  `lean_diagnostic_messages`. Single-line replacements away from continuation lines are fine.
- **The "unused local binding" scan is ~100% false-positive in the `Grounding/` layer.** A name-reference scan
  flagged 27 `have`s in `Grounding/MemoryChips.lean`; **every one is load-bearing** — 18 are consumed by the
  *next line's* `subst` (which finds the equation by the variable, not by name) and the other 9 feed a
  downstream bare `omega`. Do not budget a dead-binding pass for that layer on the strength of a grep.
- **`git grep <thing> main` answers "did this exist before the *branch*", not "did the marathon introduce
  this".** `dtumad/proof-cleanup` diverged from `main` long before the campaign and carries substantial
  unrelated work. Use `git grep <thing> <pre-batch-sha>` or `git log -S … main..HEAD`.
