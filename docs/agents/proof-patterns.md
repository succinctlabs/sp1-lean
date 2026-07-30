# Proof patterns & landmines

> **Read Clean's docs first.** This file records *SP1-specific instances*; the general doctrine lives in
> Clean's own docs (upstream <https://github.com/Verified-zkEVM/clean>, or in-tree under
> `.lake/packages/Clean/` — see `AGENTS.md` for the "where to find them" note). Before any nontrivial proof
> work read Clean's `doc/performance-problems.md` (§"The root failure mode" — make the dangerous value
> opaque, cross spellings by syntactic rewriting) and `doc/proving-guide.md`. **When you hit a new `whnf` /
> heartbeat / `(kernel) deep recursion` blowup, check `performance-problems.md` first** — most of the
> landmines below are worked instances of one of its 9 fix patterns (see §"Clean's unifying principle" for
> the mapping). Clean's `AGENTS.md` owns the subcircuit-boundary, helper-lemma, spec, and
> `ElaboratedCircuit` disciplines.

Concrete, build-verified patterns for the witnessed-`FormalCircuit` gadgets in `Native/Operations/`
(+ their proofs in `Proofs/Operations/`).
Reference templates: `AddOperation.lean` (carry chain), `IsZeroOperation.lean` (tiny witness
gadget), `BitwiseU16Operation.lean` (byte/opcode), `IsZeroWordOperation.lean` (composed subcircuits).

## Clean's unifying principle (and our instances)

Almost every performance landmine below is one concrete instance of the single doctrine in Clean's
`doc/performance-problems.md` (upstream <https://github.com/Verified-zkEVM/clean>, or in-tree under
`.lake/packages/Clean/`): **the elaborator and kernel decide defeq by `whnf`, which is cheap
on symbolic terms but catastrophic when a term can unfold into a large concrete computation (a `ZMod`
`.val`/`npow` over a big modulus, a recursive def at a literal depth, a `2^64` power). The fix is always to
make the dangerous value *opaque* before any defeq touches it, and cross between spellings by *syntactic
rewriting* (`rw`, `simp only`), never by unification.** Read that doc first; the map below tells you which
of its patterns each of our notes realizes, so a *new* blowup is anticipated rather than rediscovered.

| Our SP1-specific note (below) | Clean's general rule (Clean's `doc/`) |
|---|---|
| §"Keeping a nested sub-op's `cols` folded" (`eval_fromElements ↓100000`) | performance-problems §"Keep hypothesis types folded when applying generic lemmas" + item 1; proving-guide §"What (not) to unfold" |
| The metavariable landmine — never `exact <lemma> _ _ hyp` at a decoded row (7.4M `Vector.mapRange` unfolds); pass the **folded** `Spec` and match on the head symbol (`memoryTimeNat_lt_of_registerAccessCols`) | performance-problems item 1 + §"Keep hypothesis types folded" — *this is the same fix as the working-tree `GroundingAdapter`/`TimeExtraction` change* |
| §"The converse core" — make `(m*65535).val` opaque via `obtain`, **not** `set`/`let` | performance-problems item 4 verbatim ("`set` is not enough … only the `obtain`-an-existential form is genuinely opaque"); also explains why soundness survives where completeness explodes |
| §"Bit-shift chip soundness" — factor `2^64` into an abstract-`BitVec` helper (`srl_toNat`/`sra_toNat`), never `skipKernelTC` | performance-problems item 9 ("kernel has no accelerated `Nat.pow`; factor arithmetic into a `private theorem` over abstract ℕ") |
| Mul: keep `eval((output …) …)` an opaque atom (don't `simp [Expression.eval]`) | performance-problems items 1/4 (opaque values) |
| §"`ElaboratedCircuit` field obligations: let the default tactics close them" | complements Clean `AGENTS.md` "pass `elaborated` as an **explicit field** for factored circuits (else `soundness` elaborates with metavariables)" + README roadmap (this automation is known-incomplete upstream) |
| §"Compile-time / performance landmines" — "`maxHeartbeats` tightening is the wrong lever", "a bump in a simple proof is a code smell" | Clean's thrice-stated "**Never modify maxHeartbeats**" + performance-problems §"Measuring honestly" (`#count_heartbeats` lies; use `set_option maxHeartbeats <low>` / `diagnostics true` to find the true floor) |
| The 3 remaining gated completeness proofs (Branch/ShiftLeft/DivRem); ShiftRight is the validated repair | performance-problems §"Kernel size cliffs in completeness proofs": `circuit_proof_start_core` → per-component `dsimp only [main, circuit_norm] at h_env` → `.1`/`.2` → split into a (virtual, free) subcircuit when the parent cliffs |

Two disagreements worth stating honestly (see also `docs/architecture.md` §"Relationship to Clean's `Air`
layer"): (1) our large `maxHeartbeats` footprint splits into *term-intrinsic* cost (DivRem/Mul/carry chains
— genuine 64-bit arithmetic at a scale Clean doesn't face) that legitimately needs a raised ceiling, and
*maskable* blowups the opaqueness patterns above eliminate — treat every bump in a *simple* proof as class
(2). (2) Clean's "don't hand-unpack `ConstraintsHold` into helper lemmas" rule targets *single-circuit*
proofs; our `Soundness/` whole-machine layer legitimately reasons about the *ensemble*'s global balance,
which is a different regime — but per-chip closed-form families (`<chip>_memoryInteractionValues_eq`) are
closer to what Clean would fold into a bundled `Spec`/`exposedChannels` conjunct.

## maxHeartbeats: the fold recipe + no-bump discipline

**The invariant: don't raise a ceiling — fold the blowup.** `scripts/check_heartbeats.sh` (a CI `guards`
gate + part of `run_audit.sh`) fails if the `set_option maxHeartbeats` count grows past
`scripts/heartbeats_baseline.txt`. So a new blowup must be *folded*, not bumped. A genuinely term-intrinsic
addition (the KEEP-set below) requires a conscious baseline bump in the same PR. This kept the capstone build
fast; keep it that way. The current baseline is **SP1Clean 317 / SP1CleanTest 16**; two thirds of the
SP1Clean sites sit in auto-generated `Extracted/` (whose only lever is `update_extracted.py`), leaving
~102 hand-written ceilings. **The measured floor of every surviving hand-written ceiling is tabulated in
[`perf-findings.md`](perf-findings.md) — the canonical elaboration-budget record — including the five that
sit at under 2× headroom and are therefore the declarations most likely to break on the next toolchain or
mathlib pin.** Read that table before touching any surviving ceiling.

> **The guard is a raw grep, so never write the option string into a Lean comment or docstring under
> `SP1Clean/` or `SP1CleanTest/`.** `check_heartbeats.sh` counts sites with `grep -rc` over exactly those
> two directories and does not parse Lean, so a comment *mentioning* the option scores as a live ceiling
> and silently corrupts the ratchet. When recording a measured ladder in the source — which you should —
> phrase it without the literal: *"the former 8M ceiling was ~170× over; measured floor bracket
> (40000, 100000]"*. Keep such notes to **one line**; multi-line transcripts belong in `perf-findings.md`.
> (`Proofs/Sail/Advance.lean` carries one pre-existing phantom instance, so the baseline has always counted
> at least one non-ceiling.)

**1. `simp` → `simp only` — the biggest lever for chip/contract closers.** A full `simp [X.circuit, X.main,
…, circuit_norm]` drags in the *entire default simpset* — that, not the `circuit`/`main` unfold, is the real
cost that forced the per-chip ceilings. `simp only [<same args>, circuit_norm]` closes the identical goal
cheaply (fits the 200k default). This single change removed all `TypedTimeContracts` (26→1) and `TypedState`
(27→3) overrides. **Gotcha:** in the `firstStraightCPUTimeContract`-style closers, **keep `input, offset` in
the args** — dropping them makes chips whose CPUState subcircuit is *not* the operations-list head (AluX0,
and the `right/left/rfl`-navigated Jalr/Branch) time out. Where goal-1 membership isn't at the head, add the
manual `right/…/left/rfl` navigation (see `TypedTimeContracts` Jalr/Branch).

**2. The `circuit_output_eq` fold — for closed-forms referencing `<chip>.circuit.output`.** The memory
closed-form family (`<chip>_memoryInteractionValues_eq`, the ×25 capstone rollout) blows up because
`simp only [circuit_norm]` leaves `<chip>.circuit.output {concrete row}` un-reduced (its residual is the
*structural* output — witnessed vars via `Vector.mapRange`, **not** a computed `a+b`). `circuit.output`
reduces to `elaborated.output` only under `explicit_circuit_norm` (Clean's `FormalCircuitBase.output` is
`@[explicit_circuit_norm]`, not `@[circuit_norm]`), and no global lever bridges it (a global tag yields the
*worse* normal form `circuit.elaborated.output`, still stuck on the chip's `elaborated` projection). **Fix:
a per-chip `rfl` helper over an OPAQUE input**, colocated in `Proofs/Chips/<Chip>/Formal.lean` after
`def circuit`:
```lean
@[circuit_norm] theorem <chip>_circuit_output_eq (input : Var <Chip>.Inputs (ZMod p)) (offset : ℕ) :
    (<Chip>.circuit (p := p)).output input offset = <the chip's elaborated.output struct> := rfl
```
then close with `simp only [circuit_norm, …]` (auto-fires the tagged helper; no whole-`circuit` unfold at the
concrete row). This is Clean's `doc/performance-problems.md` item-1 ("extract witness values through a lemma
over an opaque variable") — the unfold is symbolic over the opaque `input`, kernel-checked *once*; applying
it at the concrete row is a pure rewrite. It dropped `addChip_memoryInteractionValues_eq` from 4M to **no
override**. The RHS struct is copy-pasteable from `Native/Chips/<Chip>/Defs.lean` for hand-written-output
chips; for auto-elaborated chips, extract the normalized RHS via `lean_goal` on `(<Chip>.circuit.output
input offset)`. If the `@[circuit_norm]` tag perturbs the chip's own soundness/completeness, drop the tag and
pass the plain lemma explicitly.

**3. Measure floors by lowering the real ceiling — `#count_heartbeats` LIES.** It runs with an *unlimited*
budget and under-reports (Clean's `doc/performance-problems.md` §"Measuring honestly"). A prior note here
claimed `Sll.soundness = 72 heartbeats`; re-measured with `set_option maxHeartbeats <low>` it genuinely needs
> 200k. Always lower the *actual* ceiling and rebuild to find a floor; never trust `#count_heartbeats`.

**4. Diagnosing a budget-bound declaration — four facts that separate a measurement from a guess.**

- **A ceiling has *declaration* granularity only.** The heartbeat counter is cumulative from the
  declaration's start, so wrapping one expensive tactic line in a scoped `… in` directive does **not**
  isolate that tactic — the wrapped line still fails at the *enclosing declaration's* rung. "Pin the one
  expensive tactic high and ladder the rest" is therefore not a usable strategy. To attribute cost *within*
  a declaration, `sorry` out the other branches instead — and restore before any other tool call, since a
  `sorry` left on disk trips the repo's own guards.
- **A cascading `(kernel) unknown constant '_private.…'` is never a result; it is a re-measure
  instruction.** When a producer `def` exhausts its budget, every dependent cascades with that error
  instead of its own timeout, so the dependents' true floors are invisible and they read as "binding" when
  they may be hundreds of times over. Two properties make it hard to spot: the cascade also lands on
  *unceilinged* consumers, where it reads as independent breakage; and **which producer is named changes
  between rungs** — the same masked line reported `divRemComparisonBlocks_roundtrip` at one rung and
  `divRemArithmeticBlocks_roundtrip` at the next, because the producers' pass/fail set had changed. Masking
  is itself rung-dependent (`MulOperation/RawSpec.full_product` masks at 1M and not at 200k/400k), so never
  conclude "no masking" from one probe. Pin the suspected producer high, re-run, and confirm the dependency
  by grepping for citations rather than inferring it from the error.
- **The timeout's phase name is a cost *class* read at the binding rung, not a stable fingerprint.**
  `whnf` (usually reported at column 1 of a signature) = an elaboration-bound `circuit_proof_start` tower,
  foldable · `isDefEq` = an abstraction/unification blowup (a `set` over a large term is the classic cause)
  · `«abstract nested proofs»` = post-elaboration, neither foldable nor term-intrinsic · `«LCNF compiler»` =
  genuinely code-generation-bound, where **none of the fold recipes apply**
  (`Native/Operations/MulOperation/Defs.lean`'s `main` is the only known case: it elaborates fine at 40000
  and only codegen times out;
  `noncomputable def` is *rejected*, not deferred, because `SP1CleanTest/TraceGenTests` derives traces from
  `main`'s witness closures and would break `lake test`). **The phase moves with the rung** — measured at
  n=56, the control-rung distribution (`elaborator` 21 · `isDefEq` 14 · `«synthesize pending MVars»` 14 ·
  `whnf` 7) bore almost no resemblance to the binding-rung distribution. Read it at the *lowest failing*
  rung, and never treat a rung-1 phase as the site's identity.
- **A floor measured through the LSP is not a floor against the gate.** The `lean-lsp` server does not
  apply the pillar libs' `moreLeanArgs` — the same reason `lake env lean` cannot certify a pass. So when
  *keeping* a ceiling, size it at roughly **4× the measured bracket top**, not at the bare lowest passing
  rung. Removal is unaffected: a site clearing 40000 against the plain 200000 default has ≥5× headroom
  either way. Also: a failure *position* is an attribution tool and says nothing reliable about magnitude,
  and an **in-body** position is not even stable across runs (three identical invocations at one rung named
  three different owners, while the *signature* positions stayed fixed).

**The KEEP-set — genuinely term-intrinsic; do NOT `simp→simp only`-sweep (tested, zero speedup).**
`compile-profile.md:131` records the exact `simp→simp only` experiment on the DivRem/Mul family with **zero
speedup** — the cost there is `nlinarith` / `linear_combination` / product-glue `simpa` / `omega` over big
arithmetic / kernel `2^64`-whnf / kernel `decide`/`bv_decide` / term-size, none a default-simpset drag. Keep
their ceilings: `Proofs/Operations/DivRemOperation/Core.lean`, `Native/…/DivRemOperation/OwnAsserts.lean`,
`MulOperation/RawSpec.lean`, `Proofs/Chips/MulChip/Formal.lean` (128M completeness), `MulOperation/Formal.lean`,
both Shift `Core.lean` `nlinarith` farms, the six Shift `Soundness/{Sll,Sllw,Sra,Sraw,Srl,Srlw}` conjuncts,
`Math/Word.lean` `toBitVec64`, `Proofs/Sail/Advance.lean`. `Faithful/` (73) is anchor-safe but *not*
mechanically safe (the full `simp` does real `List`/`Perm`/`decide` work + shapes residuals for downstream
`rw`) — per-theorem only, low payoff. `Extracted/` (105 × flat 8M) is proof-obligation-free `@[irreducible]
def` let-chains — the only lever is right-sizing the emit in `update_extracted.py`.

## The witnessed-`FormalCircuit` recipe

Each gadget (`Native/Operations/<Op>/` + `Proofs/Operations/<Op>/Formal.lean`) exposes, in order:

1. **`RawSpec`** — the literal meaning of SP1's extracted constraint list at `is_real = 1` (carry-bool +
   range form, or per-byte form, or a composition of sub-gadget `RawSpec`s). Anchored to the extracted
   constraints in `Faithful/<Op>.lean`.
2. **`Assumptions`** — operand preconditions (`Word.isU64`, limb `< 2^16`, opcode booleanity, …).
3. **`Spec`** — *semantic*, e.g. `Word.toBitVec64 value = …` or an `if … then 1 else 0` indicator.
4. **a core lemma** (`<sem>_of_<raw>` / `<raw>_of_<sem>`) re-deriving `RawSpec ↔ Spec` natively.
5. **`main`** — witness the result columns, range-check them, assert the constraints (or
   `subcircuit <Sub>.circuit` for composition).
6. **`elaborated : ElaboratedCircuit`** — `localLength` + the `*_eq`/`subcircuitsConsistent`/
   `channelsLawful` obligations.
7. **`soundness` / `completeness`** — `circuit_proof_start` first, then wire `h_holds`/`h_env` to the
   core lemma.
8. **`circuit : FormalCircuit`** — bundle.

After each: confirm `#print axioms` (or the `lean_verify` MCP tool) shows only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Discharging the `elaborated` obligations for a composed `main`

When `main` uses `subcircuit <Sub>.circuit …` (e.g. `IsZeroWordOperation` composing four
`IsZeroOperation`s), discharge the obligations with the sub-circuit's own `circuit`/`elaborated`
unfolded:

```lean
localLength_eq := by
  simp +arith [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
subcircuitsConsistent := by
  simp only [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
  try omega          -- closes the `offset + k = k + offset` residue
channelsLawful := by
  simp [circuit_norm, main, <Sub>.circuit, <Sub>.elaborated]
```

A flat compose of several sub-circuits discharges fine this way — there is no "elaboration wall" for
the Operations layer (that wall is a chip-layer phenomenon; see the memory note).

## Soundness / completeness wiring for a composed gadget

- **Soundness.** `h_holds` hands you, per sub-circuit, `<Sub>.Assumptions (eval x) → <Sub>.Spec (eval x) <subcols>`.
  Apply each with `trivial` when its `Assumptions = True`, `simp only [<Sub>.circuit, <Sub>.Spec, …] at`
  to expose the sub-Spec, then feed the core lemma. The goal carries trailing
  `channelsWithRequirements = [] ∨ <Sub>.Assumptions …` conjuncts — discharge each with `Or.inr trivial`.
- **Completeness.** `h_env` gives the sub-circuit completeness facts and the witnessed-vector values
  (`hw_i := hw ⟨i, by norm_num⟩`). The goal is the *constraint gates* themselves (boolean gate, gluing
  equalities) — not the Spec. Discharge subcircuit `Assumptions` (= `True`) with `trivial` and the gluing
  gates from the honest witnesses.

## Keeping a nested sub-op's `cols` folded through `circuit_proof_start` (completeness)

When a chip composes a **deeply-nested** sub-op via `assertion … ⟨…, fromElements w, …⟩` (e.g.
`DivRemChip`'s `IsEqualWordOperation`/`IsZeroWordOperation` overflow flags — `is_diff_zero → 4×
is_zero_limb → {inverse, result}`), `circuit_proof_start`'s goal `simp only [circuit_norm]` rewrites the
sub-op `cols = eval (fromElements w)` via `ProvableType.eval_eq_eval` (`@[circuit_norm ↓ high]`, prio
10000) — pushing `eval` through the struct into a **deeply-nested record** whose `toElements` is
intractable (a `circuit_norm` fixed point that can't be re-folded; `getElem_toElements_eval_varFromOffset`,
`exact`, `rw`, `convert`, `interval_cases <;> simp` all whnf-time-out — flat `MulOperation` cols are fine,
the nesting is the killer). The sub-circuit `Spec` obligation then can't be discharged.

**Fix — selective non-decomposition (NOT struct-flattening, NOT brute force).** Bump
`ProvableType.eval_fromElements` (`eval (fromElements xs) = fromElements (xs.map env)`; exists in Clean's
`Provable.lean`, **un-tagged**) to top `circuit_norm` priority in the proof file:

```lean
attribute [local circuit_norm ↓ 100000] ProvableType.eval_fromElements
```

It intercepts `eval (fromElements w)` and keeps it **flat** (`fromElements (w.map env)`) before
`eval_eq_eval` can decompose it; then `eval_eq_eval` can't fire (the head is no longer `eval`). Each
nested-cols pin closes with `intro i hi; simp only [ProvableType.toElements_fromElements,
Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]`.

- **Priority must be *strictly* > 10000.** At a `↓ high` tie `eval_eq_eval` wins the *outer* struct and
  `eval_fromElements` only rewrites the leaves → the cols is still the nested record (symptom: N
  "unsolved goals", one per pin, each ~70 kB).
- **It's selective for free.** Only cols passed as a literal `fromElements w` match; a sub-op composed
  with a `ProvableType.witness` result (`varFromOffset` form) or a struct literal (`{value := …}`,
  `{msb := …}`) does **not** — so `Mul`/`Add`/`Lt`/`U16MSB` are untouched. Keep the attribute `local`.
- **Diagnosis tool** (the full `circuit_proof_start` goal is a ~69 kB decomposed term that times out the
  30 s LSP): in a throwaway theorem, `circuit_proof_start_core; dsimp only [main]` then `lean_goal` — core
  is just `intro`s and `dsimp` is definitional, both LSP-cheap, and the goal shows the cols still folded as
  `cols := fromElements w`, revealing the form + which sub-ops use it.

This technique reduced the DivRem completeness core substantially, but the current 4.31 driver remains
an explicit deferred proof; do not cite the experiment as a closed theorem.

## The `FormalAssertion` + `populate` demotion (generalizing the Add worked example)

For ops whose witnessed columns are **pinned by the semantic `Spec`** (see `../architecture.md`
"Assertion vs `FormalCircuit`"), the op is a *witnessless* `FormalAssertion` and the **chip** owns the
witnessing. Template: `Native/Operations/{AddOperation,SubOperation,AddwOperation,SubwOperation}/`
(`Defs`/`Populate`/`RawSpec`; hand-maintained circuit form in `Defs.lean`, proofs in
`Proofs/Operations/<Op>/Formal.lean`) and `Native/Operations/{U16MSBOperation,U16CompareOperation}.lean`
(single file, proofs in `Proofs/Operations/<Op>/Formal.lean`).

- **`Inputs`** gains the result/witness columns + `is_real` (e.g. `⟨a, b, value, is_real⟩`); `Spec` is
  `is_real = 1 → <semantic eq>` (gated); `Assumptions` gains `(is_real = 0 ∨ is_real = 1)`.
- **`main` witnesses nothing** (`localLength 0`): each range check becomes a gated byte pull
  `byteChannel.pullIf input.is_real ⟨6, input.is_real * value[i], const 16, 0⟩`, each assert is
  `is_real`-gated (`input.is_real * (cᵢ * (cᵢ - 1)) === 0`).
- **`elaborated`**: `localLength 0`, `output _ _ := ()`, `channelsWith{Guarantees,Requirements} :=
  [byteChannel.toRaw]`, plus the three `@[circuit_norm]` rfl-lemmas (`channelsWith*_eq`, `localLength_eq`).
- **`populate`** (in `Elaborated`) computes the witness; **`spec_populate`** proves `Spec ⟨…, populate …⟩` —
  the chip uses it to discharge the `assertion …circuit`'s completeness obligation (`Assumptions ∧ Spec`).
- **Soundness**: byte ranges from the pull `Guarantees` (`byteRowSpec_range`), carry-bools from the gated
  asserts (`bool_of_mul_pred`), fed to `<sem>_of_<raw>`; plus a byte *padding requirement* per receive
  (`intro h; rw [gate_zero_of_ne hbin h, zero_mul, ← c16]; exact (byteRowSpec_range 0 h16p).mpr (by simp)`).
- **Chip side** (`Proofs/Chips/AddChip.lean`): `let value ← witnessVector n (fun env => <Op>.populate …)`;
  `assertion <Op>.circuit ⟨…, value, is_real⟩`. Soundness feeds the op's `Assumptions`
  (`(h_op ⟨ha,hb,h_bin⟩ hr).2`); the channel tail gains `Or.inr ⟨ha, hb, h_bin⟩`. Completeness reconstructs
  per-limb `#v[eval input_var[i]]_i = input_word` (`Vector.ext; interval_cases i`), then `rw [hval]; exact
  <Op>.spec_populate …`.

### The converse core — for an assertion that composes a sub-`assertion`

When a demoted op (Addw/Subw) composes another (U16MSB) as a sub-`assertion`, its **completeness** must
reconstruct the sub's `Spec` from its own semantic `Spec`. That needs the *converse* of the forward keystone:
`carries_of_addwSemantics : … → toBitVec64 (resultWord) = signExtend(…) → RawSpec ∧ (msb = if … then 1 else 0)`
(`Native/Operations/AddwOperation/RawSpec.lean`). **Landmine:** make `M := (m*65535).val` an *opaque* variable via
`obtain ⟨M, hMdef⟩ : ∃ M, (m*65535).val = M := ⟨_, rfl⟩` — a `set`/`let` lets the kernel reduce `(m*65535).val`
through `ZMod`'s `Nat.rec` multiply → "**(kernel) deep recursion detected**". (Symbolic `2^48`/`2^64` in
`omega` are *fine*; the recursion was *only* the unfolded `M`.) The msb falls out by
`m*65535 = m'*65535 → m = m'` (`mul_right_cancel₀ c65535_ne_zero`).

### U16MSB's `Assumptions` are gated

`U16MSBOperation.Assumptions := (input.is_real = 1 → input.a.val < 2^16) ∧ (input.is_real ∈ {0,1})`. The
composer only bounds `a` via its own `is_real`-gated byte pull, so on padding the bound is unavailable but
the `Spec` is vacuous. An *un*gated `a.val < 2^16` is undischargeable on padding. The sub-assertion's
`Assumptions` surface as a real conjunct in the parent's soundness *and* in its completeness (`Assumptions ∧
Spec`) — feed `⟨fun _ => bound, Or.inr rfl⟩` (+ `rfl` for the `is_real = 1 →` Spec gate).

### Aux-column ops composing a demoted sub-op (stay `FormalCircuit`, fix only the composition)

Lt/Mul keep witnessing their aux columns (FormalCircuit) but swap `subcircuit U16X.circuit a` for
`let w ← witnessVector 1 (fun env => #v[U16X.populate_… (env a)]); assertion U16X.circuit ⟨a, w[0], 1⟩`
(gate `1`, ungated — `mult = -1` pure receive, no padding requirement); use `w[0]` for the old `.msb`.
**Place the `witnessVector` at the same offset the old subcircuit's first column occupied** so
offset-dependent proofs survive (LtUnsigned/Mul soundness reference only columns *before* the U16X). The op
now emits byteChannel → declare `[byteChannel.toRaw]` + the rfl-lemmas + import `Model.Channels`. **Bind
`let bm : Expression _ := w[0]`** before using it — `(is_signed - 1) * w[0] === 0` otherwise defaults the `1`
to `ℕ` (`HSub (Expression _) ℕ` synth failure).

### Bit-shift chip soundness (the `ShiftRight` SRL dispatch)

`ShiftRight`/`ShiftLeft` have **no operation gadget** — SP1 inlines the limb decomposition of the register
read into the chip asserts, so the chip is a skeleton (asserts + byte pulls in `main`, semantic `Spec` in
`FormalModel/Contracts/Chips.lean`). The native arithmetic is ported verbatim from sp1-lean `ShiftRight/Common.lean` into
`Native/Operations/ShiftRightMath.lean` (the `srl/sra/srlw/sraw_close_su16_*_case` lemmas + `is_mod_64`,
`cancel_mul_65536`, the `srl_within_byte_shift*` division identities, a local `HWord`). Port landmines: the
early lemmas rely on a section `variable [Fact (Nat.Prime p)] [Fact (2^17<p)]` + a `local instance : NeZero
p`; file-level `set_option maxHeartbeats 100000000` + `linter.unusedVariables false`; sed range-extraction
drops `section`/`end` markers and `/--` openers (strip/restore them).

- **Completeness: preserve the visible flag gate, fold the arithmetic tail.** Clean's shallow channel-law
  discharge needs the combined shift-flag sum boolean constraint in the parent; hiding that constraint
  inside a child prevents the parent from proving its gated byte pulls lawful. Keep the four individual
  flag booleans and combined sum gate in the parent, then compose a zero-witness `FormalAssertion` whose
  `CoreSpec` is the remaining 53 assertions in exact upstream order. Prove the child with ordinary
  `circuit_proof_start [CoreSpec]`; prove the parent with `circuit_proof_start_core`. The child exposes no
  interactions, so a compositional `interactionsWith_subcircuit_eq_nil` lemma erases it from channel proofs
  without unfolding its constraints. This is a virtual boundary: no witness cell, assertion, interaction,
  or AIR order changes. The resulting `ShiftRightChip.completeness` and bundled `circuit` are axiom-clean.
- **Spec on the register read, not a ghost operand.** The asserts decompose
  `adapter.op_b_memory.prev_value` (rs1) and read the shift amount from `op_c_memory.prev_value[0]` (rs2),
  and `main` never touches a separate `op_b_val`. So the `Spec` must shift `rs1 := adapter.op_b_memory
  .prev_value` by `rs2 := adapter.op_c_memory.prev_value` (like `BranchChip`), and `Assumptions` bound
  `isU64` of *those reads* — otherwise the operand is disconnected from everything the circuit constrains
  and soundness is unprovable. (Contrast Add/Lt, which pass `op_b_val` *into* an operation gadget.)
- **Kernel `2^64` deep-recursion → abstract-`BitVec` bridge, NOT `skipKernelTC`.** `BitVec.toNat_ushiftRight`
  at `BitVec 64` plants `2^64` (via `BitVec.ushiftRight`'s `@[expose]` body); reduced **over a concrete
  `Word`-derived `BitVec 64`** it deep-recurses the kernel re-check even under `lake build`'s `--tstack`. The
  split-into-bare-`rw` (sp1-lean PROOF_PATTERNS §3 #8) was **not** enough. The kernel-clean fix (mirrors
  `ShiftLeftChip`'s `sll_rv64_eq`, no `skipKernelTC`): isolate the `RV64.srl`/`sra` `.toNat` unfold into a
  helper over **abstract `BitVec 64` args** (`ShiftRightChip/Math.lean` `srl_toNat`/`sra_toNat_{false,true}` :
  `(RV64.srl c b).toNat = b.toNat / 2^(c.toNat % 64)`), where the `2^64` body is kernel-checked once over
  variables. The `_div_to_bitvec` wrapper then only does `apply BitVec.eq_of_toNat_eq; rw [srl_toNat, hsh]`
  with `hsh : (toBitVec64 rs2).toNat % 64 = rs2[0].val % 64` proved the clean `ShiftLeft` way
  (`Word.toBitVec64_toNat` + `Word.toNat_def` + `show (2:ℕ)^N = <literal>` masks + `omega`) — so it never
  re-unfolds a shift over a `Word` value. For a non-shift `BitVec 64` msb/extract (`low32_msb_eq_b1`), mirror
  `toBitVec64_msb_eq_b3_ge`: a `rw` chain (not `simp only`) + mask **every** `2^N` (incl. `2^48`) to a literal.
  (Was `set_option debug.skipKernelTC true in` — removed 2026-06-18; now CI-gated by
  `scripts/check_no_skipkerneltc.sh` so it can't come back. The option is the last-resort escape, not
  the recipe.) Lemma name is `BitVec.extractLsb'_toNat` (not `toNat_extractLsb'`); `extractLsb 5 0 =
  extractLsb' 0 6`, `.toNat = x.toNat % 2^6`.
- **`simp only [id_eq]` before `linear_combination`/`ring` over field elements.** Clean wraps field
  elements as `id (ZMod p)`, which blocks `ring`'s instance synthesis (`IsRightCancelAdd (id (ZMod p))`).
  `clear_value` does **not** fix it; `simp only [id_eq] at h ⊢` does (the `BranchChip` L510 pattern).
  `linarith` never works on `ZMod p` (no order) — use `linear_combination`.
- **Pervasive form bridges.** The ported close lemmas use `((N:ℕ):ZMod p)` casts and `cb_i * (2:ℕ)`-cast
  exponents while the asserts/byte-pulls use ZMod literals (`N`, `cb_i * 2`); bridge each with `push_cast;
  ring` / a one-shot `have hXY : … = … := by push_cast; ring; rw [hXY]`. `norm_num at h` *distributes*
  negations (breaking later `rw` matches) — use a targeted `rw [show (2:ℕ)^10 = 1024 from by norm_num]`.
- **Stage A (shared prerequisites) shape** (`Proofs/Chips/ShiftRightChip.lean` `soundness` SRL bullet): `set`
  column aliases with the **exact** `env.get (i₀+4+1+1+…)` forms (Lean does not reduce the index
  arithmetic) + `clear_value`; `single_flag` (one flag = 1 ⇒ others 0, via a `ZMod.val_add_of_lt` chain);
  `b_msb = 0` ⇒ no sign fill; an `hbyte_fact` extractor folding `sum*v → v` (on the real row `sum = 1`) +
  `byteRowSpec_range_val` (symbolic-width `Range` extraction) for the limb ranges; eval bridges from
  `h_input`; the v-encodings + de-gated limb splits; `is_mod_64` to normalise the shift count.
- **The 4×16 leaf dispatch** (SRL conjunct, fully proven): `rcases b_cb5 <;> rcases b_cb4` (4 byte-shifts),
  then per byte-shift: zero the off-selectors, substitute `a[j] = limb_result[j]` from the output-placement
  asserts (`h_o*`), expand via the limb_result decomposition, then `rcases b_cb0..3 <;> first | exact
  srl_close_su16_{bs}_case S … | …` over the 16-entry S/M/N table.
  - **`ring1`, never `ring`, in the leaf `by`-blocks.** `ring` falls back to `ring_nf` on a wrong
    alternative (leaving `256 = 65536` unsolved), which `first` reports as an error it can't backtrack past;
    `ring1` fails cleanly so `first` moves on to the matching `S/M/N`.
  - **`mul_eq_zero` does NOT fire on `ZMod p`** (neither as `.mp` nor as a `simp only` lemma — the
    `Nat.rec` Mul-instance quirk). Extract the one-hot selectors via `simp at hh` (full `simp` *does* apply
    it) then a uniform `first | exact hh | exact hh.resolve_right (by norm_num [hne2, hne3])` (full `simp`
    sometimes closes clean, sometimes leaves a `suX = 0 ∨ <numeric> = 0` disjunction — the `norm_num`
    needs the `hneN : (N:ZMod p) ≠ 0` facts). Suppress `linter.unusedTactic`/`unreachableTactic` for the
    dead `resolve_right` branch.
  - The 16 alternatives differ only in `S/M/N`; **generate them** (and byte-shifts 1–3) with a script over
    the table rather than hand-typing. Watch the replace span doesn't swallow the following `· sorry`
    bullets.
- **SRA/SRLW/SRAW** add a `b_msb`/`srw_msb` sign-fill on top. SRA: derive `b_msb = if op_b[3].val ≥ 32768
  then 1 else 0` from the `U16MSBOperation` gadget `Spec` (apply `h_msb1 ⟨…, bool_of_mul_pred h_sra_b⟩`),
  case-split on `op_b[3].val ≥ 32768` (BitVec msb via `ShiftRightMath.toBitVec64_msb_eq_b3_ge`). The msb=0
  arm reuses the SRL dispatch (`sra_div_to_bitvec_false` → `srl_close`); the msb=1 arm uses
  `sra_div_to_bitvec_true` → `sra_close_su16_*_case` with `sraFill = 65536 − v0123`. Both conversion
  helpers route through the abstract-`BitVec` bridges `sra_toNat_{false,true}` (kernel-clean, no
  `skipKernelTC` — see the `2^64` bullet above). SRLW/SRAW are the 32-bit (2-limb `HWord`) analogs,
  `signExtend 64`-packaged via `toBitVec64_signExtend_word`.

## Landmines

- **Never `set_option (debug.)skipKernelTC` (CI-gated).** It bypasses the kernel type-check re-run, defeating
  the axiom-clean trust anchor. `scripts/check_no_skipkerneltc.sh` fails the audit and CI on any hit in
  `SP1Clean/**/*.lean`. When a goal blocks on a kernel deep-recursion / `2^64`-unfold error, factor the
  expensive compute into an abstract-`BitVec` helper proved once over variables and apply it symbolically —
  see the `2^64` bullet under "Bit-shift chip soundness" above for the worked `srl_toNat`/`sra_toNat` fix.

- **`autoImplicit` is ON here, and it fails *silently* when you hoist a statement.** A lemma whose
  **statement** mentions a name reachable only through a targeted `open` — e.g. `byteChannel`, which lives in
  `SP1Clean.Channels` — does **not** error. The name is auto-bound as a fresh implicit variable, the lemma
  elaborates as something weaker and different, and it surfaces much later as a confusing mismatch printing
  `Channels.byteChannel` against `byteChannel`. Any hoisted statement mentioning a channel needs
  `open SP1Clean.Channels (byteChannel) in` (the shape `Faithful/CPUState.lean` already uses mid-file).
  **Validate a new shared statement by *applying* it at an existing call site** — a scratch `example`
  discharging the verbatim hand-written `have` — before rolling it out. Also check for an import cycle before
  promising a hoist covers every site: `ChipTactics.lean` imports `Faithful/CPUState.lean`, so CPUState
  cannot cite anything hoisted into `ChipTactics`. A partial correct hoist beats a forced general one.

- **Not every `change` is a free abbrev-restatement — some bridge two distinct defeq constants, and deleting
  one gives `maximum recursion depth`, not a timeout.** A `change` that merely restates an `abbrev` is safe
  to drop when the closer is a term rather than a tactic needing the syntactic form
  (`MicroTime.chainState_succ_front` went 8 lines → 2 that way). But collapsing
  `change … at clockCount; exact clockCount` in `supported_core_witness_grounding` fails with **`maximum
  recursion depth has been reached`**, because `StateMsg.timeNat (initialBoundaryStateMessage …)` and
  `Semantics.clkNat …` are two *different* constants that merely happen to be defeq — the `change` is doing
  real bridging work. Likewise `TimedGrounding.stepOnce_of_sailStep`'s `change` is what makes the next line's
  `unfold` possible (`Semantics.stepOnce` ≠ `Machine.stepOnce`). **Before deleting a `change`, check that
  both sides name the same constant.** And note the failure mode: `maxRecDepth` (default 512) is *not* the
  heartbeat counter, so no budget change diagnoses or fixes it — when a long `main` or a deep term blows up,
  suspect `maxRecDepth` before heartbeats.

### Gadget-level (arithmetic, `Native/Operations/` + `Proofs/Operations/`)

- **`circuit_proof_start` must be the FIRST tactic** in soundness/completeness. Any
  `haveI`/`set_option`/`have hp` goes *after* it, or it errors "can only be used on Soundness/Completeness"
  (put `set_option … in` on the theorem instead). (`circuit_proof_start` lives in `Clean.Utils.Tactics`.)
- **Imports before the module doc-comment.** A `/-! … -/` header before the `import` lines makes the package
  `-D linter.flexible` flag get rejected on the (now zero-imports) header. Imports first, then the doc-comment.
- **`a + -b` vs `a - b` is not syntactically equal.** Lookup `.Spec` results and `=== 0` gates surface
  as `… + -…`, but `RawSpec`/`Spec` are written with `-`. Before matching, `rw [← sub_eq_add_neg] at <hyps>`
  (or add `sub_eq_add_neg` to the `simp only`). Forgetting this gives "type mismatch … + -… vs … - …".
- **`mul_eq_zero` won't fire on `ZMod p`** (a `Nat.rec` Mul-instance quirk). To get `x = 0 ∨ x = 1` from
  `x * (x - 1) = 0`, go through `inv_mul_cancel₀` / a `bool_of_mul_pred`-style lemma, not `mul_eq_zero`.
- **`Word` is an `abbrev` for `Vector`** — `w.toBitVec64` dot-notation fails. Write `Word.toBitVec64 w`.
- **Fin-indexed env reads:** use `h_env ⟨k, by norm_num⟩`, not `h_env k` — the latter inserts a non-reducing
  `↑(k : Fin n)` coercion.
- **`#v[…]` field selectors need the right simp set.** To turn `(#v[a,b,c,d])[k]`-style hyps into the
  bare entries use `simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
  List.getElem_cons_succ, Nat.add_zero]` — but only include the lemmas that actually fire (the
  `unusedSimpArgs` linter is an error under the project's `-D` flags).
- **Helper lemmas over a structured `cols` won't unify with loose `env.get` terms.** State shared cores
  (e.g. `result_collapse`) over **loose field variables** with the gluing hyps as explicit equalities,
  so the same lemma applies to both a structured `cols` and the soundness goal's `env.get (i₀+k)` terms.
  Pin the equality args by passing `eq_of_sub_eq_zero <gate>` (its concrete type fixes the metavars).
- **Extract a heavy case-dispatch shared by soundness + completeness into a sibling module.** When a chip's
  soundness and completeness both run the *same* expensive case analysis in opposite directions (e.g. a
  one-hot opcode dispatch: soundness derives `flag=1 → (br=1 ↔ cond)` from `br = decision`, completeness the
  converse), don't inline it twice under the giant `circuit_proof_start` goal — there each `omega`/
  `linear_combination`/`simp` drags the whole chip context and the proof needs a 16M-heartbeat ceiling. Lift
  it to two directional lemmas over **loose `ZMod p` field variables** in a `Proofs/Chips/<Op>Chip/Decision.lean`
  sibling (imported by `Formal`): they elaborate at the **default** heartbeat ceiling (small context), and
  soundness/`completeness` collapse to one `exact (…).mp`/`linear_combination (…).mpr` call apiece. State the
  lemma conclusions **verbatim** in the chip `Spec`'s shape (incl. `Word.toBitVec64`/`.slt`/`.ult` forms) so
  the call sites need no goal-bridging. `BranchChip` did this (16M→8M soundness, 16M→4M completeness, ~540-line
  `Formal` + a 3.5 s `Decision`); cf. the `Math/ShiftBounds.lean` `nlinarith` dedup. The `id (ZMod p)`
  field-carrier landmine bites at the seam: `simp only [id_eq] at <gate-hyp>` to strip it before feeding the
  loose-`ZMod p` lemma (see the `id_eq` note above).
- **`maxHeartbeats` floors.** `toBitVec64`/`asm8` rw chains are whnf-heavy: `set_option maxHeartbeats 2000000 in`
  for soundness/completeness; the carry lemmas (`addSemantics_of_carries` etc.) need up to `16000000`.
- **`omit [Fact (2^17 < p)] in` — and *any* `set_option … in` — goes *before* the doc-comment**, not between
  the doc-comment and the theorem. Put after a `/-- … -/` it is a parse error (`unexpected token
  'set_option'; expected 'lemma'`), and the second-order damage is worse than the error: a scripted pass over
  the file then **silently skips that site**, no timeout appears, and it reports a clean result for a
  declaration it never actually tested. Check placement before trusting a measurement.
- **`omit [Fact …] in` errors with "cannot omit referenced section variable"** when the instance is
  actually used (e.g. via a `ZMod` cast). Drop the `omit`; silence the unused-section-var linter with
  `set_option linter.unusedSectionVars false in` only when the var is genuinely unused.
- **`ZMod.val_natCast_of_lt (by omega)` — never inline it.** Inlined, the `by omega` elaborates against a
  metavar goal `?a < ?n` with no `p` in scope and fails. Instead write a separate `have hX : (… : ZMod p).val =
  … := ZMod.val_natCast_of_lt (by omega : x % 256 < p)` with a **concrete type ascription**, so `omega` sees the
  prime bound. Also feed `omega` the numeric forms (`have e8 : (2:ℕ)^8 = 256 := by norm_num`; rewrite
  `2^17 < p` to `131072 < p`) since it doesn't evaluate exponentials.
- **`high_byte`-style div/mod lemmas:** prove `(low%256) + 256*(u/256) = u.val` first, lift to `ZMod`
  via a `calc … ZMod.natCast_zmod_val`, then `linear_combination` it — do **not** `rw` the lifted
  equation, which also rewrites inside `u.val`.
- **Opcode case split** `o = 0 ∨ 1 ∨ 2` from `o.val`: build it via
  `calc o = ↑(o.val) := (ZMod.natCast_zmod_val _).symm; _ = ↑(0:ℕ) := by rw [h]; _ = 0 := by norm_num`. **Not**
  `ZMod.val_injective` (takes the modulus explicitly), and **not** `rw [key]` (loops on the val).
- **`add_comm` / BitVec instance quirk** — same family as the `mul_eq_zero` quirk. Match the gadget's operand
  order (`op_b + op_c`) in the chip Spec and let the Sail bridge `add_comm` to `execute_RTYPE`'s convention,
  rather than rewriting inside the gadget.
- **`ring` never fails, and that bites twice.** On a goal it cannot close outright it runs `ring1`, fails,
  emits `Try this: ring_nf`, and then succeeds via the `ring_nf` fallback.
  1. **The `info:` leak.** On goals like `x - x = 0` after `rw`, the proof passes but the build is no longer
     clean. Use `simp` (the `is_real` binary gate and `interval_cases` carry goals), `ring_nf`, or the
     explicit lemma (`sub_eq_add_neg`, `zero_mul`) instead.
  2. **`ring` cannot lead a `first` ladder.** `first | ring | linear_combination k | …` breaks *every*
     branch with `unsolved goals`: `ring` "succeeds" as a mere normalisation on the goal that actually needed
     `linear_combination`, shadowing every alternative behind it. **Use `ring1` as the leading
     alternative** — it fails cleanly so `first` moves on. A *trailing* `ring` is safe only because
     everything reaching it is already `ring1`-closable. (Measured on `LtOperationUnsigned.sel_populate`;
     same root cause as the `ring1`-in-leaf-blocks note under "Bit-shift chip soundness".)
- **`simp_all` leaks** into unrelated hypotheses — prefer targeted `simp [...] at h`.
- **Named-implicit-arg syntax `(u := …)` can be rejected by `lake` even when the LSP accepts it.** Make
  such lemma args **explicit** and pass positionally.
- **`linear_combination` / `interval_cases`** need explicit `import Mathlib.Tactic.LinearCombination` /
  `Mathlib.Tactic.IntervalCases`.
- **`limb_lift` (`Math/Word.lean`) takes 5 explicit value args first:**
  `limb_lift _ _ _ _ _ ha hb hv hc_in hc_out h_eq`.
- **W-instruction sign extension — reuse `Word.toBitVec64_signExtend_word`, don't re-derive.** For a 32→64
  sign-extended result word `#v[v0, v1, m·65535, m·65535]` (SLLW, ADDW, SUBW), the native
  `Word.toBitVec64_signExtend_word R X m …` closes `Word.toBitVec64 R = X.signExtend 64` given `m = if
  R[1].val ≥ 32768 then 1 else 0` and `X.toNat = R[0].val + R[1].val·2^16`. The `m`-form is exactly what
  `U16MSBOperation.Spec` hands you, so the SLLW subcase lemmas (`Native/Operations/ShiftLeftCore.sllw_subcase_cb4_*`)
  skip sp1-lean's `HWord.sign_extend_32_to_64_msb` / `sllw_a2_a3_eq_msb_byte` entirely. The new
  `Math/HWord.lean` then only needs `isU32`/`toBitVec32`/`toBitVec32_toNat`.
- **SLLW shift amount is 5 bits, not 6.** `RV64.sllw` masks `rs2` to bits 4-0 (`is_mod_64`'s `%64` result
  projects to `%32` via `c0_mod32_of_mod64`, splitting `cbsum6 = cbsum5 + cb5·32`); and with `is_sll = 0` the
  byte-shift `cb4 + cb5·2·is_sll` collapses to `cb4` ⇒ **2-way** dispatch (vs SLL's 4). Bridge `RV64.sllw` to
  the `HWord` form via a top-level `sllw_rv64_eq` (`extractLsb' 0 32`/`0 5` → `setWidth`, kernel-checked once,
  off the inline soundness path — same `2^N`-recursion reason `sll_rv64_eq`/`toBitVec64_toNat_mod64` exist).
- **`linear_combination` sign for `a = m·k` from a `m·k - a = 0` gate.** A `cols.X·c - a[j]` constraint
  surfaces as `X·c - a = 0`; to prove `a = X·c` you need **`linear_combination -hgate`** (coefficient −1),
  not `linear_combination hgate` (which leaves `2a − 2X·c ≠ 0` and "ring expressions not equal").

### Chip / reader composition (`Chips/`, `Native/Readers/`)

- **Struct-output `FormalCircuit` completeness — witness via `fromElements #v[…]`, not the struct literal.**
  A reader/gadget whose `Output` is a *nested* `ProvableStruct` (e.g. `Extracted.RTypeReader`: 22 cols across
  `RegisterAccessCols`/`Word`/`RegisterAccessTimestamp`) should witness with
  `ProvableType.witness (fun env => fromElements (M := <Struct>) (#v[…] : Vector _ (size <Struct>)))`, **not**
  with the explicit `⟨…, ⟨…⟩, …⟩` struct literal. The witness's flat op is `fun env => toElements (compute env)`;
  with the `fromElements` form that reduces by `ProvableType.toElements_fromElements` to the bare `#v[…]`, so the
  completeness extraction `have hk : env.get (…) = v := by simpa using h_env ⟨k, by decide⟩` is cheap. With the
  explicit struct literal, `toElements ⟨…⟩` is a tower of nested `Vector.append`s and the `simpa` **times out at
  `whnf` even at 16 M heartbeats**. (The circuit's *output* is `varFromOffset` either way — soundness/`output_eq`
  are unaffected; only the completeness witness values differ.) Match the goal's index forms (`i₀ + 1 + 4`,
  `i₀ + 1 + [4, [1, 1].sum].sum`, …) verbatim in the `have`s; `simpa` closes the residual `↑⟨k,_⟩` ↔ literal and
  offset-assoc gaps by defeq. **For a *deeply*-nested struct (`Extracted.RTypeReader`'s 22 cols) prefer
  the next entry — factor it into composed sub-circuits so no single circuit witnesses the whole tower at
  all; the `fromElements` form stays the tool for a circuit that must witness a *modest* multi-field
  struct directly (e.g. `Native/Readers/RegisterAccessTimestamp.lean`'s 2-col block).**
- **`simp [circuit_norm]`, not `simp only`, when the goal carries a witnessed-block projection tower.** If a goal
  reduces to `Expression.eval env (fromElements (Vector.cast … (mapRange n …).drop … .take …))`, `circuit_norm`
  has *no* rewrite for the `cast/drop/take/mapRange` tower, so `simp only [circuit_norm]` makes no progress and the
  closing `exact` falls back to raw `whnf` defeq (8 M+ heartbeats). Plain `simp [circuit_norm]` adds mathlib's
  default `Vector`/`getElem` lemmas, which rewrite the tower to `env.get (…)` cheaply. **Better fix:** compose the
  block as a subcircuit returning its extracted struct so the projection is a direct output field and the tower
  never appears (this is why the readers are `FormalCircuit`s, not chip-witnessed `fromElements` blocks).
- **A chip composing subcircuits keeps the *default* `output`** (do not set `output := varFromOffset <Chip> i0`).
  The chip's `main` returns a struct of subcircuit outputs at non-contiguous offsets, so `(main).output ≠
  varFromOffset`; the default `output := (main).output` is correct (and `output_eq` is `rfl`). Overriding it makes
  `output_eq`'s `rfl` time out.
- **Don't hand-write the chip's `ElaboratedCircuit` obligations — let the defaults fire.** Leaving
  `localLength_eq`/`subcircuitsConsistent`/`channelsLawful` *unspecified* uses the class defaults (`rfl` /
  `simp only [circuit_norm]; …` / `dsimp only [ChannelsLawful]; simp only [circuit_norm, seval]; …`,
  `Clean/Circuit/Basic.lean:218-249`), which close cheaply because they treat each `subcircuit` as a black box.
  Writing them explicitly as `simp +arith [circuit_norm, main, X.circuit, X.elaborated, …]` is what's slow: passing
  the subcircuits' `.circuit`/`.elaborated` forces `circuit_norm` to crack open their internals (the 22-col
  `RTypeReader` witness especially), which is what made `AddChip`'s instance need `maxHeartbeats 16000000` and ~4
  min. With the defaults it elaborates in **~1.7 s, no bump** (provide only `localLength _ := <concrete value>`).
- **In a composition soundness proof, `simp [circuit_norm] at <subcircuit-spec hyps>` BEFORE the final
  `refine`/`exact`.** A subcircuit's soundness hypothesis (e.g. `hclk13 : ((eval env (varFromOffset CPUState …))
  .clk_0_16 - 1) * 8⁻¹).val < 2^13`) is *defeq* to the goal conjunct but not syntactically equal; `exact ⟨…,
  hclk13, …⟩` makes the elaborator bridge that gap by raw `whnf` (slow → wants a heartbeat bump). A cheap
  `simp [circuit_norm] at hclk13 hclk8` normalizes both to `env.get …` first, so `refine ⟨…, hclk13, hclk8⟩`
  matches by `rfl`. Same root cause as the `simp only`/`whnf` finding above — pushing unnormalized terms into a
  defeq check. See `Proofs/Chips/AddChip.lean`.
- **Compose a chip `Spec` from its sub-circuits' `Spec`s (direct sub-calls), don't restate them inline.**
  Mirror sp1-lean's `SP1Chips` `allHold_constraints_iff` shape: the chip `Spec` is a conjunction of
  `<Reader>.Spec <reader-input-rebuilt-from-cols> cols.<block>` sub-calls (ungated — the readers' range checks
  are unconditional), the **proven** `is_real`-binary fact, and the `is_real`-gated arithmetic identity. In
  soundness each sub-call is discharged by the matching `h_<sub> trivial` from `h_holds` — it matches the
  conjunct *directly* (no per-bound `circuit_norm`), which is both cleaner and far cheaper than inlining the
  reader's bounds (an inlined "wide" spec is what historically timed out). Reconstruct the reader's cross-block
  inputs from the chip columns in the `Spec` (e.g. `clk_low := cols.state.clk_0_16 + cols.state.clk_16_24*65536`,
  `wv* := cols.add_operation.value[i]`). See `Proofs/Chips/AddChip.lean`.
- **Gate a reader's byte/range checks by `is_real` so padding rows are vacuous — range-check `is_real * value`.**
  SP1 sends each byte lookup with multiplicity `is_real`, so on padding (`is_real = 0`) the check isn't
  enforced and a real zero-padding row (all columns 0) is accepted. We don't model the byte bus (we use
  `Gadgets.ToBits.rangeCheck`, an unconditional assertion), so replicate the gating by range-checking
  `is_real * value`: on `is_real = 1` it's `value` (the real check), on `is_real = 0` it's `0` (trivially in
  range). The reader takes `is_real` as an input and its `Spec` becomes `is_real = 1 → <bounds>`. Soundness:
  under `is_real = 1`, `rw [h_real, one_mul]` turns the `is_real * value` bound into the `value` bound.
  Completeness: the padding-safe witness makes `value = 0`, so the gated check is `is_real * 0 = 0` (`mul_zero`)
  for *any* `is_real` — no `is_real`-binary assumption needed. **Scope it per SP1's constraint list:** in
  `RTypeReader` only the timestamp **byte** checks are `is_real`-gated; the `op_a_0 * wv` **zeroing gates are
  unconditional** (SP1 emits bare `assertZero`). And a pure arithmetic gadget like `AddOperation` needs *no*
  gating — a zero row already satisfies `0 = 0+0`; it's specifically the readers' byte checks that break on
  zeros. See `Native/Readers/{CPUState,RTypeReader}.lean`.
- **`is_real`-binary is *proven*, not assumed — split it across `Assumptions`/`ProverAssumptions`.** The chip
  emits the binary gate `is_real * (is_real - 1) === 0`, so soundness derives `is_real = 0 ∨ is_real = 1` from
  the gate hypothesis via `bool_of_mul_pred` (`Math/Word.lean`; it wants the `x * (x + -1) = 0` form,
  which is exactly the eval'd gate) and puts it in the `Spec`. Drop it from the (soundness) `Assumptions`. Only
  *completeness* still needs it as a precondition — keep it in `ProverAssumptions` (the prover commits to a
  boolean selector). This is the point of `GeneralFormalCircuit`'s decoupled Assumptions/ProverAssumptions.
- **A `maxHeartbeats` bump in a *simple* proof is a code smell, not a fix.** Genuine arithmetic (the
  `toBitVec64`/`asm8`/carry-chain rw towers in `Native/Operations/`) legitimately needs `2_000_000`–`16_000_000`. But a
  *structural/compositional* proof — a chip threading subcircuit Specs, an `ElaboratedCircuit` instance, a reader
  range-check — that only passes with a bump is almost always brute-forcing a `whnf`/defeq blowup that a cheap
  normalization removes. Before bumping such a proof, find the unnormalized term and fix it: prefer the default
  obligations; `simp [circuit_norm] at <hyp>` to align forms before `exact`; witness via `fromElements #v[…]` so
  `toElements` reduces (see above). `AddChip` went 16M-everywhere → **zero bumps** this way (243 s → 1.7 s).

## Reader composition (nested-struct readers as composed `FormalCircuit`s)

A reader whose `Extracted` output is a *deeply nested* `ProvableStruct` (`Extracted.RTypeReader` = four
scalars + three `RegisterAccessCols`, each a `Word` + a `RegisterAccessTimestamp`) cannot be a single
flat-witness circuit: even with the `fromElements` trick, `circuit_proof_start`'s `circuit_norm` has to
normalize the whole nested tower in one `whnf` and times out (minutes, then a hard timeout even at 4 M / 16 M
heartbeats). The fix that scales — and the shape the readers now use — is to **mirror the struct nesting with
composed sub-circuits**, exactly how `Clean/Gadgets/Keccak/KeccakRound.lean` proves a 1288-column state with
plain `circuit_proof_start`.

- **Factor each sub-struct into its own `FormalCircuit` that fills its own witness-gen obligations; compose
  them as `subcircuit`s.** One file per block (`Native/Readers/RegisterAccessTimestamp.lean` ⊂
  `Native/Readers/RegisterAccessCols.lean` ⊂ `Native/Readers/RTypeReader.lean`). The parent witnesses only its *own* scalar
  columns and `subcircuit <Block>.circuit ⟨…⟩` per nested block, then `return ⟨…⟩` assembling the output from
  the scalars and the sub-circuit outputs. Because each block is a sub-circuit *output* (an opaque
  `varFromOffset`), no nested struct literal is ever witnessed, so `circuit_norm` treats each block as a
  black box and every proof closes at the **default** heartbeat floor (the point — a bump here is the code
  smell above). The parent's `localLength` is just the sum (`4 + 3 * 6` for `RTypeReader`); a chip composing
  the reader sums the readers' `localLength`s in `main` order (`6 + (4+4*16) + (4+3*6)` for `AddChip`) — and
  this is the one obligation to **recompute whenever a composed reader's column count changes**, because the
  default `localLength_eq` `rfl` only fails *late* (once the reader compiles), as a stale `AddChip` did when
  the readers moved off `Gadgets.ToBits.rangeCheck` bit-witnesses onto zero-width `ByteTable` lookups.
- **A `FormalCircuit` whose `main` composes sub-circuits must *omit* `output` — same rule as a chip.** Setting
  `output _ i0 := varFromOffset <Struct> i0` forces the `output_eq` obligation to `whnf` the subcircuit
  composition → `(deterministic) timeout at whnf (200000 heartbeats)`, which then cascades to `Unknown
  identifier 'elaborated'` at `def circuit := { elaborated with … }`. Omit it: the default `output :=
  (main).output offset` is the assembled struct of sub-circuit outputs and `output_eq` is `rfl` with no
  unfolding (`Native/Readers/RegisterAccessCols.lean`, `Native/Readers/RTypeReader.lean`, `Proofs/Chips/AddChip.lean`). Set
  `output` explicitly **only** for a *leaf* circuit whose `main` has no sub-circuits — there `varFromOffset`
  is right and cheap (`Native/Readers/RegisterAccessTimestamp.lean`).
- **Emit a struct-input-projected byte check as an inline `Circuit.lookup ByteTable ⟨…⟩`, not a
  `byteRangeCheck`/`byteRangeCheckBits` `FormalAssertion` sub-circuit.** When the lookup argument flows from a
  *struct field* of the input (`input.clk_target` into the `U8Range`/`Range` argument), composing the
  `FormalAssertion` wrapper as a sub-circuit makes `circuit_proof_start` explode in `whnf` (superlinear in
  subcircuit-args-over-struct-projections). The raw inline `Circuit.lookup ByteTable ⟨op, x, …⟩` — the
  in-circuit half of SP1's `send_byte`, the same way `BitwiseU16Operation` uses `ByteXorTable` — is
  semantically identical (membership in the same `ByteTable`) and closes at the default floor. Soundness:
  `simp only [circuit_norm, ByteTable] at h_holds` turns each lookup into a `ByteRowSpec` fact; convert via
  `byteRowSpec_range`/`byteRowSpec_u8range`. The `FormalAssertion` wrappers stay fine when the arg is the
  *whole* bare input (`Native/Readers/CPUState.lean`'s clock checks). Related: a `FormalAssertion`'s predicate
  *preconditions* belong in its internal `Assumptions`, not threaded in as extra inputs.
- **Soundness/completeness shapes for a reader composing N sub-circuits.** After `circuit_proof_start`,
  `h_holds` is the N sub-circuit results (`Assumptions → Spec`, `Assumptions = True` so use `h_ trivial`)
  **then** this circuit's own asserts, in `main` emission order — `obtain ⟨h_a, h_b, h_c, z0, z1, z2, z3⟩`.
  The *soundness goal* is `Spec ∧ (N `Requirements` tails)`, one tail per composed sub-circuit
  (`channelsWithRequirements = [] ∨ Assumptions`, closed by `Or.inl rfl` since the sub-circuits declare no
  channels). The `Spec` is a *folded* unit and the anonymous-constructor flattening is **shallow** (it will
  not auto-split a nested `∧` sitting in a non-tail field), so match the goal tree exactly — e.g.
  `refine ⟨⟨⟨z0,z1,z2,z3⟩, ?_⟩, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩` nests the `Spec`'s own conjuncts; a
  flat tuple mis-associates and the elaborator reports `z0` "expected to have type `[the whole conjunction]`".
  *Completeness* is the opposite: `circuit_norm` yields a *flat* conjunction of the sub-circuits' `True`
  assumptions and this circuit's gate obligations (e.g. `env.get(op_a_0) * wv = 0`), so a flat
  `refine ⟨trivial, …, ?_, ?_⟩` fits; pull a witnessed-`0` column out as the k-th conjunct of `h_env`
  (`obtain ⟨_, _, h0, -⟩ := h_env`) and close each gate with `rw [h0, zero_mul]`. See `Native/Readers/RTypeReader.lean`.
  (For *channel*-emitting readers the tails carry real `Guarantees` content — see `../bus-model.md` §3 for
  that boilerplate; `Channel` is the faithful way to model the State/Byte/Program/Memory interactions.)

## `ElaboratedCircuit` field obligations: let the default tactics close them (don't hand-write proofs)

**Rule of thumb: an `ElaboratedCircuit` instance should almost never carry a hand-written field proof.**
Every field obligation — `localLength_eq`, `output_eq`, `subcircuitsConsistent`, `channelsLawful` — ships
with a Clean **default tactic** (`Clean/Circuit/Basic.lean`) that runs `simp only [circuit_norm, seval]`
(plus a `try`-closer). The right move is *always* to make that default succeed by feeding `circuit_norm`
the right `rfl`-lemmas — **not** to override the field with a bespoke `:= by …`. When you find yourself
writing an explicit field proof, treat it as a smell: the missing piece is usually a `circuit_norm`
lemma, and once it exists the field can be **omitted** so the default tactic resolves the goal. The
current main library has no deferred field proof. Preserve any remaining explicit proof only when it
documents a real structural exception and cannot be replaced by the default tactic.

The recipe that gets you there:

1. **Every circuit exposes its `channelsWithGuarantees` / `channelsWithRequirements` / `localLength` as
   `@[circuit_norm]` `rfl`-lemmas, right after its `elaborated` instance.** Name them
   `channelsWithGuarantees_eq` / `channelsWithRequirements_eq` / `localLength_eq` (namespace-local, so no
   clashes). Prefix each with `set_option linter.unusedSectionVars false in` (the `Fact` prime/bound
   instances are in scope but unused in a `rfl` lemma; `omit` errors on the ones whose projection still
   needs the field instance, so the `set_option` form is the robust choice). Example
   (`Native/Readers/CPUState.lean`):
   ```lean
   set_option linter.unusedSectionVars false in
   @[circuit_norm] lemma channelsWithGuarantees_eq :
       (ElaboratedCircuit.channelsWithGuarantees field Extracted.CPUState : List (RawChannel (ZMod p)))
         = [stateChannel.toRaw, byteChannel.toRaw] := rfl
   ```
   These are the cheap rewrites that replace the old inline `have … := rfl; rw […]` boilerplate, and they
   are what lets a *composing* circuit's default tactic see through the sub-circuit's declared lists/length
   (otherwise they "sit in an instance argument" that `simp` won't cheaply reduce — the `RTypeReader`
   instance in particular `whnf`-blows up).

   **Companion lemma — `circuit.localLength`, not just `elaborated.localLength`.** When an op/reader is
   *composed* as a sub-circuit, the updated Clean routes its offset through `<Sub>.circuit.localLength`
   (via the `@[circuit_norm]` `FormalCircuit/FormalAssertion/GeneralFormalCircuit.toSubcircuit_localLength`
   lemmas). That term is *syntactically distinct* from the `elaborated.localLength` that the `localLength_eq`
   above is stated about, so `localLength_eq` never fires on it — the offset stays an unreduced
   `circuit.localLength` and bloats every downstream `e*`/`hsem` in the composing chip's soundness proof.
   So **also expose `circuit.localLength` as an `@[circuit_norm]` rfl-lemma**, named `circuit_localLength`,
   placed right after `def circuit` (it can't sit beside `localLength_eq`, because `circuit` is defined
   later — in `Formal.lean` for split ops). Every op/reader that is ever composed as a sub-circuit carries
   one (example `Native/Operations/MulOperation.lean`):
   ```lean
   set_option linter.unusedSectionVars false in
   @[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
       circuit.localLength x = 557 := rfl   -- same numeral as `localLength_eq` (0 for most)
   ```
   With these in `circuit_norm`, subcircuit offsets reduce to numerals *inside `circuit_proof_start`* for
   every chip, keeping the manipulated terms small. (This globalized a per-chip workaround that used to
   re-declare the eight `<Op>.circuit.localLength` values locally inside `Proofs/Chips/DivRemChip/Formal.lean`.)
   Corollary: strengthening `circuit_norm` this way can make a previously-needed manual
   `simp only [<Sub>.circuit, circuit_norm]` in a sub-op's *own* proof report `` `simp` made no progress``
   or flag a now-unused simp arg — that's the lemma working; drop the redundant step (as in
   `Native/Operations/LtOperationSigned.lean`).
2. **The generic list/propositional closers are tagged `circuit_norm` once**, in
   `Model/Channels.lean` (conceptually they belong with Clean's `channels_lawful` default, but that
   is a pinned dep we don't edit): `List.cons_subset List.mem_cons List.cons_ne_nil List.not_mem_nil
   List.Subset.refl or_false and_self`. With these, the residual `⊆`/`∈` `channelsLawful` goal reduces to
   `True` and the default tactic finishes.

With (1)+(2) in place, **omit `channelsLawful` (and `localLength_eq` / `output_eq`) entirely** — the
default tactic closes them. This holds for `RegisterAccessTimestamp`, `RegisterAccessCols`, `RTypeReader`,
`CPUState`, `AddOperation`, and every chip (`AddChip`, `AddwChip`, `SubwChip`, …). If a default *doesn't*
close — usually because a sub-circuit's `_eq` lemma is missing or not `@[circuit_norm]` — **add the lemma**
rather than reaching for an override. A one-line `channelsLawful := by simp only [circuit_norm, seval,
<Sub>.channelsWith*_eq …]` naming the sub-circuit lemmas is the last resort (still no inline `have`s); it
remains only in `LtOperationSigned`.

> **Two caveats before you delete a field.** (a) **Omission is per-file, not family-wide, and it is a
> performance decision** — the default tactic whnf's the whole `main`, and on the chips whose `main` pulls
> in the sign-extension block that costs +63% to +132% or times out outright; see "Omitting an
> `ElaboratedCircuit` field …" under *Compile-time / performance landmines*. A/B-time it. (b) A
> `Prop`-valued field is a *proof*, so proof irrelevance makes **which** proof you wrote invisible to every
> importer — these fields are freely golfable in a way that `def` *data* bodies are not. But invisible to
> defeq is not the same as free to elaborate: dropping a `by exact` there removes an opaqueness barrier and
> can be a downstream catastrophe (same landmine section).

**Soundness-tail caveat.** Because the `channelsWith*_eq` lemmas are in `circuit_norm`, `circuit_proof_start`
also reduces the sub-circuit channel projections in a `GeneralFormalCircuit`/`FormalCircuit` *soundness*
goal: the per-sub-circuit "requirement tail" (`channelsWithRequirements = [] ∨ Assumptions`) collapses —
sometimes all the way to `True`, sometimes to the bare `Assumptions`, sometimes staying a disjunction.
Don't hard-code its shape; close it with a `first` that covers every collapse level:
```lean
refine ⟨⟨…the Spec tuple…⟩, ?_⟩
first
  | trivial
  | exact ⟨trivial, Or.inl rfl, Or.inl rfl⟩
  | (refine ⟨?_, ?_, ?_⟩ <;> first | trivial | exact Or.inl rfl | exact Or.inr h_as | exact Or.inr trivial)
```
See `Proofs/Chips/AddChip.lean` and `Native/Readers/RegisterAccessCols.lean` for the worked examples.

## Compile-time / performance landmines

The compile-time profile lives in `docs/snapshots/compile-profile.md` (regenerate with
`scripts/profile_compile.sh`); the per-declaration elaboration-budget record is
[`perf-findings.md`](perf-findings.md). These are the durable, still-true lessons behind them — apply them
when adding a chip or chasing a slow file. The broad attribute/macro wins have already been harvested
(below); remaining cost is term-intrinsic in the DivRem/Shift/Mul heavies, so new slowness almost
always means a *local* regression against one of these.

- **⚠ `by exact` on a `def`'s Prop-valued field can be load-bearing *opacity* — A/B-time the DOWNSTREAM
  consumers, not the edited file.** A tactic block is auto-abstracted into an **opaque auxiliary proof
  constant**; the equivalent term-mode form is *inlined*, so `isDefEqDelta` unfolds it straight into
  whatever cites the enclosing `def`. Dropping `by exact` from one field of `divRemChipRowCodec` — correct
  by proof irrelevance, −1 line, and clean in its own file — took `Faithful/DivRemChip/Exact.lean` from
  **260s to >1230s and still climbing**, pinned in `Lean_Meta_isDefEqDelta` / `whnfImp` /
  `unfoldDefinition`. Reverting that single hunk restored 260s. This is Clean's whnf-into-expensive-values
  doctrine arriving from an unexpected direction: on a field that any heavy module unfolds, the tactic block
  *is* the opaqueness barrier. Note also **why it hung instead of erroring** — the blown-up work landed
  inside the one declaration still carrying a very large budget, enough to absorb roughly an hour of extra
  `whnf`. **A high surviving ceiling silently converts a downstream regression from a loud error into a slow
  build**, which is the argument for the ratchet beyond tidiness.

- **The `v[i]` index-bound tax — already fixed by the `decide` fast path.** Every `v[i]` elaborates
  an `i < n` bound side-goal; in Lean 4.28's Std the slice-support `get_elem_tactic_extensible` rule
  does ~11 full-context traversals (`rw … at *`, `dsimp … at *`, a slice `simp`) per index — ~0.34s
  for `1 < 4` inside a hypothesis-heavy soundness proof, paid in every `have` type. `Math/GetElemFastPath.lean`
  registers one `macro_rules | get_elem_tactic_extensible => decide` line *above* Std's (so it's tried
  first among the extensible rules, still after `done`/`assumption`): literal bounds close by kernel
  `Nat.decLt` in ~26 heartbeats, non-literals fall through. This single line halved the swept set when
  it landed; **don't regress it** (e.g. by importing a module that re-shadows the rule below Std's). If
  a `have`-dense proof suddenly slows, suspect the fast path isn't in scope.

- **Measure `circuit_proof_start`; a large parent can make its one-shot normalization the bottleneck.**
  Medium chips still normalize cheaply, and many slow soundness files spend their time in arithmetic.
  ShiftRight completeness is the counterexample that matters: the exact 53-assert arithmetic tail proves
  with ordinary `circuit_proof_start` in about four seconds when folded behind its own `FormalAssertion`,
  while normalizing that tail together with the parent readers, witness closures, and interactions ran for
  minutes. Use `circuit_proof_start_core` in that parent and normalize projected components separately.
  Do not infer success or failure from elapsed time alone; require the build's explicit completion line.

- **`ElaboratedCircuit` `localLength_eq`'s `rfl` default whnf-unfolds `main` — seconds on a big main.**
  On a 17-op `main` the default `rfl` costs ~15s; `channelsLawful`'s default fails outright on
  channel-heavy mains. Hand-write the simp-route `localLength_eq` (and the `channelsWith*_eq` /
  `circuit_localLength` rfl-lemmas) on every chip with a non-trivial `main` so the defaults stay cheap
  — see the "ElaboratedCircuit field obligations" section above for the full recipe. Chips with small
  mains (2–5 ops) can keep the `rfl` default; it's cheap there.

- **Omitting an `ElaboratedCircuit` field is a *performance* decision, not only a style one — A/B-time it,
  per file.** Letting Clean's default tactic fire (see "ElaboratedCircuit field obligations" above) is
  usually right, but the default **whnf's the entire chip `main`**, while a hand-written
  `simp only [circuit_norm, main, <subcircuits>]` never does. Measured across 19 `Native/Chips` files:

  | what `main` composes | effect of omitting the field |
  |---|---|
  | `AddressOperation` **+ `U16MSBOperation`** | **+63% to +132%**, or an outright `timeout at whnf` |
  | `AddressOperation` only | −3% (safe) |
  | ALU chips whose `output_eq` body already read `simp only [main, circuit_norm]` | ~0% (safe) |

  The driver is **not** "is it a load chip" — it is whether `main` pulls in the sign-extension block
  (`LoadDouble`/`StoreDouble` are fine; `LoadHalf`/`LoadWord`/`LoadByte`/`Lt`/`Mul` are not), and the ALU
  chips are neutral only because their hand-written body unfolded `main` anyway. **The trap:** the defaults
  *succeed* on these files, so an untimed edit reports a clean −2 lines while silently adding 60–130%, and a
  full `lake build` will not catch it either (+3s on a 2.5s module vanishes inside a ~480s build). These
  files sit at a ~2.2s import floor, so real deltas are compressed — validate your instrument on a
  known-regressing file before trusting a null result. **Ordering:** run any omission pass *before* a
  ceiling pass, because a defaulted `output_eq` can manufacture a fresh ceiling.

- **`set_option linter.all false` on the generated `Extracted/` modules removes the linter tax.** The
  ~76 auto-gen modules carry it in their headers; keep it when regenerating (the linter passes over the
  monolithic generated terms were a measurable chunk of their cost).

- **`maxHeartbeats` tightening is the *wrong* lever — don't chase the ceilings.** The heavy Shift/DivRem
  proofs are kernel / type-checking-bound; their real cost is term-intrinsic (the `2^64` reductions, the
  product-glue `simpa`s) — chase *that* (the abstract-`BitVec` helpers + shared-tail dedup below), not the
  `set_option` numbers. **Caveat — measure with a low ceiling, not `#count_heartbeats`.** An earlier note here
  claimed `ShiftLeftChip/Soundness/Sll.soundness` "measures at 72 elaboration heartbeats"; that was a
  `#count_heartbeats` figure, which runs with an *unlimited* budget and under-reports (Clean's
  `doc/performance-problems.md` §"Measuring honestly"). Re-measured 2026-07-21 with `set_option maxHeartbeats
  <low>`, `Sll.soundness` **times out at the 200k default** (`whnf`/`isDefEq`) — its elaboration floor is
  genuinely > 200k, so its 4M ceiling is *binding* (do not drop it to default), even though a mid-range
  ratchet buys no wall-clock. To find a true floor, always lower the real ceiling and rebuild; never trust
  `#count_heartbeats`.

- **For many-case chips, extract semantic evidence instead of splitting full circuit soundness.** The old
  DivRem architecture proved nine `GeneralFormalCircuit.Soundness` theorems over the same enormous `main`
  and shared their requirements tail through a custom `SpecObligation` tactic. Lean 4.30/4.31 made even
  goal normalization dominate, and the whole stack was retired. The replacement has four layers:
  (1) a stable contract (`FormalModel/Contracts/DivRem.lean`), (2) circuit-independent evidence types and
  evidence→ISA proofs (`Proofs/Chips/DivRemChip/Cases.lean`), (3) reusable field/carry assembly lemmas, and
  (4) one generated-row→evidence theorem. Pair quotient/remainder cases so arithmetic is proved once;
  model exceptional branches as explicit constructors; keep final output routing separate. Use local
  helper lemmas inside layer (4) for offset plumbing, but do not export N operation-shaped circuit proofs.

## Golf & cleanup discipline

How to golf/clean a proof without breaking the repo's invariants (axiom-clean, 0-warning, no `info:`).
Distilled from the 2026-06 (109 files, −591 lines) and 2026-07 (the ceiling ratchet) cleanup campaigns,
axiom-cleanliness preserved throughout. The remaining deferred cleanup TODOs live under `docs/roadmap.md`
§ "Cleanup / polish backlog"; the available cleanup skills are catalogued at the end of this section, and
the binding house rules for `/cleanup` and `/cleanup-all` — which override the `mathlib-quality` plugin
where they conflict — are in [`cleanup-profile.md`](cleanup-profile.md).

**Instant, always-safe wins** (the bulk of the line savings):
- `:= by rfl` → `:= rfl`; `show T from by tac` → `show T by tac`; `rw […] at h; exact h` → `rwa […] at h`;
  `refine F ?_; exact e` → `exact F e`; `simp only […] at h ⊢; exact h` → `simpa only […] using h`.
- Merge adjacent identical `simp only`/`rw`; inline a single-use `have x := e` that has **no** `by` body.
- Reach for mathlib instead of a hand proof: `zero_ne_one`, `Int.eq_zero_of_abs_lt_dvd`, etc.

**Before golfing a `have`, search for it — by far the most common finding is that the lemma already exists
and simply is not cited.** This repo has good shared substrate — `Math/ShiftBounds.lean` (`lo_hi_lt`,
`hi_lo_lt`, `factor_le`), `Math/Word.lean`'s `val_N_zmod_p` / `val_N_ne_zero` families, `Math/Gate.lean`'s
`bool_val_le`, `Math/EvalVec.lean`'s `vec4_eval` — and proofs all over the tree re-derive those exact facts
by hand. Measured instances: a 20-line `key` in `ShiftLeftChip/Populate.lean` that was literally
`ShiftBounds.hi_lo_lt`; `two_ne_zero_one` (13 lines) and `h64ne` (6 lines) hand-rolling `val_2_zmod_p` /
`val_64_zmod_p`; four hand-rolled copies of mathlib's own `Nat.cast_ofNat` sitting next to a sibling file
that used the real one. `lean_local_search` on the statement shape plus a grep of the `Math/` families is
cheaper than any tactic golf, and it is where the lines actually are.

> **Cashing a lever does not have to mean rewriting with it.** Measured on `AddOperation.soundness`:
> `rw [Nat.cast_ofNat]` (forward, against a goal) is safe, but `rw [← Nat.cast_ofNat]` rewrites the `6`
> opcode column, and pinning it as `rw [← Nat.cast_ofNat (n := 16)]` does **not** rescue it — it targets the
> right column but yields `↑(OfNat.ofNat 16)`, a *different spelling* from `↑16`, which is a live
> char-for-char hazard against the downstream `byteRowSpec_range` match. The safe way to retire a
> hand-rolled copy in the `←` direction is to **keep the local `have` and prove it by the real lemma** —
> `have c16 … := Nat.cast_ofNat` instead of `:= by norm_cast`. The duplication is gone, every downstream
> `rw [← c16]` keeps its exact spelling, and nothing moves.

**The dominant structural win — eval-map factoring.** Chip/op `Formal.lean` proofs repeat a per-limb
`have eX : Expression.eval env input_var_X[i] = input_X[i] := by rw [← hX]; simp [Vector.getElem_map]`, one per
limb. Collapse the copies into ONE quantified helper
`have eX : ∀ i (hi : i < n), … := by intro i hi; rw [← hX]; simp [Vector.getElem_map]`, then call `eX i (by omega)`
at each site (~12–25%/file on Load/Store/op `Formal.lean`). A *global* lemma for the per-limb `eX` helper was
investigated and is **not** worth it: it saves only ~1 line/helper while re-churning ~36 already-clean
`Formal.lean` files plus a foundational rebuild, at form-variation risk. (The narrower length-4 `#v` → `Vector.map`
fold *was* worth hoisting — it's the shared `SP1Clean.vec4_eval` in `Math/EvalVec.lean`, used across the
Mul/Lt/Bitwise/Shift `Formal` proofs + the DivRem completeness `Driver`.)

> **Then take the second step: partially apply the helper.** Collapsing each repeated bridge to a one-liner
> is only half the win. On `Proofs/Operations/DivRemOperation/Core.lean` the same two-line
> `rw [← h, Vector.getElem_map]` bridge appeared **176 times**; folding to one-liners took 352 → 176 lines,
> and *partial application* — replacing each per-index family with one **quantified `simp only` rule** —
> took 176 → **25**. Total −466 (−40% of the file), elaboration 19.0s → 15.8s. Whenever you have collapsed
> N copies to N one-liners, ask whether one quantified rule replaces the whole family.
>
> **Landmine: the quantified `simp only` rule only fires when the helper's bound *is* the vector's own
> length.** `StoreWordChip`'s `eoap : ∀ i (hi : i < 2), … prev_value[i] = …` is stated at bound 2 over a
> **length-4** `Word`, so the `getElem` side condition becomes a derived `omega` term rather than `hi`
> itself and simp cannot key the pattern. It **fails silently** — no tactic error — and surfaces four lines
> later as `Application type mismatch` on the consuming `exact`. When the bound and the length disagree,
> leave that helper at explicit indices.

**Kernel-safe dedup on the bit-shift / DivRem cores** (the `2^64` landmine zone — read the "Bit-shift chip
soundness" § first). A heavy file may repeat a byte-identical `have` block across N sibling lemmas. You can
factor it into a single helper **iff the block is pure `ZMod.val` / `Nat` arithmetic with no `2^64`/`BitVec`
reduction** — extract it as a lemma **over loose variables** and apply it symbolically. This is kernel-safe
because a lemma application instantiates an *already-checked* body, so the kernel does no *extra* reduction
(no `skipKernelTC`; elaboration time does not regress). **Hard constraint:** the helper's conclusion must match
the original `have`'s type **character-for-character** — it's a downstream `rw`-target, and `(16 : ZMod p) - …`
is **not** interchangeable with `(16 - … : ZMod p)`. The heavy `2^64`-scale work itself is already isolated in
abstract-`BitVec` helpers (`srl_toNat`/`sra_toNat`) — leave those alone. Worked example: `inner_val`/`inner_hi_val`
in `Proofs/Chips/ShiftLeftChip/Core.lean`.

> **Scope refinement on that hard constraint (measured).** What matters is the **ascription position**,
> because that decides which numeral gets elaborated at which type. It is **not** about redundant outer
> parens: `((16 : ZMod p) - X).val` and `(16 - X : ZMod p).val` elaborate to the same term, and every
> downstream `rw` fires across that spelling. Treat differing *ascription placement* as blocking; treat
> cosmetic parenthesisation as fine — the stricter reading costs real golf for no safety.
>
> **A hoisted `have key := fun … =>` binding has no expected type**, so named arguments like `(cb4 := cb4)`
> become mandatory where the original `exact` did not need them. Give `key` an explicit `∀` type and the trap
> disappears; that is the better habit. Relatedly, **the `private` visibility that keeps the axiom census
> stable cannot cross a module boundary**, so preferring `private` can *force* a duplicate: the same 3-line
> `registerIndexCast` lemma exists in both `Soundness/GroundingAdapter.lean` and
> `Soundness/Grounding/ITypeChips.lean` because the importer cannot see a `private` declaration in its
> dependency. That is an
> accepted cost — `scripts/gen_axiom_probe.py` skips `private` lines, and a stable census matters more than
> two duplicated lines — but record such pairs as an owner decision rather than promoting one to public.

**Traps — `have`s that look dead but are load-bearing** (verify with `lean_goal` / a build before removing):
- `have hp : 2 ^ 17 < p := Fact.out` (and `have : 131072 < p`) — feeds a downstream `omega` that needs the
  magnitude; grep shows one occurrence (its own line) yet `omega` consumes it implicitly.
- `haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩` — supplies an instance to later
  `ZMod.val`/`omega` steps. There is **no** global `NeZero p` instance, *on purpose*: a `Fact (2^17 < p)`-derived
  one would make the pervasive `omit [Fact (2^17 < p)] in` clauses illegal (`Model/ByteTable.lean:84`). A
  `Fact p.Prime`-derived global instance *might* survive the `omit` pattern (it depends on primality, not the
  magnitude) and eliminate most of the ~185 `haveI` copies — but it cuts against the documented local-instance
  discipline and risks instance-resolution surprises, so it's an owner decision, not a drive-by change.

> **Apparent dead `have`/`obtain` bindings are load-bearing far more often than not — verify by
> elaboration, never by grep.** Two systematic sweeps produced **27** and **9** candidates whose names had
> exactly one occurrence in the file, and *every one of them was live*: most fed the **next line's**
> `subst`, or were consumed implicitly by a downstream bare `omega`. One (`providerBound`) silently fed
> `get_elem_tactic` for an index that appears in a **statement**, so deleting it would have changed a
> signature. A single-occurrence grep is evidence of nothing here.
>
> **And do not judge `Fact`/`NeZero` locals by inspection or by their derivation source** — that heuristic
> has now been wrong in *both* directions (all four `2 ^ 17`-derived `NeZero p` copies in
> `Native/Operations/BitwiseU16Operation.lean` turned out dead, while the same shape is load-bearing
> elsewhere). What decides it is whether `Fact p.Prime` is already in that declaration's **elaborated
> signature**: the hazard is not that the proof breaks (a broken proof is loud and safe) but that deleting
> the local can make `Fact p.Prime` newly *used*, which **adds a binder to the signature** — a quiet
> statement change. Two consequences:
> - **The standing cheap check is `linter.unusedSectionVars`.** Zero warnings ⟺ every section instance is
>   still used ⟺ no binder was dropped. So if a golf stops using an instance, the fix is **not** `omit`
>   (which removes the binder and *changes the signature*) but `set_option linter.unusedSectionVars false in`,
>   which keeps the auto-included binder and leaves the signature byte-identical
>   (`LtOperationSigned.zero_ne_one'` is the worked case). A *brand-new* declaration takes the ordinary
>   `omit [Fact (2 ^ 17 < p)] in` instead, because it has no prior signature to preserve.
> - **The recipe is `#check`, delete, re-elaborate, `#check` again**, comparing the printed signatures
>   byte-for-byte. Re-elaboration alone is necessary but *not* sufficient — a signature can gain a binder
>   while every proof still compiles.
>
> In-proof `have`s that re-derive `Fact (2 ^ 17 < p)` under a stronger hypothesis are dead by construction,
> since `Math/Word.lean` declares `instFact_2_17_of_2_24` and `instFact_2_24_of_2_25`.

- **`have ⟨…⟩ := h` destructures *without consuming*; `rcases`/`obtain` clears `h`.** Where a proof needs a
  hypothesis both whole *and* destructured, the usual `refine ⟨valid, ?_⟩` + `rcases valid` dance is
  unnecessary — `have ⟨_, …, shardLayout, halts, _⟩ := valid` keeps `valid` in scope. Worth checking wherever
  a hypothesis is reintroduced right after being cased on.

- **Two declarations can be the same declaration definitionally without looking it.**
  `Soundness/TimeExtraction.lean` had three payoff theorems with byte-identical bodies because
  `Readers.RegisterAccessTimestamp.Spec` applied to `real` *is* `ActiveTimestampBounds …`, and
  `RegisterAccessCols.Spec` is *defined as* the timestamp `Spec`; two collapsed to three-line term
  applications of the first. When sibling theorems share a proof body verbatim, check whether their
  hypotheses are defeq before assuming they are genuinely different results.

**Tactic dedup with `local macro` — the most effective lever in `Soundness/`, and six traps that all fail
far from their cause.** A repeated *tactic shape* (as opposed to real mathematics, which wants a lemma) is
best deduplicated with a `local macro`. It is an established construct in the grounding layer — ~50 of them,
`lake lint` passes over them — and macros are **not declarations**: they never enter a signature multiset and
never reach the axiom probe. Two break-evens, both measured, and they are different numbers: **lines ≈5 call
sites**; **time is much lower**, because a controlled A/B isolated the cost to *declaration* rather than
expansion (body alone 5.178s · body + 4 macros **unused** 5.403s · body + 40 expansions 5.454s), i.e.
**~0.07s per macro declared and expansions are free**. Don't declare a macro you use twice; don't hesitate
over expansion count. The traps:

1. **Definition-site identifier resolution.** A macro body resolves identifiers where the macro is
   *defined*, so placing it before a constant it cites fails at **every call site** with ``Unknown
   identifier `foo✝` `` — which reads like a typo or a stale name. Place the macro *after* what it
   references.
2. **A quotation-local `rfl` binds a name instead of substituting.** In an `rcases` pattern it introduces a
   *variable* called `rfl`, and the failure surfaces ~20 lines later as `Application type mismatch` on
   `rfl`, nowhere near the macro. Fix: ``mkIdent `rfl``.
3. **An antiquotation's category must match the splice site.** `unfolds:term,*` cannot splice into
   `simp only [$unfolds,*]`: it fails at the *macro definition* with `Lean.Syntax.TSepArray `term ","`
   vs `TSepArray [simpStar, simpErase, simpLemma]`, and then every call site — up to 1500 lines away —
   reports the useless `Tactic '…' has not been implemented`. Declare it
   `unfolds:Lean.Parser.Tactic.simpLemma,*` (bare `simpLemma` is not in scope outside `Lean.Parser.Tactic`).
4. **`local macro` is scoped to the enclosing `section`, not the file.** Declaring one inside a `section`
   makes every call site in *later* sections report a bare `error: unknown tactic`, which reads like a parser
   bug. Hoist the macro block above the first `section`.
5. **A macro whose *definition* fails still registers its syntax**, so every call site reports ``Tactic
   `…` has not been implemented`` and the real error at the definition is completely hidden. When you see
   "has not been implemented", scroll up to the definition — the diagnosis is never at the call site.
6. **`String.take` returns `String.Slice` in 4.31**, so `.toUpper` on it fails with `Invalid field
   'toUpper': The environment does not contain 'String.Slice.toUpper'`. Use `String.capitalize` when deriving
   names inside a macro.

What a macro *cannot* reach: caller binders (`env`, `input`, `real`, `decoded`, `hchip`, `guarantees`) are
unreachable from a quotation without `Lean.mkIdent`, and repetition that is a **term inside a `have` type**
rather than a tactic shape needs an ordinary (`private`) helper lemma instead. And prefer macros that
generate **tactics** over macros that generate **declarations**: the latter removes parsed signatures from
the source text, which is exactly what `scripts/gen_axiom_probe.py` (regex over source) and
`scripts/check_report_citations.sh` (16 hard-coded file+declaration pairs) rely on being there.

**Don't golf:**
- **`Faithful/*` anchors** — conservative only (drop `by exact` / dead `let` / `from by`); never restructure
  proof terms or statement forms; they are *syntactic* faithfulness anchors.
- **`Spec`/`Assumptions`/statement forms**, `set_option`/`maxHeartbeats`, `ElaboratedCircuit` field structure.
- **Auto-gen** — `Extracted/`, `*Vectors.lean`, `Native/Operations/*/RawSpec`, etc.; banner-check the header.
- **Narrative comments on kernel-sensitive Shift/DivRem files** — they document the `2^64` / `id (ZMod p)`
  landmines + proof roadmaps; they are the institutional memory of *why* the proof is shaped that way. (A
  blanket comment-strip on `ShiftLeftChip/Soundness/Sll` was reverted for exactly this.)

**Verify every batch:** `lake build SP1Clean` clean (0 warn, no `info:`), then
`scripts/run_audit.sh` (zero proof deferrals and no unexpected axiom-census change) — and separately
`scripts/check_report_citations.sh`, which `run_audit.sh` does **not** invoke (see "Build & verification
gotchas"). On heavy files watch the per-file elaboration time in the build log and **revert on regression**.

> **Never *infer* an axiom change from the tactics you removed — measure both versions.** A report that
> replacing some `omega` calls in `FormalModel/Contracts/Chips.lean` had dropped `Classical.choice` was
> false in both halves once measured in place: `rv64_addw_eq` never carried it, and `rv64_mulw_eq` went
> `[propext]` → `[propext, Quot.sound]`, a strict *addition* — the opposite direction from the claim. Nothing
> left the permitted set, so the change was admissible, but the claim was not. **Run `#print axioms` on the
> pre-edit version too, or say nothing about axioms.**

**Merge gotcha (post-`git merge`):** an auto-merge can *silently duplicate* a lemma that both branches added
near each other — no conflict marker, but `lake build` fails with "`<name>` has already been declared". Always
run the full `lake build` after a merge even when `git status` shows no conflicts (`Proofs/Chips/BitwiseChip/
Bridge.lean` hit this when upstream #101's immediate-type bridges met a golfed copy).

**Available cleanup skills:**
- **`/cleanup`** — the per-file 7-phase workflow (style audit → per-decl golf → simplify → verify). Best for a
  handful of named files.
- **`/cleanup-all`** — the orchestrator marathon (dispatches per-batch workers across the whole tree). Best for a
  project-wide sweep; honor the repo guardrails (auto-gen exclusion, axiom-clean, heavy-core caution).
- **`/decompose-proof`** — break one long proof into named sub-lemmas.
- **`/split-file`** — split an over-long file along namespace/section seams.
- **`Skill(simplify)`** — a holistic reuse/altitude review pass on a file (invoked inside `/cleanup` Phase 6.5).

## "emitted = projection": `<b>Lookups_eq_emitted` (proving a trace projection IS the emission)

Goal: prove a hand-written trace-level projection (`Soundness/*Consistency.lean`'s `stateLookups`,
`memoryLookups`, `programLookups`) equals the `toAccess`-image of what the circuit *actually emits* on that
channel — turning the projection from a parallel shadow into a derived theorem. **State, Program, and Memory
are DONE** (`stateLookups_eq_emitted`, `programLookups_eq_emitted`, `memoryLookups_eq_emitted`, all
axiom-clean). **Only Byte remains** (its emits are *carried by* the `RAC ⊃ RAT` subcircuits + `pullIf`
form — a recovery-*through*-nesting, not the drop-based recovery below).

Two foundations files: `Model/InteractionProjection.lean` (`AbstractInteraction.toAccess env`,
`signedVal` = the centered representative for `-is_real`-valued mults, and the per-channel
`toAccess_emitted_<msg>` kernels) and `Model/InteractionRecovery.lean` (the subcircuit-drop toolkit).

**Kernel form (critical).** `Channel.emit` produces `_root_.emitted`, and `circuit_norm` unfolds the
`@[circuit_norm] Channel.emitted` def to it — so the `toAccess_emitted_<msg>` kernels are stated on
`emitted (channel := <chan>) mult msg` (the `_root_.emitted` form), **not** `chan.emitted`. This lets the
kernel fire by `simp` directly, with no per-emit `rw [show … = chan.emitted … from rfl]` re-fold (which
doesn't scale past 1 emit). Kernel proof: `simp only [..., emitted, ...]` then a trailing `simp` — but the
9/16-field `toElements` unfold must be `simp only` (deterministic, linear); plain `simp` over the full set
blows up at `whnf` for the bigger structs.

**The recipe (worked for Program + Memory — a *composed* reader, `RTypeReader`):**
1. **Drop the byte-only subcircuits.** `have hnil : ∀ inp o, interactionsWith <chan>
   (RegisterAccessCols.elaborated.main inp o).2 = [] := by intro inp o; apply
   interactionsWith_main_snd_eq_nil; simp [circuit_norm, ElaboratedCircuit.channels]`. The `.2`-form
   `interactionsWith_main_snd_eq_nil` (InteractionRecovery) matches what `circuit_norm` leaves
   (`(main … off).2`, since `Circuit.operations c off = (c off).2`); it discharges `<chan> ∉ circuit.channels`
   from `ElaboratedCircuit.channels_subset` — needs the *symmetric* channel-distinctness
   (`memoryChannel_eq_byteChannel_false` etc.) + `ElaboratedCircuit.channels` in the simp set.
2. **Drop the `op_a_0 === 0` Equality gates.** `have heq := fun n inp =>
   filter_interactions_formalAssertion_eq_nil (Gadgets.Equality.circuit id) <chan> (n := n) inp
   List.not_mem_nil List.not_mem_nil` (the `===` desugars to `Gadgets.Equality.circuit id`, a
   `FormalAssertion` with no channels; TypeMap is `id` not `field`; `List.not_mem_nil` takes the element
   *implicitly* — no `_`).
3. **Reduce `interactionsWith` to the target emits.** `simp only [<rdr>.main, circuit_norm, hnil, heq,
   <otherchan>_eq_<chan>_false, if_false]` — the other bus's emits collapse via the explicit
   channel-distinctness `= False` lemma + `if_false` (`circuit_norm` alone leaves the `if … = … then`).
4. **Apply the kernel + bind.** `simp only [toAccess_emitted_<msg>]` then `simp [circuit_norm,
   signedVal_is_real hp2 h_real, signedVal_neg_is_real hp2 h_real, <Lookups>, <Access>, h_*]`. Realization
   hyps: WITNESSED columns as `env.get <offset> = r.cols.…` (`circuit_norm` turns `eval env (var ⟨off⟩)` into
   `env.get off`); INPUT fields as `Expression.eval env input.… = …`; SUBCIRCUIT-output columns as
   `Expression.eval env (RegisterAccessCols.elaborated.output ⟨…⟩ <off>).field = …` (these stay `eval env
   (output …)`, NOT `env.get`). `hp2 : 2 < p` from `Fact (2^17 < p)`.

**Byte (deferred — the different case; see `../architecture.md` §"Interaction half" and `../roadmap.md`).**
Byte's emits are *the content* of the `RAC ⊃ RAT` subcircuits (they
don't drop), so recovery must *recover* their emits through two levels of nesting (the State
`exposedChannels` route composed through nesting), plus a `pullIf` kernel (mult `-is_real`,
value-folded `is_real*value`). First the **byte faithfulness cleanup** removed the divergent reader byte
checks (CPUState's 4 `pc`, `RegisterAccessCols`'s 4 `prev_value`) SP1 has no analog of — so the readers now
emit exactly `ByteConsistency.byteRows`'s 8 checks, which is what makes byte `eq_emitted` well-posed.

## `ChipAir` / `Machine` (the cross-chip bus aggregate)

`Model/ChipAir.lean`: `ChipAir {name, perRow : Row → LookupAccessList, included}`, `Machine := List
(ChipAir Row)`, `Machine.busAggregate`/`busBalance` over the *computable* `InteractionBus`
core (never `noncomputable interactionsWith`). `multiplicitySum_busAggregate_cons` decomposes a machine's
per-key sum into per-chip sums. (The bespoke per-bus `ChipAir`s + `Machine` that drove the retired
`TraceValid` capstone lived in `Soundness/MachineConsistency.lean`, removed 2026-06-05; the surviving
statement-layer infra is `Model/ChipAir.lean`, and the live cross-chip argument is the gated
`Soundness/GatedVm/` path.) **Gotcha:** `Machine` is an `abbrev` for `List`, so `m.busAggregate`
dot-notation resolves to `List.busAggregate` — call `Machine.busAggregate m` explicitly. Statement layer
only: it makes Σsends = Σreceives expressible; it does not derive the per-bus meaning (those stay threaded).

## Build & verification gotchas (partly a repeat from LEAN_SAIL_NOTES)

- **`lake build <module>` is the only authoritative signal.** The lean-lsp diagnostics/`lean_goal`
  results can go stale and report a clean state while `lake build` still fails. Capture build output to a
  logfile and check the exit code; an empty log + `Build completed successfully` = real success.
- **`lake env lean <file>` does NOT rebuild edited dependencies — it silently checks against stale oleans.**
  `lake env` **only sets the environment; it builds nothing.** Measured: after one file was edited, its source
  was **4 hours newer than its `.olean`** while a `lake env lean` run on a *dependent* module resolved happily
  against the stale one and reported green. So the instrument is **stronger than the LSP on flags** (it
  applies the pillar's `moreLeanArgs`, which the LSP does not) and **weaker on freshness** (the LSP at least
  answers `Imports are out of date and must be rebuilt`). Neither is a pass oracle for a *pair* of edited
  files. Mitigations, in order: (1) work **deepest-first**, so each file is verified before its dependencies
  move; (2) after editing a dependency run `lake build <Dep.Module>` to refresh its olean, *then* re-verify the
  dependents; (3) treat a full `lake build SP1Clean` as the only joint confirmation. `lake env lean` also
  exits 0 on a Lean stack overflow, so it is sound only as a **falsifier**: a reported error is real, a clean
  run certifies nothing.
- **Diagnosing a stale olean:** compare `<Mod>.trace` against `<Mod>.trace.nobuild`. And if a module you
  touched does not appear in a build's job list, delete its `.olean`/`.ilean`/`.trace`/`.hash` and rebuild it
  explicitly — that distinguishes a genuine cached pass from an olean written seconds earlier by a dying
  process, which a 1-second no-op rerun cannot. **A rebuild on an immediate second `lake build` means the
  first run never persisted that olean, so the first run was not a pass.**
- **Absence from an *in-progress* job list is not evidence of a cache hit.** Lake prints a job line only on
  *completion*, so a 286s module is invisible for its entire run. Job-list absence is only meaningful once the
  build has exited. Relatedly, the critical path of a build is usually a module the edit never touched:
  `Faithful.DivRemChip.Exact` measured **298s of a 356s build** while not being in that round's changed set at
  all. Do not attribute build wall-clock to the files you edited.
- **Lake 4.31 in this toolchain has no `-j` option** — only `-J/--json` (`lake build SP1Clean -j 3` fails
  with `unknown short option '-j'`, and there is no top-level `-j` either). Control build concurrency by not
  running anything else, not by a flag.
- **Two different `lean` process shapes; they need different patterns.** *LSP file workers* are
  `lean --worker -Dserver.reportDelayMs=0 file:///…`, children of `lean --server` — these are what leak and
  hold GB after an agent exits (7 stale workers holding 22 GB RSS has been observed), and
  `pkill -f "lean --worker"` is the correct reaper. *Build workers* spawned by `lake build` have argv
  `lean --tstack=400000 -Dlinter.style.…` with **no `--worker` token**, so that grep pattern reports
  *nothing* mid-build — which reads as a hang. For build liveness use **`ps -ef | grep tstack`**, then
  `ps -o command= -p <pid>` to name the exact file being elaborated. **Never kill `lean --server` / `lake
  serve`**: the `lean-lsp` MCP server *is* that process, and killing it drops the MCP connection for the whole
  session.
- **When a build genuinely is hung, `sample <pid>` is the diagnostic — not RSS.** RSS is actively
  misleading: a *healthy* run plateaus at ~3.2 GB within 40 s (that is just the import footprint), which is
  indistinguishable from stuck. A stack sample discriminates immediately — `Lean_Meta_isDefEqDelta` /
  `whnfImp` / `unfoldDefinition` / `reduceRec` is a delta-unfolding blowup, not progress. It is cheap; reach
  for it before killing or before waiting longer.
- **Audit-harness quirks.** `scripts/run_audit.sh` **rewrites `docs/snapshots/axiom-census.txt` as a side
  effect, even on a pass**, so it leaves the tree dirty; inspect the delta before restoring, because an
  auto-generated `bv_decide` `ax_N_M✝` index moving *because a proof term changed* is **hygienic** — no axiom
  entered or left a set. Restore with a scratchpad `cp`, not `git checkout --` (the agent harness's guardrail
  script blocks that as destructive). And `run_audit.sh` does **not** invoke
  `scripts/check_report_citations.sh` — run it yourself, or its 16 hard-coded file+declaration citations go
  unchecked.
- Work one file and one build at a time; avoid batching many edit + LSP calls in a single turn.
- **LSP times out on a big chip file → introspect via a scratch `import`.** `lean_goal` on a 600+-line chip
  (e.g. `ShiftLeftChip.lean`'s completeness) times out because it re-elaborates the whole file. Instead write
  a throwaway `SP1Clean/Scratch.lean` = `import …<Chip>` + `example : …Completeness … := by
  circuit_proof_start; sorry`; the import is served from the cached olean, so only the tiny `example`
  elaborates live and `lean_goal` returns the full proof state instantly. Delete the scratch before
  committing (it lands in the lake glob).
