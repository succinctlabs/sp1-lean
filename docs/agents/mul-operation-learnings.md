# MulOperation soundness & completeness — pitfalls & recipes

Patterns and pitfalls from the `MulOperation` `FormalCircuit` soundness **and completeness** proofs
(the 16-limb schoolbook multiply, 5 subcircuits, ~557 columns). These are the primary costs anyone
working on composed multi-column Clean circuits will likely hit. Complements
`proof-patterns.md` (general recipe) — this file is the *Mul-scale gotchas*. The `keep eval(output)
opaque` / `id (ZMod p)` / literal-default pitfalls below are SP1 instances of Clean's general
opaqueness doctrine — see `proof-patterns.md` §"Clean's unifying principle" and Clean's
`doc/performance-problems.md`.

**Status:** `MulOperation.soundness` **and** `MulOperation.completeness` are fully proved (all 5
variants, axiom-clean — `#print axioms` on each, and on `MulOperation.circuit`, shows only `[propext,
Classical.choice, Quot.sound]`). Soundness recipes: §1–§10; completeness: §11 (the concrete-witness
path) with the closed 16-chain-gate tactic in §11.5. `MulChip.soundness` composes it (see §12).

## 1. The `id (ZMod p)` carrier on evaluated outputs — the primary cost

After `circuit_proof_start`, the evaluated output struct `cols` and the chain hypotheses carry an
`id (ZMod p)` wrapper (the `ProvableType`/`verifierEval` instance produces `MulOperation (id (ZMod p))`).
Any `ring`/`linear_combination` then fails with:

```
failed to synthesize instance  IsRightCancelAdd (id (ZMod p))
```

This is **not** a missing-instance bug — it's the `id` wrapper hiding `ZMod p` from typeclass
resolution. **Fix:** `simp only [id_eq] at <the hyps you feed to linear_combination>` (and the goal if
needed). `id_eq : @id α a = a` rewrites the `id (ZMod p)` carrier back to `ZMod p`. Do this *before*
`linear_combination`. `show (_ : ZMod p) = _` alone does **not** help (it fixes the Eq carrier but not
the atom types).

## 2. `getD`-based column expressions in `main` block `circuit_norm` → heartbeat exhaustion

If `main` builds the constraint expressions through an indexed helper, e.g.
`let bE : ℕ → Expression _ := fun i => [b0, b1, …].getD i 0`, the `List.getD` is **opaque to
`circuit_proof_start`'s `circuit_norm`**. The chain hypotheses then arrive as
`env.get _ = Expression.eval env (big-getD-expr) + …` with the `eval` *unreduced*. Trying to reduce it
post-hoc is fatal: `simp [Expression.eval]` / `simp [circuit_norm]` whnf-reduce the
subcircuit-`output`-bearing leaves (`(ElaboratedCircuit.output …).low_bytes[i]`), which **unfolds the
composed subcircuits** and blows past 40M heartbeats.

**Fix: inline the column expressions in `main`** (no `getD`, no indexed `let`). Then
`circuit_proof_start` evaluates them once, cheaply, and each chain hypothesis comes out already in
`env.get`/byte form. This single change is what made soundness tractable.

## 3. `Expression.eval` in a simp set whnf-reduces `output` (don't)

`simp [Expression.eval]` matches `eval`'s constructor cases by whnf-reducing the argument. For
`eval ((output …).low_bytes[i])` that whnf unfolds the subcircuit `output` (`varFromOffset` + the
sub-op's `main`) → very slow. Keep `eval((output …).low_bytes[i])` as an **opaque atom** on both the
goal and the hypotheses so they match syntactically.

There are **no `eval_const` / `eval_var` simp lemmas** (only `Expression.eval_add` / `eval_mul`). For
the one var-leaf reduction you do need, use a local rfl lemma:
```lean
have evar : ∀ n : ℕ, Expression.eval env (Expression.var { index := n }) = env.get n := fun _ => rfl
```

## 4. `eval(input_var_b[i])` vs `input_b[i]` are different ring atoms

`circuit_proof_start` leaves operand reads as `Expression.eval env input_var_b[i]` in the chain
hypotheses, but the goal's `colSum`/`extendedBytes` uses the value `input_b[i]`. `ring` treats them as
distinct atoms → "ring failed, ring expressions not equal". Build the bridge facts and feed them to the
simp that normalizes the hypotheses:
```lean
have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp [Vector.getElem_map]
…
simp only [id_eq, eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3] at hch0 hch1 … hch15
```
(`hib`/`hic` are the `h_input` conjuncts `Vector.map (eval) input_var_b = input_b`.)

## 5. Literals default to ℕ in inline `Expression` products

`signs[0] * 255` inline elaborates `255 : ℕ` → `HMul (Expression _) ℕ` synth failure. Write
`signs[0] * (255 : ZMod p)` (the `HMul Expr F` instance). In a `List`/`![…]` element position the
`OfNat (Expression _)` coercion fires automatically, but **inline it does not** — so when you move
expressions out of a list into the constraint, annotate every bare numeral that multiplies an
`Expression`.

## 6. Inline `a * b * c` associativity

`bExpr * cExpr` where `cExpr` itself ends in `* 256⁻¹` flattens left-assoc to `(bExpr * (…)) * 256⁻¹`,
which can mis-elaborate. Parenthesize each factor: `(bExpr) * (cExpr)`.

## 7. Refolding the goal to route through a core `Spec` lemma

`circuit_proof_start` unfolds `Spec` into `Spec_body ∧ channel_obligations`. You **cannot** `apply
mulSemantics_of_raw` or `show Spec _ _` — Lean won't unify a metavar-headed `Spec ?i ?c` against the
unfolded goal (it won't delta-unfold `Spec` to assign the metavars). What works:
```lean
refine ⟨mulSemantics_of_raw (p := p) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
```
The core lemma's *whole* `Spec` body unifies with the goal's grouped first conjunct, inferring `cols`.
The trailing channel obligations close with `· and_intros <;> exact Or.inl rfl`
(`channelsWithRequirements = []` for these subcircuits/range-checks).

Always pass `(p := p)` explicitly — otherwise resolution stalls on `Fact (2^24 < ?p)` before `p` is
known.

## 8. `output` / `output_eq` for a mid-struct hidden-column subcircuit — just omit it

The documented "varFromOffset desync" wall (a `subcircuit` consumes its full `localLength`, e.g. 68,
not its provable size, e.g. 4, so a mid-struct sub-op shifts every later field) is **moot**: do **not**
set `output := varFromOffset` and do **not** write a custom offset-based `output`. Simply **omit both
`output` and `output_eq`** from the `ElaboratedCircuit` instance. The default
`output := fun _ off => (main input).output off` is by-construction correct, and `output_eq` defaults
to `rfl`. (`localLength_eq`/`subcircuitsConsistent` stay as the usual
`simp [circuit_norm, main, <SubOp>.circuit]` proofs.)

## 9. `![…] ⟨k, h⟩` indexing needs full `simp`, not `simp only`

`byteAt`/`extendedBytes` produce `![e0,…,e15] ⟨k, h⟩` where the Fin index `⟨k, h⟩` (from a `dite`
proof) is **not** syntactically the literal `k`, so `simp only [Matrix.cons_val_zero, …]` won't fire.
Full `simp` carries the Fin/Matrix simprocs that reduce it. Likewise concrete `dite`/`ite` need the
`reduceDIte`/`reduceIte` simprocs (present in full `simp`, must be listed in `simp only`).

## 10. The working soundness chain-gate tactic (k = 0..15)

```lean
have evar : ∀ n : ℕ, Expression.eval env (Expression.var { index := n }) = env.get n := fun _ => rfl
simp only [id_eq, eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3] at hch0 … hch15   -- strip id + reduce operand reads
interval_cases k <;>
  (simp [productVal, carryVal, colSum, byteAt, extendedBytes, Finset.sum_range_succ,
     Finset.sum_range_zero, Vector.getElem_map, Vector.getElem_mapRange, evar] <;>
   first | linear_combination hch0 | … | linear_combination hch15)
```
(16 explicit per-`k` bullets also work and pinpoint a failing `k` when debugging.) Wrap the theorem in
`set_option linter.unusedSimpArgs false in` because the shared full-`simp` arg list is unused on the
`k = 0` column.

## 11. Three composed `U16MSBOperation`s — structure and proof patterns

`MulOperation` composes three `U16MSBOperation` `FormalAssertion`s (one for each of `b`, `c`,
`product`). Mul **stays a `FormalCircuit`** (it has genuine aux columns — carry, `b_lower`/`c_lower` —
that its semantic `Spec` does *not* pin); only the composition of the three sign-bit MSBs uses the
assertion interface. Each MSB is witnessed via `witnessVector 1` and constrained via `assertion
U16MSBOperation.circuit`. Key technical facts:

- **Offset-safety.** The three MSBs sit *after* every column the soundness body references — it reads only
  carry `i₀+k` and product `i₀+16+k`. The `witnessVector`s occupy the same offsets as the old subcircuits,
  so all `env.get` indices are identical and the 16 chain bullets (§10) require no edits. *Always* place a
  demoted sub-op at its old first column.
- **`mulSemantics_of_raw`'s `hmsb` param** takes the raw bit-equality
  (`cols.product_msb.msb = if (product[2] + product[3]*256).val ≥ 32768 then 1 else 0`) directly; the
  soundness site supplies it from the gated sub-Spec.
- **Gated `Assumptions` at the three sites.** `U16MSBOperation.Assumptions` is
  `(is_real = 1 → a.val < 2^16) ∧ is_real ∈ {0,1}` (gated — see `proof-patterns.md`).
- **Elaborated-field simp set.** Keep `U16MSBOperation.circuit` in `localLength_eq` /
  `subcircuitsConsistent`; use `simp only` (not `simp`) for `channelsLawful`, including
  `Gadgets.ToBits.rangeCheck` to reduce the 32 rangeCheck subcircuits'
  `channelsWithRequirements field unit = []`. Set `maxHeartbeats 40000000` on the instance. Declare
  `channelsWith{Guarantees,Requirements} := [byteChannel.toRaw]` + the three `@[circuit_norm]` rfl-lemmas.
- **Soundness channel-requirement tail.** `circuit_proof_start` collapses each MSB's `[] ∨ Assumptions`
  disjunct; `and_intros` splits into `(is_real = 1 → bound)` + `is_real ∈ {0,1}`:
  ```lean
  and_intros <;> first
    | exact Or.inl rfl | exact Or.inr rfl
    | (intro _; first | (rw [eb3]; exact hbU3) | (rw [ec3]; exact hcU3)
                      | (rw [byte_compose_val pb2 pb3 rfl]; omega))
  ```

## 12. Completeness — the concrete-witness path (no converse lemma)

Because `main` witnesses **concrete** `schoolCarry`/`schoolProduct` columns (definitionally
`MulCarryChain.carry`/`product (cpNat (extStream …))`), completeness discharges every constraint
*forward* — there is **no** converse lemma (unlike `AddwOperation.completeness`, a `FormalAssertion`).
After `circuit_proof_start`, `h_env` exposes everything: the carry/product witnesses (`∀ i:Fin 16,
env.get (i₀+i) = …`), the **gated U16toU8 Specs** (`U16toU8.Assumptions → Spec`, dischargeable), the
three msb witnesses (`= populate_msb …`), and the signs witnesses.

Two **crux bridge lemmas** (the conceptual core, both in `MulOperation.lean` before `completeness`):
- `byteAt_extendedBytes_val`: `(byteAt (extendedBytes w lower s) i).val = extStream w[*].val s.val i`.
  Landmines: give the `byte_compose_val` facts **explicit `w[j]` types** (the U16toU8 `Spec` phrases
  them via `⟨w⟩.u16_values[j]`, a *distinct* `omega` atom from `w[j]`); and use `show <component>.val =
  <extStream value>` per case — `byteAt`'s `if`, the `![…]` Matrix index, and `extStream`'s `getD` all
  *compute* (defeq) but do **not** `simp`-reduce at literal Fin/Nat indices.
- `colSum_eq_cpNat`: `colSum (extendedBytes …) … k = (cpNat (extStream …) … k : ZMod p)` for `k<16`.
  Via `colSum_val` + the byte bridge + a `(range 16).filter (·≤k) = range (k+1)` reindex + `←
  ZMod.natCast_zmod_val`.

Assembly (`refine` skeleton, structure confirmed): `⟨?uba, ?uca, ⟨?mba,?mbs⟩, ⟨?mca,?mcs⟩, ⟨?mpa,?mps⟩,
⟨trivial,?c0⟩…⟨trivial,?c15⟩, ⟨trivial,?p0⟩…⟨trivial,?p15⟩, ?sd0,?sd1,?sb0,?sb1, ?ch0…?ch15⟩`. Setup:
the eval bridges, a flag-val bound (`Σ flag.val ≤ 1` from `sum ∈ {0,1}` via the val-cast argument), the
`extStream` byte bounds (`extStream_le`/`extStream_eq_zero`), the **total** `hcp : ∀ i, cpNat … i ≤
cpBound` (via `cpNat_le_cpBound_total` — the `i≥16` totality the obvious `cpNat_le_cpBound` misses), and
`hcarry_lt`/`hprod_lt` (via `carry_lt`/`product_lt` + `carry_val`/`product_val`). Discharge: the 32
rangeChecks `⟨trivial, by simpa only [Gadgets.ToBits.rangeCheck] using hcarry_lt/hprod_lt k …⟩`; U16toU8
`⟨hbU0..hbU3⟩`; U16MSB via `spec_populate` (msb = `populate_msb` from `h_env`); sign defs via the signs
witnesses (`simpa using hsg_w 0/1`); sign bools via msb bit-ness (`populate_msb` of a `<2^16` value is
`0/1` — close with `simp`, **not** `ring` → info-note).

## 12.5. The working completeness chain-gate tactic (k = 0..15)

The 16 chain gates `case ch0..ch15` close with one uniform recipe (the mirror image of the soundness
chain step §10). Per gate `k`, goal `env.get (i₀+16+k) = <inline byte expr> + carry terms`:

```lean
case ch<k> =>
  rw [hp_eq <k> (by norm_num), hc_eq <k> (by norm_num), hc_eq <k-1> (by norm_num)]  -- → MulCarryChain form
  have hcs := colSum_eq_cpNat input_b input_c _ _ _ _ hbl hcl hsb hsc <k> (by norm_num)
  rw [hbse_val, hcse_val, ← hCPW] at hcs               -- fold the in-circuit colSum to ↑(CPW k)
  simp [colSum, byteAt, extendedBytes, Finset.sum_range_succ, Vector.getElem_map] at hcs  -- expand colSum
  simp only [id_eq, eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3]   -- strip goal's `id`; normalise eval(input_var_*)
  linear_combination (MulCarryChain.gate_succ CPW <k-1>) - hcs
```

Five things that bite, each load-bearing:
- **Position rewrites.** `hp_eq k`/`hc_eq k` carry the `+0`-free quirk at the low end: `k=0` uses
  `hp_eq0, hc_eq0` (the columns appear as `env.get (i₀+16)` / `env.get i₀`, no `+0`); `k=1`'s carry-in
  is also `env.get i₀`, so use `hc_eq0`, not `hc_eq 0` (whose `env.get (i₀+0)` won't `rw`-match).
- **The `id (ZMod p)` carrier** (Learnings §1) is on the *goal* here, not the hyps. Without
  `simp only [id_eq]` on `⊢`, `linear_combination` fails with `IsRightCancelAdd (id (ZMod p))`.
- **`eval(input_var_*)` vs `input_*`** (§4): the goal's high-byte numerators read `Expression.eval …
  input_var_b[j]` while `hcs` (from `colSum_eq_cpNat`, which takes `w = input_b`) has `input_b[j]`.
  Normalise the goal with `eb0..ec3` or `ring` sees distinct atoms.
- **`colSum` needs full `simp`** (§9) + `Finset.sum_range_succ` to expand `∑ x ∈ range 16` (default
  `simp` alone leaves the sum symbolic for `k ≥ 1`).
- **Put the gate lemma IN the `linear_combination`, with a `- hcs` sign — do NOT `rw` it.** A numeral
  index like `2` won't unify with `gate_succ`'s `?i + 1` under `rw`; as a `linear_combination` term the
  defeq `(k-1)+1 = k` is handled by ring. Sign: goal is `product = inline + carry_in − carry_out·256`,
  gate gives `product = cp + carry_in − carry_out·256`, `hcs` gives `inline = cp`, so the combination
  is `gate − hcs`. `k = 0` uses `gate_zero CPW` (no carry-in).

The theorem carries `set_option linter.unusedSimpArgs false in` because low-`k` columns leave some of
the shared `eb*/ec*` (and `Finset.sum_range_succ` at `k=0`) unused. `colSum_eq_cpNat`'s middle four
args (`lower lower' s s'`) are left as `_` — inferred from `hbl`/`hcl`/`hsb`/`hsc`.

## 13. MulChip composition — the `sum = 1` channel-tail trap (option A)

`MulChip` composes `MulOperation.circuit` as a `subcircuit`. The chip soundness's channel-requirement
tail asks for `MulOperation.Assumptions` **unconditionally**, but that originally included `sum = 1`,
which **fails on padding rows** (`is_real = 0 ⇒ all flags 0 ⇒ sum = 0`). Fix (the faithful one):
**weaken `MulOperation.Assumptions` from `sum = 1` to `sum ∈ {0,1}`** and re-prove its soundness —
inside each gated `Spec` conjunct, recover `sum = 1` from the active flag via `sum_eq_one` before
`rest_zero` (the `isU64`-of-`resultWord` conjunct needs no `sum = 1`). The `a ↔ resultWord` linkage:
`main` witnesses `a` and asserts it equals the flag-weighted product slice `aSelector`; soundness uses
`aSelector_eq_resultWord` (collapse via `rest_zero`) then the five `rv64_mul*_eq` BitVec bridges. **Build
trap:** `lake env lean MulChip` loads `MulOperation`'s *olean* — after editing `MulOperation` you must
`lake build SP1Clean.Native.Operations.MulOperation` before checking `MulChip`, else stale signatures
cause spurious mismatches. `bv_decide` in the bridges adds `Lean.ofReduceBool`/`trustCompiler` (accepted).

## Tooling notes

- **Generate the N-limb boilerplate programmatically.** Every 16-wide artifact here — `full_product`,
  `product_reassembly`, `extendedBytes_toNat`, `high_half_eq`, the inline `main` columns, the
  57-component `h_holds` destructure, the 16 chain bullets — is best emitted by a small script rather than
  hand-typed; the schoolbook convolutions are otherwise transcription-error-prone.
- **Heartbeats:** the Mul soundness needs `set_option maxHeartbeats 40000000` (the cost is the per-`k`
  `interval_cases` over the huge `cols`, not the arithmetic). `circuit_norm` on many large hypotheses
  is the thing to avoid.
