import Clean.Circuit.WitnessIR

/-! # Environment-locality of the witness IR

A witness generator is *local* when its output depends on the environment only through the circuit
expressions it embeds. For the `.native` constructor that is unknowable — an arbitrary Lean closure
has no read set. For `.ir` it is decidable by inspection: the only ways an `.ir` program touches the
environment are `FExpr.expr` (an embedded circuit expression), `VExpr.envRange` (a run of raw cells),
and `FExpr.dataGet`/`hintGet` (committed data / prover hints).

This module makes that precise. `FExpr.exprs` and friends collect the embedded expressions;
`VExpr.envIndices` collects the raw cells; and `WitgenIR.eval_congr` says that two environments
agreeing on exactly those produce the same witnesses.

## Why it matters

`Circuit.ComputableWitnesses` — the precondition of Clean's honest-witness-generation theorem
`Circuit.witgen_usesLocalWitnesses` — is exactly a witness-congruence obligation. Without a
structural lemma, each gadget discharges it by unfolding its own IR under `simp`, which is both
per-gadget work and a performance trap: `circuit_norm` carries the `u64Wrap` simproc, which runs
`omega` on every `% 2 ^ 64` subterm, and in a congruence goal there are no bounds in scope for those
`omega` calls to use, so every one of them fails at full cost. (Measured downstream: ≥32×, still
failing at eight times the default heartbeat budget, versus a quarter of the default with the
simproc disabled.) Applying a lemma instead of simping the IR body avoids the trap entirely.

## Upstream

Destined for Clean, beside `Clean/Circuit/WitnessIR.lean`'s evaluator or
`Clean/Circuit/Subcircuit.lean`'s `compose_computableWitnesses`. Clean has exactly one
`ComputableWitnesses` instance in tree (`Gadgets/Addition8/Addition8FullCarry.lean`), discharged by
a bespoke `simp_all` that works only because that gadget has no subcircuits and flat field inputs;
any composed circuit needs this.

Note the `data`/`hint` premises: `ProverEnvironment.AgreesBelow` constrains only `get`, so a witness
reading `dataGet`/`hintGet` cannot satisfy `ComputableWitnesses` as Clean currently states it. Adding
those two conjuncts to `AgreesBelow` upstream is a small non-breaking change (it *weakens* every
obligation, and both `ProverEnvironment.fromList` and `.fromArray` carry constant `data`/`hint`, so
the new components are `rfl` at every use site) — and it is what makes those two constructors
provable here rather than fatal. -/

namespace Witgen

variable {F : Type} [FiniteField F]

/-! ## The read set -/

mutual

/-- The circuit expressions a field-sorted IR expression embeds. -/
def FExpr.exprs : FExpr F → List (Expression F)
  | .expr e => [e]
  | .const _ => []
  | .localVar _ => []
  | .add x y => x.exprs ++ y.exprs
  | .mul x y => x.exprs ++ y.exprs
  | .inv x => x.exprs
  | .ofU64 n => n.exprs
  | .ite c t e => c.exprs ++ t.exprs ++ e.exprs
  | .listGet xs i => FExpr.exprsList xs ++ i.exprs
  | .dataGet _ _ row _ => row.exprs
  | .hintGet _ _ row _ => row.exprs

/-- Pointwise over a list, as a separate recursor: `listGet` is a nested occurrence, which the
equation compiler cannot see through with `List.flatMap`. Mirrors Clean's own `FExpr.evalList`. -/
def FExpr.exprsList : List (FExpr F) → List (Expression F)
  | [] => []
  | x :: xs => x.exprs ++ FExpr.exprsList xs

/-- The circuit expressions a u64-sorted IR expression embeds. -/
def U64Expr.exprs : U64Expr F → List (Expression F)
  | .const _ => []
  | .val x => x.exprs
  | .idx => []
  | .localVar _ => []
  | .add x y => x.exprs ++ y.exprs
  | .mul x y => x.exprs ++ y.exprs
  | .div x y => x.exprs ++ y.exprs
  | .mod x y => x.exprs ++ y.exprs
  | .land x y => x.exprs ++ y.exprs
  | .lor x y => x.exprs ++ y.exprs
  | .lxor x y => x.exprs ++ y.exprs
  | .shiftL x y => x.exprs ++ y.exprs
  | .shiftR x y => x.exprs ++ y.exprs
  | .ite c t e => c.exprs ++ t.exprs ++ e.exprs

/-- The circuit expressions a condition embeds. -/
def BExpr.exprs : BExpr F → List (Expression F)
  | .true => []
  | .false => []
  | .feq x y => x.exprs ++ y.exprs
  | .neq x y => x.exprs ++ y.exprs
  | .lt x y => x.exprs ++ y.exprs
  | .flt x y => x.exprs ++ y.exprs
  | .bit x _ => x.exprs
  | .not b => b.exprs
  | .and x y => x.exprs ++ y.exprs

end

/-- The circuit expressions a `let`-step embeds. -/
def Step.exprs : Step F → List (Expression F)
  | .letF e => e.exprs
  | .letU e => e.exprs

/-- The circuit expressions a vector former embeds. -/
def VExpr.exprs : {n : ℕ} → VExpr F n → List (Expression F)
  | _, .lit es => FExpr.exprsList es.toList
  | _, .mapRange _ body => body.exprs
  | _, .envRange _ => []
  | _, .bitsOf x => x.exprs
  | _, .append a b => a.exprs ++ b.exprs

/-- The raw environment cells a vector former reads directly (only `envRange` does). -/
def VExpr.envIndices : {n : ℕ} → VExpr F n → List ℕ
  | _, .lit _ => []
  | _, .mapRange _ _ => []
  | n, .envRange offset => (List.range n).map (offset + ·)
  | _, .bitsOf _ => []
  | _, .append a b => a.envIndices ++ b.envIndices

/-- Everything a witness program reads: the embedded expressions of its steps and its output. A
`.native` payload has no inspectable read set, so it collects nothing — and correspondingly gets no
congruence below. -/
def WitgenIR.exprs : {m : ℕ} → WitgenIR F m → List (Expression F)
  | _, .native _ => []
  | _, .ir steps out => steps.flatMap Step.exprs ++ out.exprs

/-- The raw cells a witness program reads directly. -/
def WitgenIR.envIndices : {m : ℕ} → WitgenIR F m → List ℕ
  | _, .native _ => []
  | _, .ir _ out => out.envIndices

/-! ## Context agreement -/

/-- Two evaluation contexts agree when their `let`-step values and loop index coincide, and their
environments carry the same committed data and prover hints. Expression- and cell-level agreement is
tracked separately, per term, because that is what varies. -/
structure CtxAgree (ctx ctx' : Ctx F) : Prop where
  locals : ctx.locals = ctx'.locals
  idx : ctx.idx = ctx'.idx
  data : ctx.env.data = ctx'.env.data
  hint : ctx.env.hint = ctx'.env.hint

namespace CtxAgree

omit [FiniteField F] in
theorem refl (ctx : Ctx F) : CtxAgree ctx ctx := ⟨rfl, rfl, rfl, rfl⟩

omit [FiniteField F] in
/-- Re-index both contexts (the `mapRange` body step). -/
theorem withIdx {ctx ctx' : Ctx F} (h : CtxAgree ctx ctx') (i : ℕ) :
    CtxAgree { ctx with idx := i } { ctx' with idx := i } :=
  ⟨h.locals, rfl, h.data, h.hint⟩

omit [FiniteField F] in
/-- Replace both `locals` by a common value (the `evalSteps` fold step). -/
theorem withLocals {ctx ctx' : Ctx F} (h : CtxAgree ctx ctx') (l : Array (F ⊕ UInt64)) :
    CtxAgree { ctx with locals := l } { ctx' with locals := l } :=
  ⟨rfl, h.idx, h.data, h.hint⟩

end CtxAgree

/-- Abbreviation for "these two contexts evaluate every expression in `es` the same way". -/
def AgreeOn (ctx ctx' : Ctx F) (es : List (Expression F)) : Prop :=
  ∀ e ∈ es, Expression.eval ctx.env.toEnvironment e = Expression.eval ctx'.env.toEnvironment e

theorem AgreeOn.left {ctx ctx' : Ctx F} {es es' : List (Expression F)}
    (h : AgreeOn ctx ctx' (es ++ es')) : AgreeOn ctx ctx' es :=
  fun e he => h e (List.mem_append_left _ he)

theorem AgreeOn.right {ctx ctx' : Ctx F} {es es' : List (Expression F)}
    (h : AgreeOn ctx ctx' (es ++ es')) : AgreeOn ctx ctx' es' :=
  fun e he => h e (List.mem_append_right _ he)

/-! ## The congruences

One mutual block over the three expression sorts, mirroring their mutual definition. Every case is
either a leaf (`const`, `idx`, `localVar` — the last by `CtxAgree.locals`) or a congruence of the
evaluator applied to the inductive hypotheses, with `AgreeOn.left`/`.right` splitting the read set
along the same `++` the definitions produced. -/

mutual

theorem FExpr.eval_congr {ctx ctx' : Ctx F} (hc : CtxAgree ctx ctx') :
    ∀ (x : FExpr F), AgreeOn ctx ctx' x.exprs → x.eval ctx = x.eval ctx'
  | .expr e, h => h e (by simp [FExpr.exprs])
  | .const _, _ => rfl
  | .localVar _, _ => by simp only [FExpr.eval, hc.locals]
  | .add x y, h => by
      simp only [FExpr.eval, FExpr.eval_congr hc x h.left, FExpr.eval_congr hc y h.right]
  | .mul x y, h => by
      simp only [FExpr.eval, FExpr.eval_congr hc x h.left, FExpr.eval_congr hc y h.right]
  | .inv x, h => by simp only [FExpr.eval, FExpr.eval_congr hc x h]
  | .ofU64 n, h => by simp only [FExpr.eval, U64Expr.eval_congr hc n h]
  | .ite c t e, h => by
      simp only [FExpr.eval, BExpr.eval_congr hc c h.left.left,
        FExpr.eval_congr hc t h.left.right, FExpr.eval_congr hc e h.right]
  | .listGet xs i, h => by
      simp only [FExpr.eval, U64Expr.eval_congr hc i h.right]
      exact FExpr.evalList_congr hc _ xs h.left
  | .dataGet _ _ row _, h => by
      simp only [FExpr.eval, U64Expr.eval_congr hc row h, hc.data]
  | .hintGet _ _ row _, h => by
      simp only [FExpr.eval, U64Expr.eval_congr hc row h, hc.hint]

theorem FExpr.evalList_congr {ctx ctx' : Ctx F} (hc : CtxAgree ctx ctx') :
    ∀ (i : ℕ) (xs : List (FExpr F)), AgreeOn ctx ctx' (FExpr.exprsList xs) →
      FExpr.evalList ctx i xs = FExpr.evalList ctx' i xs
  | _, [], _ => rfl
  | 0, x :: _, h => by
      simp only [FExpr.evalList]
      exact FExpr.eval_congr hc x h.left
  | i + 1, _ :: xs, h => by
      simp only [FExpr.evalList]
      exact FExpr.evalList_congr hc i xs h.right

theorem U64Expr.eval_congr {ctx ctx' : Ctx F} (hc : CtxAgree ctx ctx') :
    ∀ (x : U64Expr F), AgreeOn ctx ctx' x.exprs → x.eval ctx = x.eval ctx'
  | .const _, _ => rfl
  | .val x, h => by simp only [U64Expr.eval, FExpr.eval_congr hc x h]
  | .idx, _ => by simp only [U64Expr.eval, hc.idx]
  | .localVar _, _ => by simp only [U64Expr.eval, hc.locals]
  | .add x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .mul x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .div x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .mod x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .land x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .lor x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .lxor x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .shiftL x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .shiftR x y, h => by
      simp only [U64Expr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .ite c t e, h => by
      simp only [U64Expr.eval, BExpr.eval_congr hc c h.left.left,
        U64Expr.eval_congr hc t h.left.right, U64Expr.eval_congr hc e h.right]

theorem BExpr.eval_congr {ctx ctx' : Ctx F} (hc : CtxAgree ctx ctx') :
    ∀ (x : BExpr F), AgreeOn ctx ctx' x.exprs → x.eval ctx = x.eval ctx'
  | .true, _ => rfl
  | .false, _ => rfl
  | .feq x y, h => by
      simp only [BExpr.eval, FExpr.eval_congr hc x h.left, FExpr.eval_congr hc y h.right]
  | .neq x y, h => by
      simp only [BExpr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .lt x y, h => by
      simp only [BExpr.eval, U64Expr.eval_congr hc x h.left, U64Expr.eval_congr hc y h.right]
  | .flt x y, h => by
      simp only [BExpr.eval, FExpr.eval_congr hc x h.left, FExpr.eval_congr hc y h.right]
  | .bit x _, h => by simp only [BExpr.eval, FExpr.eval_congr hc x h]
  | .not b, h => by simp only [BExpr.eval, BExpr.eval_congr hc b h]
  | .and x y, h => by
      simp only [BExpr.eval, BExpr.eval_congr hc x h.left, BExpr.eval_congr hc y h.right]

end

/-- The `let`-step fold: equal starting locals and agreeing step expressions give equal results.
This is where `CtxAgree.locals` is *established* rather than assumed. -/
theorem evalSteps_congr {env env' : ProverEnvironment F}
    (hdata : env.data = env'.data) (hhint : env.hint = env'.hint) :
    ∀ (steps : List (Step F)) (locals : Array (F ⊕ UInt64)),
      (∀ e ∈ steps.flatMap Step.exprs,
        Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e) →
      evalSteps env steps locals = evalSteps env' steps locals
  | [], _, _ => rfl
  | .letF e :: steps, locals, h => by
      have hc : CtxAgree (F := F) { env, locals } { env := env', locals } := ⟨rfl, rfl, hdata, hhint⟩
      have hstep : e.eval { env, locals } = e.eval { env := env', locals } :=
        FExpr.eval_congr hc e fun x hx => h x (by simp [Step.exprs, hx])
      simp only [evalSteps, hstep]
      exact evalSteps_congr hdata hhint steps _ fun x hx => h x (by simp [hx])
  | .letU e :: steps, locals, h => by
      have hc : CtxAgree (F := F) { env, locals } { env := env', locals } := ⟨rfl, rfl, hdata, hhint⟩
      have hstep : e.eval { env, locals } = e.eval { env := env', locals } :=
        U64Expr.eval_congr hc e fun x hx => h x (by simp [Step.exprs, hx])
      simp only [evalSteps, hstep]
      exact evalSteps_congr hdata hhint steps _ fun x hx => h x (by simp [hx])

omit [FiniteField F] in
/-- An element's read set is contained in the list's. -/
theorem FExpr.mem_exprsList : ∀ {x : FExpr F} {xs : List (FExpr F)}, x ∈ xs →
    ∀ e ∈ x.exprs, e ∈ FExpr.exprsList xs
  | x, _ :: xs, hx, e, he => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (FExpr.mem_exprsList hx e he)

/-- Vector formers. `envRange` is the only one reading raw cells, hence the `hcells` premise —
vacuous for every other former, and `VExpr.envIndices` is `[]` there. -/
theorem VExpr.eval_congr {ctx ctx' : Ctx F} (hc : CtxAgree ctx ctx') :
    ∀ {n : ℕ} (v : VExpr F n), AgreeOn ctx ctx' v.exprs →
      (∀ i ∈ v.envIndices, ctx.env.get i = ctx'.env.get i) →
      v.eval ctx = v.eval ctx'
  | _, .lit es, h, _ => by
      simp only [VExpr.eval]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map]
      have hmem : es[i] ∈ es.toList := List.getElem_mem (by simpa using hi)
      exact FExpr.eval_congr hc es[i] fun x hx => h x (FExpr.mem_exprsList hmem x hx)
  | _, .mapRange n body, h, _ => by
      simp only [VExpr.eval]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_mapRange]
      exact FExpr.eval_congr (hc.withIdx i) body h
  | _, .envRange offset, _, hcells => by
      simp only [VExpr.eval]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_mapRange]
      exact hcells _ (by
        simp only [VExpr.envIndices, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  | _, .bitsOf x, h, _ => by
      simp only [VExpr.eval, FExpr.eval_congr hc x h]
  | _, .append a b, h, hcells => by
      simp only [VExpr.eval, VExpr.eval_congr hc a h.left fun i hi => hcells i (by simp [VExpr.envIndices, hi]),
        VExpr.eval_congr hc b h.right fun i hi => hcells i (by simp [VExpr.envIndices, hi])]

/-! ## The capstone -/

/-- **A witness program reads the environment only through its own read set.**

Two prover environments carrying the same committed data and prover hints, and agreeing on every
circuit expression the program embeds and every raw cell it reads, produce identical witnesses.

This is the lemma to *apply* when discharging `Circuit.ComputableWitnesses` — never unfold the IR
body under `simp [circuit_norm]` to do it (see the module docstring on `u64Wrap`).

`.native` is excluded rather than assumed away: its read set is genuinely unknowable, which is why
a chip must be on the `.ir` form before it can be shown to generate witnesses honestly. -/
theorem WitgenIR.eval_congr {m : ℕ} {env env' : ProverEnvironment F}
    (steps : List (Step F)) (out : VExpr F m)
    (hdata : env.data = env'.data) (hhint : env.hint = env'.hint)
    (hexprs : ∀ e ∈ (WitgenIR.ir (F := F) steps out).exprs,
      Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e)
    (hcells : ∀ i ∈ (WitgenIR.ir (F := F) steps out).envIndices, env.get i = env'.get i) :
    (WitgenIR.ir steps out).eval env = (WitgenIR.ir steps out).eval env' := by
  have hsteps : evalSteps env steps = evalSteps env' steps :=
    evalSteps_congr hdata hhint steps _ fun e he =>
      hexprs e (List.mem_append_left _ he)
  simp only [WitgenIR.eval, hsteps]
  exact VExpr.eval_congr
    (ctx := { env, locals := evalSteps env' steps })
    (ctx' := { env := env', locals := evalSteps env' steps })
    ⟨rfl, rfl, hdata, hhint⟩ out
    (fun e he => hexprs e (List.mem_append_right _ he))
    (fun i hi => hcells i hi)

end Witgen
