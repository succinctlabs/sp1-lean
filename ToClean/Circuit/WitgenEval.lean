import Clean.Circuit.WitnessIR

/-! # Struct-level witness-IR evaluation: `toElements` collapse and gated struct payloads

Two small layers Clean's witness IR is missing for *struct-shaped* witness payloads
(`x : M (Witgen.FExpr F)` for a `ProvableType M`):

* **The `toElements` evaluation collapse.** Clean has the `Expression.eval` versions
  (`ProvableType.toElements_eval` / `ProvableType.getElem_eval_toElements`,
  `Clean/Circuit/Provable.lean`) but no `Witgen` counterparts, so every per-cell fact about a
  flattened struct payload today needs a hand-written per-struct `toElements`-navigator family
  (see the 45-cell battery in SP1's `MulOperation`). `Witgen.toElements_eval` and
  `Witgen.getElem_eval_toElements` close that gap generically: one `rw` turns a flattened-cell
  evaluation into a cell of the struct-level `Witgen.eval`, where the payload's own semantic
  lemma applies. Both are definitional one-liners — the entire content is that `Witgen.eval` is
  `fromElements ∘ map eval ∘ toElements`.

* **Gated struct payloads.** Provers routinely populate a whole column struct only under a flag
  (`if is_real = 1 then populate … else zeroCols`). The witness IR has cell-level `.ite` only, so
  `Witgen.gateFE` (gate against the all-zero struct) and `Witgen.iteFE` (two-branch dispatch)
  lift it to the struct level, with eval lemmas that produce the value-level `if` directly.
  `gateFE` and `iteFE` are defined independently — defining one via the other would make their
  eval lemmas cross the `toElements` tower of a compound literal definitionally, which is
  exactly the `whnf` cliff this file exists to avoid.

## Upstream

Destined for `Clean/Circuit/WitnessIR.lean`, beside `Witgen.eval` and the `fields n`-specialised
`Witgen.eval_fields'` / `Witgen.FExpr.eval_getElem` (of which the two collapse lemmas are the
`ProvableType`-generic forms). Declared in the `Witgen` namespace they would occupy upstream, so
acceptance is a deletion plus dropping the import. -/

namespace Witgen

variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

/-- Flattening commutes with evaluation: the mapped `toElements` of a struct payload is the
`toElements` of its struct-level evaluation (the `Witgen` counterpart of
`ProvableType.toElements_eval`). -/
theorem toElements_eval (ctx : Ctx F) (x : M (FExpr F)) :
    (toElements x).map (FExpr.eval ctx) = toElements (Witgen.eval ctx x) := by
  simp only [Witgen.eval, ProvableType.toElements_fromElements]

/-- Evaluating one flattened cell of a struct payload is the cell of the struct-level
evaluation (the `Witgen` counterpart of `ProvableType.getElem_eval_toElements`). -/
theorem getElem_eval_toElements (ctx : Ctx F) (x : M (FExpr F)) (i : ℕ) (hi : i < size M) :
    FExpr.eval ctx (toElements x)[i] = (toElements (Witgen.eval ctx x))[i] := by
  simp only [Witgen.eval, ProvableType.toElements_fromElements, Vector.getElem_map]

/-- Gate a struct payload cell-wise against the all-zero struct: every cell becomes
`if c then cell else 0`. The struct-level form of the prover idiom
`if is_real = 1 then populate … else zeroCols`. -/
def gateFE (c : BExpr F) (x : M (FExpr F)) : M (FExpr F) :=
  fromElements ((toElements x).map fun e => FExpr.ite c e (.const 0))

/-- Dispatch between two struct payloads cell-wise on one condition. -/
def iteFE (c : BExpr F) (x y : M (FExpr F)) : M (FExpr F) :=
  fromElements ((toElements x).zip (toElements y) |>.map fun e => FExpr.ite c e.1 e.2)

/-- Evaluating a gated payload is the value-level `if` against the flattened zero struct. -/
theorem eval_gateFE (ctx : Ctx F) (c : BExpr F) (x : M (FExpr F)) :
    Witgen.eval ctx (gateFE c x)
      = if c.eval ctx then Witgen.eval ctx x
        else fromElements (Vector.replicate (size M) 0) := by
  simp only [gateFE, Witgen.eval, ProvableType.toElements_fromElements, Vector.map_map]
  split_ifs with h <;> congr 1 <;> ext i hi <;>
    simp [Function.comp, FExpr.eval, h]

/-- Evaluating a dispatched payload is the value-level `if` between the branch evaluations. -/
theorem eval_iteFE (ctx : Ctx F) (c : BExpr F) (x y : M (FExpr F)) :
    Witgen.eval ctx (iteFE c x y)
      = if c.eval ctx then Witgen.eval ctx x else Witgen.eval ctx y := by
  simp only [iteFE, Witgen.eval, ProvableType.toElements_fromElements, Vector.map_map]
  split_ifs with h <;> congr 1 <;> ext i hi <;>
    simp [Function.comp, FExpr.eval, h, Vector.getElem_zip]

/-- Environment-locality of a gated payload, from that of its condition and body. -/
theorem gateFE_congr (ctx ctx' : Ctx F) (c : BExpr F) (x : M (FExpr F))
    (hc : c.eval ctx = c.eval ctx') (hx : Witgen.eval ctx x = Witgen.eval ctx' x) :
    Witgen.eval ctx (gateFE c x) = Witgen.eval ctx' (gateFE c x) := by
  rw [eval_gateFE, eval_gateFE, hc, hx]

/-- Environment-locality of a dispatched payload. -/
theorem iteFE_congr (ctx ctx' : Ctx F) (c : BExpr F) (x y : M (FExpr F))
    (hc : c.eval ctx = c.eval ctx') (hx : Witgen.eval ctx x = Witgen.eval ctx' x)
    (hy : Witgen.eval ctx y = Witgen.eval ctx' y) :
    Witgen.eval ctx (iteFE c x y) = Witgen.eval ctx' (iteFE c x y) := by
  rw [eval_iteFE, eval_iteFE, hc, hx, hy]

/-! ### Congruence transport between the flattened site and the struct payload

`ComputableWitnesses` obligations arrive at the flattened `WitgenIR.ofFExprs` level while the
struct combinators above conclude at the `Witgen.eval` level; these three bridges move
congruences between the two without ever unfolding a `toElements` tower. -/

/-- Cell-level congruence from a site-level `ofFExprs` congruence. -/
theorem cell_congr_of_ofFExprs_congr {n : ℕ} {v : Vector (FExpr F) n}
    {env env' : ProverEnvironment F}
    (h : (WitgenIR.ofFExprs v).eval env = (WitgenIR.ofFExprs v).eval env')
    (i : ℕ) (hi : i < n) :
    v[i].eval { env := env } = v[i].eval { env := env' } := by
  rw [← WitgenIR.getElem_eval_ofFExprs v env i hi,
    ← WitgenIR.getElem_eval_ofFExprs v env' i hi, h]

/-- Struct-level congruence from the flattened site congruence. -/
theorem structEval_congr_of_ofFExprs_congr {x : M (FExpr F)}
    {env env' : ProverEnvironment F}
    (h : (WitgenIR.ofFExprs (toElements x)).eval env
      = (WitgenIR.ofFExprs (toElements x)).eval env') :
    Witgen.eval { env := env } x = Witgen.eval { env := env' } x := by
  rw [← ProvableType.fromElements_toElements (Witgen.eval { env := env } x),
    ← ProvableType.fromElements_toElements (Witgen.eval { env := env' } x)]
  refine congrArg fromElements (Vector.ext fun i hi => ?_)
  rw [← getElem_eval_toElements { env := env } x i hi,
    ← getElem_eval_toElements { env := env' } x i hi]
  exact cell_congr_of_ofFExprs_congr h i hi

/-- Flattened site congruence from the struct-level congruence. -/
theorem ofFExprs_congr_of_structEval_congr {x : M (FExpr F)}
    {env env' : ProverEnvironment F}
    (h : Witgen.eval { env := env } x = Witgen.eval { env := env' } x) :
    (WitgenIR.ofFExprs (toElements x)).eval env
      = (WitgenIR.ofFExprs (toElements x)).eval env' := by
  refine Vector.ext fun i hi => ?_
  rw [WitgenIR.getElem_eval_ofFExprs _ _ i hi, WitgenIR.getElem_eval_ofFExprs _ _ i hi,
    getElem_eval_toElements { env := env } x i hi,
    getElem_eval_toElements { env := env' } x i hi, h]

end Witgen
