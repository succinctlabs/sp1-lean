module

public import Clean.Circuit.StructEvalSimprocs
public import Clean.Utils.Tactics.ProvableStructDeriving
public meta import Lean

/-! # Per-field evaluation lemmas for a `ProvableStruct`

**Gap against upstream.** Clean's `circuit_norm` normal form for struct evaluation is
component-preserving: `ProvableStruct.eval env ⟨a, b⟩` on a *literal* decomposes into
`⟨eval env a, eval env b⟩` (the `StructEvalSimprocs`), and `Expression.eval env s.x` on a
*variable* `s` is meant to lift to `(ProvableStruct.eval env s).x`. The lift never fires: its
proof needs `toComponents s` to reduce on a variable, which matchers no longer do (the doc-comment
of `StructEvalSimprocs.lean` records the same change). So a proof that holds a row-level fact
`(ProvableStruct.eval env s).x = …` against a goal in the constraint form `Expression.eval env s.x`
has no `circuit_norm` bridge, and Clean's own `Examples/FemtoCairo/TypesLemmas.lean` writes the
bridge by hand, once per field:

```lean
@[circuit_norm] lemma State.eval_pc (env : Environment F) (s : Var State F) :
    (eval env s).pc = Expression.eval env s.pc := by
  obtain ⟨pc, ap, fp⟩ := s
  simp [circuit_norm, explicit_provable_type]
```

`provable_struct_eval_lemmas S` generates exactly those lemmas for every field of `S` (proof:
`cases s; simp only [circuit_norm]`, so the right-hand side lands in whatever normal form the
field's type has — `Expression.eval` for a scalar, `Vector.map (Expression.eval env)` for a
`Vector F n`, `ProvableStruct.eval` for a nested struct). Scalar and nested-struct lemmas are
`circuit_norm` members; a `Vector F n` field's lemma is declared but left untagged, because
Clean's indexing simproc does lift `Expression.eval env s.c[i]` to `(ProvableStruct.eval env s).c[i]`
and the two would loop. Upstream home: the `deriving ProvableStruct` handler, next to the
`fromComponents_cons` lemma it already emits. Supported shape: a structure whose only parameter
is `(F : Type)`. -/

@[expose] public section

namespace ProvableStruct

variable {F : Type} [FiniteField F]

/-- The cell-wise reading of "the evaluated struct variable at `offset` is `w`" (the shape a
`witnessVector`-style witness condition takes once `circuit_norm` has decomposed
`varFromOffset α offset` into a literal): cell `j` of the environment is cell `j` of `w`'s
flattening. Fold the literal back with `change ProvableStruct.eval env
(ProvableStruct.varFromOffset α offset) = _ at h` (definitional) and apply. -/
theorem get_of_eval_varFromOffset_eq {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (offset : ℕ) (w : α F)
    (h : ProvableStruct.eval env (ProvableStruct.varFromOffset α offset) = w)
    (j : ℕ) (hj : j < size α) : env.get (offset + j) = (toElements w)[j] := by
  subst h
  rw [← ProvableStruct.eval_eq_eval, ← ProvableStruct.varFromOffset_eq_varFromOffset,
    ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]

end ProvableStruct

open Lean Elab Command Meta

namespace ProvableStruct

/-- `provable_struct_eval_lemmas S` declares `S.eval_<field> : (ProvableStruct.eval env s).<field> =
Eval.eval env s.<field>` (tagged `circuit_norm`) for every field of the structure `S`. -/
elab "provable_struct_eval_lemmas " id:ident : command => do
  let structName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let some info := getStructureInfo? env structName
    | throwErrorAt id "`{structName}` is not a structure"
  let some (.inductInfo indInfo) := env.find? structName
    | throwErrorAt id "`{structName}` is not an inductive type"
  unless indInfo.numParams == 1 do
    throwErrorAt id "`{structName}` must have exactly one parameter `(F : Type)`"
  let structIdent := mkIdent structName
  for field in info.fieldNames do
    -- `_root_`: the generated name is absolute, whatever namespace the command sits in.
    let lemmaIdent := mkIdent (`_root_ ++ structName ++ Name.mkSimple s!"eval_{field}")
    let fieldIdent := mkIdent field
    -- A `Vector F n` field keeps Clean's lifted normal form (`(ProvableStruct.eval env s).c[i]`,
    -- which Clean's indexing simproc does produce), so its lemma is not a `circuit_norm` member:
    -- tagging it would loop against that simproc through `eval_fields`/`getElem_map`.
    let some projFn := getProjFnForField? env structName field
      | throwErrorAt id "no projection function for field `{field}` of `{structName}`"
    -- 0 = scalar (`F`); 1 = `Vector F n` (`Word F`, `fields n F` included); 3 = a vector of
    -- something else (a `ProvableVector`); 2 = a nested struct or anything else.
    let kind : Nat ← liftTermElabM do
      forallTelescopeReducing (← getConstInfo projFn).type fun xs body => do
        if body == xs[0]! then pure 0
        else
          let body' ← whnfD body
          if body'.isAppOfArity ``Vector 2 then
            pure (if body'.getAppArgs[0]! == xs[0]! then 1 else 3)
          else pure 2
    -- Proof: on the constructor literal `cases s` exposes, `ProvableStruct.eval` reduces
    -- definitionally (`toComponents` / `eval.go` / `fromComponents` all compute), so the
    -- projection is `rfl`. A `simp only [circuit_norm]` here normalises the WHOLE struct's
    -- evaluation before projecting — quadratic in the field count (45-field `DivRemChip.Columns`:
    -- 27 s of `simp` for its 45 lemmas, 5 s with `rfl`; measured 2026-09-22).
    let cmd ← if kind == 1 || kind == 3 then `(
      theorem $lemmaIdent:ident {F : Type} [FiniteField F] (env : Environment F)
          (s : Var $structIdent F) :
          (ProvableStruct.eval env s).$fieldIdent:ident = Eval.eval env s.$fieldIdent:ident := by
        cases s
        rfl)
    else `(
      @[circuit_norm]
      theorem $lemmaIdent:ident {F : Type} [FiniteField F] (env : Environment F)
          (s : Var $structIdent F) :
          (ProvableStruct.eval env s).$fieldIdent:ident = Eval.eval env s.$fieldIdent:ident := by
        cases s
        rfl)
    elabCommand cmd
    -- `S.eval_congr_f : eval env s = eval env' s → <field f of s agrees>`, stated in the field's
    -- `circuit_norm` normal form so `rw`/`exact` at a constraint-form goal need no further step.
    -- Proof: project `h`, rewrite both sides with the field's `eval_f` lemma just proved, then the
    -- one Clean lemma that puts the field's kind into that normal form — never the whole
    -- `circuit_norm` set (which re-normalises the entire struct evaluation per lemma).
    let congrIdent := mkIdent (`_root_ ++ structName ++ Name.mkSimple s!"eval_congr_{field}")
    let congrCmd ← match kind with
      | 0 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Expression.eval env s.$fieldIdent:ident = Expression.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident, ProvableType.eval_field,
            ProvableType.eval_field] at this
          exact this)
      | 1 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Vector.map (Expression.eval env) s.$fieldIdent:ident
              = Vector.map (Expression.eval env') s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident, ProvableType.eval_fields,
            ProvableType.eval_fields] at this
          exact this)
      | 2 => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            ProvableStruct.eval env s.$fieldIdent:ident
              = ProvableStruct.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident, ProvableStruct.eval_eq_eval,
            ProvableStruct.eval_eq_eval] at this
          exact this)
      | _ => `(
        theorem $congrIdent:ident {F : Type} [FiniteField F] {env env' : Environment F}
            {s : Var $structIdent F}
            (h : ProvableStruct.eval env s = ProvableStruct.eval env' s) :
            Eval.eval env s.$fieldIdent:ident = Eval.eval env' s.$fieldIdent:ident := by
          have := congrArg (fun r => r.$fieldIdent:ident) h
          rw [$lemmaIdent:ident, $lemmaIdent:ident] at this
          exact this)
    elabCommand congrCmd

end ProvableStruct
