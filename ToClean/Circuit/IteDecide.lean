module

public meta import Clean.Circuit.Basic

/-! # `if decide p = true` under a stale `Decidable` instance

## Gap against upstream

`circuit_norm` carries `decide_eq_true_eq` so that witness-IR `BExpr` conditions — which surface as
`decide p = true` through the `Bool → Prop` coercion in `Witgen.FExpr.eval`'s `.ite` clause — reach
proofs as the plain proposition, `if p then … else …`. That rewrite goes through `simp`'s `ite`
congruence, which re-synthesises the `Decidable` instance for the new condition and needs the old
instance's type to match the old condition at reducible transparency. When the `.ite` clause is
reached by definitional unfolding instead (`BExpr.eval`'s equations are `rfl`-lemmas, applied without
congruence), the `ite` keeps an instance typed at the *unreduced* `BExpr.eval … = true` while its
condition already reads `decide p = true`; on Lean v4.33.1 the congruence check then fails and
`decide_eq_true_eq` silently does not fire, leaving goals of the shape
`(if p then a else b) = if decide p = true then a else b` (observed across the SP1 `Populate`
congruence lemmas after the v4.32.2 → v4.33.1 bump; the same sources normalised on v4.32.2).

`iteDecideEqTrue` closes the gap as a simproc: it rewrites `@ite α (decide p = true) inst a b` to
`@ite α p i a b`, with `i` the canonical `Decidable p` instance, by an explicit `if_congr` proof — type-correct at default transparency however the stale instance was spelled. Destined for
`Clean/Circuit/WitnessIR.lean`, beside the `decide_eq_true_eq` attribute it subsumes. -/

public meta section

open Lean Meta Simp in
/-- `@ite α (decide p = true) inst a b ↦ @ite α p i a b`, for any `inst` (including one whose type
only unfolds to `Decidable (decide p = true)` at default transparency), where `i : Decidable p` is
the canonical instance (the one carried by the `decide` if none can be synthesised). -/
simproc [circuit_norm] iteDecideEqTrue (@ite _ (decide _ = true) _ _ _) := fun e => do
  let_expr ite α c inst t el := e | return .continue
  let_expr Eq _ d tru := c | return .continue
  unless tru.isConstOf ``Bool.true do return .continue
  let_expr decide p i := d | return .continue
  let .const _ [u] := e.getAppFn | return .continue
  -- the canonical instance for `p` (what `simp`'s own `ite` congruence would synthesise), falling
  -- back to the one inside the `decide`; using the canonical one lets `eq_self` close goals whose
  -- other side already carries it
  let i' := (← synthInstance? (mkApp (mkConst ``Decidable) p)).getD i
  let e' := mkApp5 (mkConst ``ite [u]) α p i' t el
  let hc := mkApp2 (mkConst ``decide_eq_true_iff) p i
  let proof := mkAppN (mkConst ``if_congr [u])
    #[α, c, p, inst, i', t, el, t, el, hc, ← mkEqRefl t, ← mkEqRefl el]
  return .visit { expr := e', proof? := some proof }
