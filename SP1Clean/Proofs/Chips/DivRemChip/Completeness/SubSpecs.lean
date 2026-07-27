import SP1Clean.Proofs.Operations.MulOperation.Formal
import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal
import Batteries.Data.Vector.Lemmas

/-! # `DivRemChip` — sub-circuit `Spec` completeness helpers (factored for parallel compilation)

The chip's `completeness` discharges, among its 62 constraint conjuncts, seven sub-circuit-`Spec`
obligations: two `MulOperation` (`c_times_quotient_{lower,upper}`), four `IsEqualWordOperation`
(`is_overflow_{b,c}` full-word + low-half), and one `IsZeroWordOperation` (`is_c_0`). In each the
goal is `<SubOp>.Spec ⟨…, <witnessed cols block>, …⟩` where the `cols` field is the giant
`Eval.eval env (ProvableStruct.varFromOffset <SubOpCols> off)` column block; the matching `spec_*`
lemma proves the `Spec` at the *populate value* of those columns.

These helpers do exactly the cols-block → populate bridge, stated env-parametrically over an
**abstract** `cols` struct (so the helper carries no giant term and type-checks in its own file off
the 256M-heartbeat `completeness` theorem — mirroring `ownAsserts_complete`). The `completeness`
glue supplies the two pins (`hcell` from `getElem_toElements_eval_varFromOffset`, `hpop` from the
witness-hint `h_env_*`) and the chosen `spec_*` lemma (`hSpec`); the helper rewrites `cols` to the
populate value and discharges by `hSpec`. This replaces the old slow `convert <SubOp>.spec_* using 2`
(a large failed `isDefEq` over the witnessed cols block, ×17, gated behind `stop`/`sorry`). -/

namespace SP1Clean.DivRemChip.SubSpecs

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

lemma eqWord_size_eq : size (Extracted.IsEqualWordOperation) = 11 := rfl

def eqWordWitnessElements (wit : Extracted.IsEqualWordOperation (ZMod p)) :
    Vector (ZMod p) 11 :=
  Vector.cast eqWord_size_eq (ProvableType.toElements wit)

set_option linter.unusedSectionVars false in
lemma eqWordWitnessElements_eq (wit : Extracted.IsEqualWordOperation (ZMod p)) :
    eqWordWitnessElements wit = Vector.cast eqWord_size_eq (ProvableType.toElements wit) := rfl

set_option linter.unusedSectionVars false in
lemma eqWordWitnessElements_get (wit : Extracted.IsEqualWordOperation (ZMod p)) (i : Fin 11) :
    (eqWordWitnessElements wit).get i =
      (ProvableType.toElements wit)[i.val]'(by
        simpa only [eqWord_size_eq] using i.isLt) := by
  rw [eqWordWitnessElements_eq, Vector.get_cast]
  rfl

/-- The generated `IsZeroWordOperation` witness block has eleven cells.  Keeping this equality
opaque prevents parent proofs from reducing the nested operation's full `ProvableType` merely to
type-check an index into the explicitly cast witness vector. -/
lemma isZero_size_eq : size (Extracted.IsZeroWordOperation) = 11 := rfl

/-- The eleven flattened `IsZeroWordOperation` cells, sealed behind a small definition so a parent
proof can mention the witness vector without reducing the nested column structure in a hypothesis
type. -/
def isZeroWitnessElements (wit : Extracted.IsZeroWordOperation (ZMod p)) : Vector (ZMod p) 11 :=
  Vector.cast isZero_size_eq (ProvableType.toElements wit)

set_option linter.unusedSectionVars false in
lemma isZeroWitnessElements_eq (wit : Extracted.IsZeroWordOperation (ZMod p)) :
    isZeroWitnessElements wit = Vector.cast isZero_size_eq (ProvableType.toElements wit) := rfl

set_option linter.unusedSectionVars false in
lemma isZeroWitnessElements_get (wit : Extracted.IsZeroWordOperation (ZMod p)) (i : Fin 11) :
    (isZeroWitnessElements wit).get i =
      (ProvableType.toElements wit)[i.val]'(by
        simpa only [isZero_size_eq] using i.isLt) := by
  rw [isZeroWitnessElements_eq, Vector.get_cast]
  rfl

set_option linter.unusedSectionVars false in
/-- The generated `MulOperation` component spelling, exposed as a syntactic rewrite. -/
lemma mul_toComponents (cols : Extracted.MulOperation (ZMod p)) :
    toComponents cols =
      (.cons cols.carry <| .cons cols.product <| .cons cols.b_lower_byte <|
        .cons cols.c_lower_byte <| .cons cols.b_msb <| .cons cols.c_msb <|
        .cons cols.product_msb <| .cons cols.b_sign_extend <|
        .cons cols.c_sign_extend .nil) := by
  rcases cols with ⟨carry, product, bLower, cLower, bMsb, cMsb, productMsb, bSign, cSign⟩
  rfl

lemma mul_size_eq : size (Extracted.MulOperation) = 45 := rfl

lemma mul_combinedSize_eq :
    ProvableStruct.combinedSize' (components Extracted.MulOperation) = 45 := rfl

/-- The derived component flattener, with its length sealed at forty-five cells. -/
def mulWitnessElements (cols : Extracted.MulOperation (ZMod p)) : Vector (ZMod p) 45 :=
  Vector.cast mul_combinedSize_eq
    (ProvableStruct.componentsToElements (components Extracted.MulOperation) (toComponents cols))

set_option linter.unusedSectionVars false in
lemma mulWitnessElements_eq (cols : Extracted.MulOperation (ZMod p)) :
    mulWitnessElements cols = Vector.cast mul_size_eq (ProvableType.toElements cols) := rfl

set_option linter.unusedSectionVars false in
lemma mulWitnessElements_get (cols : Extracted.MulOperation (ZMod p)) (i : Fin 45) :
    (mulWitnessElements cols).get i =
      (ProvableType.toElements cols)[i.val]'(by
        simpa only [mul_size_eq] using i.isLt) := by
  rw [mulWitnessElements_eq, Vector.get_cast]
  rfl

/-- The thirteen cells following `carry` and `product`.  Their internal layout is irrelevant to
the DivRem parent proof, so it stays folded behind this definition. -/
def mulTailElements (cols : Extracted.MulOperation (ZMod p)) : Vector (ZMod p) 13 :=
  ProvableType.toElements cols.b_lower_byte ++
    (ProvableType.toElements cols.c_lower_byte ++
      (#v[cols.b_msb] ++ (#v[cols.c_msb] ++
        (ProvableType.toElements cols.product_msb ++
          (#v[cols.b_sign_extend] ++
            (#v[cols.c_sign_extend] ++ (#v[] : Vector (ZMod p) 0)))))))

/-- A deliberately shallow spelling of the generated Mul witness layout. -/
def mulFlatElements (cols : Extracted.MulOperation (ZMod p)) : Vector (ZMod p) 45 :=
  cols.carry ++ (cols.product ++ mulTailElements cols)

set_option linter.unusedSectionVars false in
lemma mulWitnessElements_eq_flat (cols : Extracted.MulOperation (ZMod p)) :
    mulWitnessElements cols = mulFlatElements cols := by
  simp only [mulWitnessElements, mulFlatElements, mulTailElements, mul_toComponents,
    circuit_norm, explicit_provable_type, ProvableStruct.componentsToElements, Vector.cast_rfl]
  rfl

private lemma append16_get_right {α : Type} (xs : Vector α 16) (ys : Vector α 29)
    (i : Fin 16) : (xs ++ ys)[16 + i.val] = ys[i.val] := by
  simpa only [Nat.add_comm] using
    (Vector.getElem_append_right' xs (i := i.val) (by omega)).symm

private lemma append16_get_left {α : Type} (xs : Vector α 16) (ys : Vector α 13)
    (i : Fin 16) : (xs ++ ys)[i.val] = xs[i.val] :=
  Vector.getElem_append_left i.isLt

/-- Product cell `i` occupies flattened witness cell `16 + i`. -/
lemma mulProduct_witnessElements (cols : Extracted.MulOperation (ZMod p)) (i : Fin 16) :
    (mulWitnessElements cols)[16 + i.val] = cols.product[i.val] := by
  rw [mulWitnessElements_eq_flat]
  exact append16_get_right cols.carry (cols.product ++ mulTailElements cols) i |>.trans
    (append16_get_left cols.product (mulTailElements cols) i)

set_option linter.unusedSectionVars false in
/-- Project all sixteen product cells from a complete forty-five-cell witness pin.  The proof is
kept abstract in this small module so a parent chip never elaborates `Eq.trans` over a concrete,
large Mul populate term. -/
lemma mulProduct_pins (get : ℕ → ZMod p) (off : ℕ)
    (cols : Extracted.MulOperation (ZMod p))
    (h : ∀ i : Fin 45, get (off + i.val) = (mulWitnessElements cols).get i) :
    ∀ i : Fin 16, get (off + 16 + i.val) = cols.product[i.val] := by
  intro i
  have hi := (h ⟨16 + i.val, by omega⟩).trans (mulProduct_witnessElements cols i)
  simpa only [Nat.add_assoc] using hi

set_option linter.unusedSectionVars false in
/-- A witnessed column struct equals a `populate` value when, cell by cell, the struct's
`toElements` reads back the env value `env.get (off + i)` (`hcell`) and that env value is the
`populate` struct's `i`-th element (`hpop`). The `ext_iff` reduction shared by all sub-circuit
cols bridges; `hpop` is exactly the chip's `h_env_*` witness pin. -/
lemma cols_eq_of_pins {α : TypeMap} [ProvableType α]
    (env : Environment (ZMod p)) (off : ℕ) (cols wit : α (ZMod p))
    (hcell : ∀ i (hi : i < size α), (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin (size α), env.get (off + ↑i) = (ProvableType.toElements wit)[↑i]) :
    cols = wit :=
  (ProvableType.ext_iff cols wit).mpr fun i hi => (hcell i hi).trans (hpop ⟨i, hi⟩)

set_option linter.unusedSectionVars false in
/-- Equality form of the `IsEqualWordOperation` witness bridge. This is the reusable core of
`subSpec_eqWord`: a complete eleven-cell pin identifies the nested column struct independently of
which semantic contract consumes it. -/
theorem eqWord_cols_eq_of_pins (env : Environment (ZMod p)) (off : ℕ)
    (cols wit : Extracted.IsEqualWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsEqualWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (eqWordWitnessElements wit).get i) :
    cols = wit := by
  apply cols_eq_of_pins env off cols wit hcell
  intro i
  have hi : i.val < 11 := by simpa only [circuit_norm] using i.isLt
  have h := hpop ⟨i, hi⟩
  change env.get (off + i.val) = (eqWordWitnessElements wit).get ⟨i, hi⟩ at h
  rw [eqWordWitnessElements_eq, Vector.get_cast] at h
  exact h

set_option linter.unusedSectionVars false in
/-- Equality form of the `IsZeroWordOperation` witness bridge. -/
theorem isZero_cols_eq_of_pins (env : Environment (ZMod p)) (off : ℕ)
    (cols wit : Extracted.IsZeroWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsZeroWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (isZeroWitnessElements wit).get i) :
    cols = wit := by
  apply cols_eq_of_pins env off cols wit hcell
  intro i
  have hi : i.val < 11 := by simpa only [circuit_norm] using i.isLt
  have h := hpop ⟨i, hi⟩
  change env.get (off + i.val) = (isZeroWitnessElements wit).get ⟨i, hi⟩ at h
  rw [isZeroWitnessElements_eq, Vector.get_cast] at h
  exact h

set_option linter.unusedSectionVars false in
/-- The evaluated eleven-cell `varFromOffset` block is the pinned `IsEqualWordOperation` value.
This packages the standard `fromElements` readback spelling so large chip proofs never have to
unify a concrete nested struct against `cols_eq_of_pins`. -/
theorem eval_eqWordBlock_eq (env : Environment (ZMod p)) (off : ℕ)
    (wit : Extracted.IsEqualWordOperation (ZMod p))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (eqWordWitnessElements wit).get i) :
    (ProvableType.fromElements
      (Vector.map (fun x => Expression.eval env x)
        (Vector.mapRange 11 fun i => var { index := off + i })) :
      Extracted.IsEqualWordOperation (ZMod p)) = wit := by
  refine eqWord_cols_eq_of_pins env off _ wit ?_ hpop
  intro i hi
  simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm]

set_option linter.unusedSectionVars false in
/-- The evaluated eleven-cell `varFromOffset` block is the pinned `IsZeroWordOperation` value. -/
theorem eval_isZeroBlock_eq (env : Environment (ZMod p)) (off : ℕ)
    (wit : Extracted.IsZeroWordOperation (ZMod p))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (isZeroWitnessElements wit).get i) :
    (ProvableType.fromElements
      (Vector.map (fun x => Expression.eval env x)
        (Vector.mapRange 11 fun i => var { index := off + i })) :
      Extracted.IsZeroWordOperation (ZMod p)) = wit := by
  refine isZero_cols_eq_of_pins env off _ wit ?_ hpop
  intro i hi
  simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm]

set_option linter.unusedSectionVars false in
/-- Exact evaluator spelling of the block produced by `populatedRowAt`.  Keeping both the outer
`fromElements` and the inner `fields 11` `varFromOffset` folded avoids asking rewriting to
reconstruct either hidden eleven-cell size equality. -/
theorem eval_eqWordFieldsBlock_eq (env : Environment (ZMod p)) (off : ℕ)
    (wit : Extracted.IsEqualWordOperation (ZMod p))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (eqWordWitnessElements wit).get i) :
    Eval.eval env
      (ProvableType.fromElements
        (ProvableType.varFromOffset (F := ZMod p) (fields 11) off) :
        Extracted.IsEqualWordOperation (Expression (ZMod p))) = wit := by
  rw [ProvableType.eval_fromElements]
  refine eqWord_cols_eq_of_pins env off _ wit ?_ hpop
  intro i hi
  simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm]

set_option linter.unusedSectionVars false in
/-- Exact `IsZeroWordOperation` spelling of `eval_eqWordFieldsBlock_eq`. -/
theorem eval_isZeroFieldsBlock_eq (env : Environment (ZMod p)) (off : ℕ)
    (wit : Extracted.IsZeroWordOperation (ZMod p))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (isZeroWitnessElements wit).get i) :
    Eval.eval env
      (ProvableType.fromElements
        (ProvableType.varFromOffset (F := ZMod p) (fields 11) off) :
        Extracted.IsZeroWordOperation (Expression (ZMod p))) = wit := by
  rw [ProvableType.eval_fromElements]
  refine isZero_cols_eq_of_pins env off _ wit ?_ hpop
  intro i hi
  simp only [ProvableType.toElements_fromElements, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm]

set_option linter.unusedSectionVars false in
/-- A complete forty-five-cell pin identifies an abstract evaluated `MulOperation` block.  The
block deliberately remains an argument: putting `Eval.eval (varFromOffset MulOperation ...)` in
this theorem's type asks `whnf` to normalize the generated nested struct before the proof starts. -/
theorem mul_cols_eq_of_pins (env : Environment (ZMod p)) (off : ℕ)
    (cols wit : Extracted.MulOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.MulOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 45, env.get (off + ↑i) = (mulWitnessElements wit).get i) :
    cols = wit := by
  refine cols_eq_of_pins env off cols wit hcell ?_
  intro i
  have hi : i.val < 45 := by simpa only [circuit_norm] using i.isLt
  have h := hpop ⟨i, hi⟩
  change env.get (off + i.val) = (mulWitnessElements wit).get ⟨i, hi⟩ at h
  rw [mulWitnessElements_eq, Vector.get_cast] at h
  exact h

set_option linter.unusedSectionVars false in
/-- Discharge one `MulOperation` sub-circuit `Spec` obligation: rewrite the witnessed `cols` block
to the `populate` value `wit` (via the two pins) and apply the supplied `spec_*` proof `hSpec`. -/
theorem subSpec_mul (env : Environment (ZMod p)) (off : ℕ)
    (b c : Word (ZMod p)) (is_real is_mul is_mulh is_mulhu is_mulhsu is_mulw : ZMod p)
    (cols wit : Extracted.MulOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.MulOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 45, env.get (off + ↑i) = (mulWitnessElements wit).get i)
    (hSpec : MulOperation.Spec
      (⟨b, c, wit, is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
        : MulOperation.Inputs (ZMod p))) :
    MulOperation.Spec
      (⟨b, c, cols, is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
        : MulOperation.Inputs (ZMod p)) := by
  rw [mul_cols_eq_of_pins env off cols wit hcell hpop]
  exact hSpec

set_option linter.unusedSectionVars false in
/-- Discharge one `IsEqualWordOperation` sub-circuit `Spec` obligation. Covers all four `is_overflow`
cases (full-word `eqb`/`eqc` and low-half `eqb2`/`eqc2`); the gate/branch selection and choice of
`spec_zero`/`spec_populate`/`spec_populate_offGate` stay at the call site (they produce `hSpec`). -/
theorem subSpec_eqWord (env : Environment (ZMod p)) (off : ℕ)
    (a b : Word (ZMod p)) (is_real : ZMod p)
    (cols wit : Extracted.IsEqualWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsEqualWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (eqWordWitnessElements wit).get i)
    (hSpec : IsEqualWordOperation.Spec
      (⟨a, b, wit, is_real⟩ : IsEqualWordOperation.Inputs (ZMod p))) :
    IsEqualWordOperation.Spec
      (⟨a, b, cols, is_real⟩ : IsEqualWordOperation.Inputs (ZMod p)) := by
  have hpop' : ∀ i : Fin (size (Extracted.IsEqualWordOperation)),
      env.get (off + ↑i) = (ProvableType.toElements wit)[↑i] := by
    intro i
    have hi : i.val < 11 := by simpa only [circuit_norm] using i.isLt
    have h := hpop ⟨i, hi⟩
    change env.get (off + i.val) = (eqWordWitnessElements wit).get ⟨i, hi⟩ at h
    rw [eqWordWitnessElements_eq, Vector.get_cast] at h
    change env.get (off + i.val) = (ProvableType.toElements wit).get i
    exact h
  rw [cols_eq_of_pins env off cols wit hcell hpop']
  exact hSpec

set_option linter.unusedSectionVars false in
/-- Discharge the `is_c_0` `IsZeroWordOperation` sub-circuit `Spec` obligation. -/
theorem subSpec_isZero (env : Environment (ZMod p)) (off : ℕ)
    (a : Word (ZMod p)) (is_real : ZMod p)
    (cols wit : Extracted.IsZeroWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsZeroWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (isZeroWitnessElements wit)[↑i])
    (hSpec : IsZeroWordOperation.Spec
      (⟨a, wit, is_real⟩ : IsZeroWordOperation.Inputs (ZMod p))) :
    IsZeroWordOperation.Spec
      (⟨a, cols, is_real⟩ : IsZeroWordOperation.Inputs (ZMod p)) := by
  have hpop' : ∀ i : Fin (size (Extracted.IsZeroWordOperation)),
      env.get (off + ↑i) = (ProvableType.toElements wit)[↑i] := by
    intro i
    have hi : i.val < 11 := by simpa only [circuit_norm] using i.isLt
    have h := hpop ⟨i, hi⟩
    change env.get (off + i.val) =
      (isZeroWitnessElements wit).get ⟨i, hi⟩ at h
    rw [isZeroWitnessElements_eq] at h
    rw [Vector.get_cast] at h
    change env.get (off + i.val) = (ProvableType.toElements wit).get i
    exact h
  rw [cols_eq_of_pins env off cols wit hcell hpop']
  exact hSpec

end SP1Clean.DivRemChip.SubSpecs
