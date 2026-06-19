import SP1Clean.Proofs.Operations.MulOperation.Formal
import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal

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

private instance : Fact (2 ^ 17 < p) :=
  ⟨lt_trans (by norm_num) (Fact.out (p := 2 ^ 24 < p))⟩

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
/-- Discharge one `MulOperation` sub-circuit `Spec` obligation: rewrite the witnessed `cols` block
to the `populate` value `wit` (via the two pins) and apply the supplied `spec_*` proof `hSpec`. -/
theorem subSpec_mul (env : Environment (ZMod p)) (off : ℕ)
    (b c : Word (ZMod p)) (is_real is_mul is_mulh is_mulhu is_mulhsu is_mulw : ZMod p)
    (cols wit : Extracted.MulOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.MulOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 45, env.get (off + ↑i) = (ProvableType.toElements wit)[↑i])
    (hSpec : MulOperation.Spec
      (⟨b, c, wit, is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
        : MulOperation.Inputs (ZMod p))) :
    MulOperation.Spec
      (⟨b, c, cols, is_real, is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩
        : MulOperation.Inputs (ZMod p)) := by
  rw [cols_eq_of_pins env off cols wit hcell hpop]; exact hSpec

set_option linter.unusedSectionVars false in
/-- Discharge one `IsEqualWordOperation` sub-circuit `Spec` obligation. Covers all four `is_overflow`
cases (full-word `eqb`/`eqc` and low-half `eqb2`/`eqc2`); the gate/branch selection and choice of
`spec_zero`/`spec_populate`/`spec_populate_offGate` stay at the call site (they produce `hSpec`). -/
theorem subSpec_eqWord (env : Environment (ZMod p)) (off : ℕ)
    (a b : Word (ZMod p)) (is_real : ZMod p)
    (cols wit : Extracted.IsEqualWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsEqualWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (ProvableType.toElements wit)[↑i])
    (hSpec : IsEqualWordOperation.Spec
      (⟨a, b, wit, is_real⟩ : IsEqualWordOperation.Inputs (ZMod p))) :
    IsEqualWordOperation.Spec
      (⟨a, b, cols, is_real⟩ : IsEqualWordOperation.Inputs (ZMod p)) := by
  rw [cols_eq_of_pins env off cols wit hcell hpop]; exact hSpec

set_option linter.unusedSectionVars false in
/-- Discharge the `is_c_0` `IsZeroWordOperation` sub-circuit `Spec` obligation. -/
theorem subSpec_isZero (env : Environment (ZMod p)) (off : ℕ)
    (a : Word (ZMod p)) (is_real : ZMod p)
    (cols wit : Extracted.IsZeroWordOperation (ZMod p))
    (hcell : ∀ i (hi : i < size (Extracted.IsZeroWordOperation)),
      (ProvableType.toElements cols)[i] = env.get (off + i))
    (hpop : ∀ i : Fin 11, env.get (off + ↑i) = (ProvableType.toElements wit)[↑i])
    (hSpec : IsZeroWordOperation.Spec
      (⟨a, wit, is_real⟩ : IsZeroWordOperation.Inputs (ZMod p))) :
    IsZeroWordOperation.Spec
      (⟨a, cols, is_real⟩ : IsZeroWordOperation.Inputs (ZMod p)) := by
  rw [cols_eq_of_pins env off cols wit hcell hpop]; exact hSpec

end SP1Clean.DivRemChip.SubSpecs
