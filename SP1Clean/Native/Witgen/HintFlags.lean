import Clean.Circuit.Basic

/-! # `hintFlagsIR` — the shared hint-flag accessor, as witness IR

Every hint-driven chip reads its variant flags the same way: row 0 of a string-keyed
`ProverHint` table, an absent key meaning all-zero (SP1's padding rows carry no hint). The
value-level accessors (`BitwiseChip.hintFlags`, `LtChip.hintFlags`, `MulChip.hintFlags`,
`BranchChip.hintFlags`, …) differ only in their key and width; this file is their common
witness-IR form — cell `i` is `FExpr.hintGet key n` at row 0, column `i`, whose zero default
is exactly the accessors' `.getD #v[0, …]` fallback.

`hintFlagsIR` is deliberately **not** `@[circuit_norm]` (the opacity doctrine): chips name it
in their `simp only` sets, and only the two lemmas below cross the boundary. -/

namespace SP1Clean

open Witgen

/-- The `n` variant flags of hint key `key`, as witness-IR field expressions: cell `i` reads
row 0, column `i` of the `ProverHint` table `key` (zeros when the key is absent — SP1's
padding-row convention). -/
def hintFlagsIR (F : Type) (key : String) (n : ℕ) : Vector (FExpr F) n :=
  Vector.ofFn fun i => .hintGet key n 0 i

variable {F : Type} [FiniteField F]

/-- Evaluating the flag vector reads row 0 of the hint table (elementwise `hintGet` semantics,
assembled): the chips' value-level `hintFlags env.hint` accessors are literally this right-hand
side. -/
theorem hintFlagsIR_eval (env : ProverEnvironment F) (key : String) (n : ℕ) :
    (WitgenIR.ofFExprs (hintFlagsIR F key n)).eval env
      = ((env.hint key n)[0]?).getD default := by
  apply Vector.ext
  intro i hi
  simp [hintFlagsIR, circuit_norm]

/-- Environment-locality: the flag vector reads the environment only through `hint`. This is the
whole `ComputableWitnesses` obligation for a hint-flag witness site (the fork's `AgreesBelow`
supplies the `hint` equation). -/
theorem hintFlagsIR_congr (env env' : ProverEnvironment F) (hh : env.hint = env'.hint)
    (key : String) (n : ℕ) :
    (WitgenIR.ofFExprs (hintFlagsIR F key n)).eval env
      = (WitgenIR.ofFExprs (hintFlagsIR F key n)).eval env' := by
  rw [hintFlagsIR_eval, hintFlagsIR_eval, hh]

end SP1Clean
