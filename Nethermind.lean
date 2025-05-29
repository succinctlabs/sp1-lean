import Mathlib
import Nethermind.Specs

/-!
This file is a copy of Nethermind's PoC proof
-/

namespace Sp1

def spec_ADD
  (ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 : BabyBear) : Prop :=
  (ML16 = 1) →
    spec_32_bit_wrap_add ML1 ML2 ML3 ML4 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15

set_option maxHeartbeats 5000000 in
theorem conformance_ADD {undefined : Prop}
  {ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 : BabyBear}
  (C00 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML8 < 256 ∧ ML9 < 256
          | 7 => ML8 < 256 ∧
                 (ML8 < 128 → 0 = 0) ∧
                 (128 ≤ ML8 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C01 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML10 < 256 ∧ ML11 < 256
          | 7 => ML10 < 256 ∧
                 (ML10 < 128 → 0 = 0) ∧
                 (128 ≤ ML10 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C02 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML12 < 256 ∧ ML13 < 256
          | 7 => ML12 < 256 ∧
                 (ML12 < 128 → 0 = 0) ∧
                 (128 ≤ ML12 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C03 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML14 < 256 ∧ ML15 < 256
          | 7 => ML14 < 256 ∧
                 (ML14 < 128 → 0 = 0) ∧
                 (128 ≤ ML14 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C04 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML1 < 256 ∧ ML2 < 256
          | 7 => ML1 < 256 ∧
                 (ML1 < 128 → 0 = 0) ∧
                 (128 ≤ ML1 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C05 :
    if ML16 = 0 then True else
    if ML16 = 1
    then (match 4 with
          | 4 => 0 = 0 ∧ ML3 < 256 ∧ ML4 < 256
          | 7 => ML3 < 256 ∧
                 (ML3 < 128 → 0 = 0) ∧
                 (128 ≤ ML3 → 0 = 1)
          | 8 => 0 < 65536
          | _ => undefined) ∧ 0 = 0
    else undefined)
  (C06 :
    if (ML17 * 2013265920) = 0 then True
    else if (ML17 * 2013265920) = 1 ∨ (ML17 * 2013265920) = BabyBearPrime - 1
         then ML1 < 256 ∧ ML2 < 256 ∧ ML3 < 256 ∧ ML4 < 256 ∧
              ML8 < 256 ∧ ML9 < 256 ∧ ML10 < 256 ∧ ML11 < 256 ∧
              ML12 < 256 ∧ ML13 < 256 ∧ ML14 < 256 ∧ ML15 < 256
         else undefined)
  (C07 :
    if (ML18 * 2013265920) = 0 then True
    else if (ML18 * 2013265920) = 1 ∨ (ML18 * 2013265920) = BabyBearPrime - 1
         then ML8 < 256 ∧ ML9 < 256 ∧ ML10 < 256 ∧ ML11 < 256 ∧
              ML1 < 256 ∧ ML2 < 256 ∧ ML3 < 256 ∧ ML4 < 256 ∧
              ML12 < 256 ∧ ML13 < 256 ∧ ML14 < 256 ∧ ML15 < 256
         else undefined)
  (C08 : True)
  (C09 : True)
  (C10 : True)
  (C11 : (ML17 * (ML17 - 1)) = 0)
  (C12 : (ML18 * (ML18 - 1)) = 0)
  (C13 : ((ML17 + ML18) * ((ML17 + ML18) - 1)) = 0)
  (C14 : (ML16 * (((ML8 + ML12) - ML1) * (((ML8 + ML12) - ML1) - 256))) = 0)
  (C15 : (ML16 * ((((ML9 + ML13) - ML2) + ML5) * ((((ML9 + ML13) - ML2) + ML5) - 256))) = 0)
  (C16 : (ML16 * ((((ML10 + ML14) - ML3) + ML6) * ((((ML10 + ML14) - ML3) + ML6) - 256))) = 0)
  (C17 : (ML16 * ((((ML11 + ML15) - ML4) + ML7) * ((((ML11 + ML15) - ML4) + ML7) - 256))) = 0)
  (C18 : (ML16 * (ML5 * (((ML8 + ML12) - ML1) - 256))) = 0)
  (C19 : (ML16 * (ML6 * ((((ML9 + ML13) - ML2) + ML5) - 256))) = 0)
  (C20 : (ML16 * (ML7 * ((((ML10 + ML14) - ML3) + ML6) - 256))) = 0)
  (C21 : (ML16 * ((ML5 - 1) * ((ML8 + ML12) - ML1))) = 0)
  (C22 : (ML16 * ((ML6 - 1) * (((ML9 + ML13) - ML2) + ML5))) = 0)
  (C23 : (ML16 * ((ML7 - 1) * (((ML10 + ML14) - ML3) + ML6))) = 0)
  (C24 : (ML16 * (ML5 * (ML5 - 1))) = 0)
  (C25 : (ML16 * (ML6 * (ML6 - 1))) = 0)
  (C26 : (ML16 * (ML7 * (ML7 - 1))) = 0)
  (C27 : (ML16 * (ML16 * (ML16 - 1))) = 0)
  (C28 : (ML16 * ((ML17 + ML18) - 1)) = 0) : spec_ADD ML0 ML1 ML2 ML3 ML4 ML5 ML6 ML7 ML8 ML9 ML10 ML11 ML12 ML13 ML14 ML15 ML16 ML17 ML18 := by
    -- We unfold the specification definitions and introduce the hypotheses.
    unfold spec_ADD; intro HML16; unfold spec_32_bit_wrap_add
    -- We substitute the learned equality on ML16, and simplify constraints of
    -- the form X * (X - 1) = 0 into X = 0 \/ X = 1.
    subst_eqs; simp [sub_eq_zero (b := (1 : BabyBear))] at *
    -- We perform a case analysis on the three carries (ML5/ML6/ML7).
    -- This splits the single goal into eight.
    rcases C24 <;> rcases C25 <;> rcases C26 <;>
    -- We substitute learned equalities on ML5, ML6, and ML7, and simplify the
    -- Fin-related definitions to enforce that all of the arithmetic is in Nat.
    subst_eqs <;> simp [BabyBearPrime, Fin.add_def, Fin.sub_def] at * <;>
    -- We remove Fin.val for 256 to enable reasoning with omega.
    simp only [Fin.lt_iff_val_lt_val] at * <;>
    rw [fin_val_simp (show 256 < BabyBearPrime by linarith)] at * <;>
    -- Now, the Lean omega tactic is able to discharge all of the goals.
    omega

end Sp1
