import Lean
import LeanRV64IM.Specialization

open Lean

/-- Recursively extract a goal from nested conjunctions in the context.
    Splits ANDs and tries exact on each branch, recursing if needed. -/
syntax "extract_from_and" ident : tactic

macro_rules
| `(tactic| extract_from_and $h:ident) => `(tactic|
  first
  | exact $h
  | (obtain ⟨h_left, h_right⟩ := $h
     first
     | exact h_left
     | exact h_right
     | extract_from_and h_left
     | extract_from_and h_right)
)

open Elab Parser Tactic in
/--
  `bv_amicus_kerneli` is kernel-friendly normalisation of `w`-wide `BitVec`s.

  - `bv_amicus_kerneli at loc` targets a particular hypothesis / conclusion
  - `bv_amicus_kerneli w <k>` specifies the width explicitly (default := 64)
-/
syntax "bv_amicus_kerneli" (ppSpace &"w" ws num)? ppSpace (location)? : tactic

macro_rules
  | `(tactic| bv_amicus_kerneli $(l)?) =>
    `(tactic| (
                -- Equational statements.
                repeat first | rewrite [@BitVec.toFin_mul 64] $(l)?
                             | rewrite [@BitVec.toFin_umod 64] $(l)?
                             | rewrite [@BitVec.toFin_sub 64] $(l)?
                             | rewrite [@BitVec.add_ofFin 64] $(l)?
                             | rewrite [@BitVec.toFin_ofNat 64] $(l)?
                             | rewrite [@BitVec.toNat_ofFin 64] $(l)?
                             | rewrite [@BitVec.ofNat_eq_ofNat 64] $(l)?
                             | rewrite [@BitVec.toNat_add 64] $(l)?
                             | rewrite [@BitVec.toNat_sub 64] $(l)?
                             | rewrite [@BitVec.toNat_mul 64] $(l)?
                             | rewrite [@BitVec.toNat_umod 64] $(l)?
                -- Definitional reduction (last resort). NOTE: Could be a separate second phase maybe.
                -- Do not constrain these to a particular size.
                             | rewrite [BitVec.mul_def] $(l)?
                             | rewrite [BitVec.umod_def] $(l)?
              ))
  | `(tactic| bv_amicus_kerneli w $n $(l)?) =>
    `(tactic| (
                -- Equational statements.
                repeat first | rewrite [@BitVec.toFin_mul $n] $(l)?
                             | rewrite [@BitVec.toFin_umod $n] $(l)?
                             | rewrite [@BitVec.toFin_sub $n] $(l)?
                             | rewrite [@BitVec.add_ofFin $n] $(l)?
                             | rewrite [@BitVec.toFin_ofNat $n] $(l)?
                             | rewrite [@BitVec.toNat_ofFin $n] $(l)?
                             | rewrite [@BitVec.ofNat_eq_ofNat $n] $(l)?
                             | rewrite [@BitVec.toNat_add $n] $(l)?
                             | rewrite [@BitVec.toNat_sub $n] $(l)?
                             | rewrite [@BitVec.toNat_mul $n] $(l)?
                             | rewrite [@BitVec.toNat_umod $n] $(l)?
                -- Definitional reduction (last resort). NOTE: Could be a separate second phase maybe.
                -- Do not constrain these to a particular size.
                             | rewrite [BitVec.mul_def] $(l)?
                             | rewrite [BitVec.umod_def] $(l)?
              ))
