import Clean.Circuit.Basic
import Clean.Utils.Field
import Mathlib.Tactic.IntervalCases

/-! # `vec4_eval` — folding a length-4 `#v` of pointwise evaluations back to `Vector.map`

The constraint extractor writes a witness hint's `populate` operands as an explicit length-4 vector
literal `#v[eval e v[0], eval e v[1], eval e v[2], eval e v[3]]`, whereas `h_input` provides them in
`Vector.map (eval e) v` form. This one lemma bridges the two; it recurs across the Mul / Lt / Bitwise
/ ShiftLeft / ShiftRight chip `Formal` proofs and the DivRem completeness `Driver`, so it lives here
in `Math` rather than being re-declared per file. Generic over a prime field `ZMod p`
(`Expression.eval` needs the `Field` instance, which the primality `Fact` supplies). -/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime]

lemma vec4_eval (e : Environment (ZMod p)) (v : Vector (Expression (ZMod p)) 4) :
    (#v[Expression.eval e v[0], Expression.eval e v[1], Expression.eval e v[2],
        Expression.eval e v[3]] : Vector (ZMod p) 4) = Vector.map (Expression.eval e) v := by
  ext k hk
  interval_cases k <;> simp [Vector.getElem_map]

end SP1Clean
