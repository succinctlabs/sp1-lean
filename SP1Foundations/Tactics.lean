import Lean

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