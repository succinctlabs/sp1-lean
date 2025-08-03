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

/-- Simplify monadic operations. Use `simpM +run` to also simplify `EStateM.run`. -/
syntax "simpM" "+run" : tactic

macro "simpM" : tactic => 
  `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet])

macro "simpM" "+run" : tactic => 
  `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, EStateM.run])
