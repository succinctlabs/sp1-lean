import Lean
import LeanRV64IM.Specialization

open Lean

section extract_from_and

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

end extract_from_and


section simpM

open Sail

/-- Simplify monadic operations. Use `simpM +run` to also simplify `XMonad.run`. -/
syntax "simpM" "+run" : tactic

macro "simpM" : tactic => 
  `(tactic| simp [bind, StateT.bind, ExceptT.bind, EStateM.bind, ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, Functor.map, StateT.map, ExceptT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift, ExceptT.mk])

macro "simpM" "+run" : tactic => 
  `(tactic| simp [bind, StateT.bind, ExceptT.bind, EStateM.bind, ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, Functor.map, StateT.map, ExceptT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift, ExceptT.mk, StateT.run, ExceptT.run, EStateM.run, SailME.run])

end simpM
