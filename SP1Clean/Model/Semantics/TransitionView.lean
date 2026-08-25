import SP1Clean.Model.Semantics.InstructionPlan
import SP1Clean.Model.Semantics.TransitionDecode

/-!
# Canonical SP1 transition projection

`Machine.LocatedTransition` is the one operational transition carrier shared by soundness and
completeness. This module gives it one richer, still proof-independent SP1 projection: the
committed fetch and official decode, canonical route key and table identity, and the attempted
exact field-free access plan.

There is deliberately no soundness-side or completeness-side sibling of this structure. Native
grounding proves that the outer projection succeeds; deterministic trace compilation consumes the
result literally. The access-plan field remains optional because total RAM-cell materialization is
a compiler-domain question, not part of ordinary Sail support. Unsupported decoder-image
constructors and unsupported routes fail closed in the outer projection; missing register/RAM
values fail closed in the one inner access projection.
-/

open LeanRV64D.Defs

namespace SP1Clean.Semantics

open Sail LeanRV64D
open SP1Clean.Soundness.Target

/-- The single proof-free SP1 view of one located ordinary transition. -/
structure SP1TransitionView where
  pc : BitVec 64
  word : BitVec 32
  decoded : instruction
  routeKey : InstructionRouteKey
  chipId : InstructionChipId
  accessPlan? : Option InstructionAccessPlan

/-- Project a located transition into the exact static information shared by native soundness and
trace completeness. The official decoder is run only through `decodeLocated?`; every remaining
field is obtained from the canonical Model-layer projection for that concern. -/
noncomputable def projectSP1Transition? (program : GuestProgram)
    (located : Machine.LocatedTransition) : Option SP1TransitionView := do
  let pc ← located.source.regs.get? Register.PC
  let word ← program.fetchWord pc
  let decoded ← decodeLocated? program located
  if instructionImageOK decoded then
    let routeKey ← instructionRouteKey decoded
    let chipId ← instructionRouteId decoded
    pure
      { pc, word, decoded, routeKey, chipId
        accessPlan? := instructionAccessPlan? decoded located.source located.transition.target }
  else
    none

/-- Successful projection exposes the exact canonical computations used to construct the view. -/
theorem projectSP1Transition?_components
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) :
    located.source.regs.get? Register.PC = some view.pc ∧
      program.fetchWord view.pc = some view.word ∧
      decodeLocated? program located = some view.decoded ∧
      instructionImageOK view.decoded = true ∧
      instructionRouteKey view.decoded = some view.routeKey ∧
      instructionRouteId view.decoded = some view.chipId ∧
      instructionAccessPlan? view.decoded located.source located.transition.target =
        view.accessPlan? := by
  unfold projectSP1Transition? at projected
  cases pcEq : located.source.regs.get? Register.PC with
  | none => simp [pcEq] at projected
  | some pc =>
      simp only [pcEq, Option.bind_eq_bind, Option.bind_some] at projected
      cases fetchEq : program.fetchWord pc with
      | none => simp [fetchEq] at projected
      | some word =>
          simp only [fetchEq, Option.bind_some] at projected
          cases decodeEq : decodeLocated? program located with
          | none => simp [decodeEq] at projected
          | some decoded =>
              simp only [decodeEq, Option.bind_some] at projected
              by_cases imageEq : instructionImageOK decoded = true
              · rw [if_pos imageEq] at projected
                cases keyEq : instructionRouteKey decoded with
                | none => simp [keyEq] at projected
                | some key =>
                    simp only [keyEq, Option.bind_some] at projected
                    cases routeEq : instructionRouteId decoded with
                    | none => simp [routeEq] at projected
                    | some chipId =>
                        simp only [routeEq, Option.bind_some] at projected
                        change some
                          ({ pc := pc, word := word, decoded := decoded, routeKey := key,
                              chipId := chipId,
                              accessPlan? := instructionAccessPlan? decoded located.source
                                located.transition.target } : SP1TransitionView) =
                            some view at projected
                        injection projected with viewEq
                        subst view
                        exact ⟨rfl, fetchEq, rfl, imageEq, keyEq, routeEq, rfl⟩
              · rw [if_neg imageEq] at projected
                contradiction

theorem projectSP1Transition?_decode
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) :
    decodeLocated? program located = some view.decoded :=
  (projectSP1Transition?_components projected).2.2.1

theorem projectSP1Transition?_route
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) :
    instructionRouteId view.decoded = some view.chipId :=
  (projectSP1Transition?_components projected).2.2.2.2.2.1

theorem projectSP1Transition?_accesses
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) :
    instructionAccessPlan? view.decoded located.source located.transition.target =
      view.accessPlan? :=
  (projectSP1Transition?_components projected).2.2.2.2.2.2

/-- On an actual shared projection, access readiness is exactly the existing semantic
`InstructionPlanReady`; there is no second view-specific or completeness-only readiness
predicate. -/
theorem projectSP1Transition?_accessPlan_isSome_iff_instructionPlanReady
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    (projected : projectSP1Transition? program located = some view) :
    view.accessPlan?.isSome ↔
      InstructionPlanReady view.decoded located.source located.transition.target := by
  unfold InstructionPlanReady
  rw [projectSP1Transition?_accesses projected]
  exact Option.isSome_iff_exists

end SP1Clean.Semantics
