import SP1Clean.FormalModel.TraceGen.AluGenerator
import SP1Clean.Model.Semantics.GuestProgram

/-!
# Reading ALU steps off a Sail execution

The half of the generator that touches the machine. `AluGenerator.lean` turns steps into events and
proves them well-formed; this turns *states* into steps.

The pleasant surprise is how little it costs. An R-type row commits three register contents — the
two sources it reads and the value its destination displaces — and all three are read from the state
*before* the step, because SP1 times the `op_a` write at `+4`, after both operand reads. So no
intra-row effect reasoning is needed for the values: they are three `get_reg?`s on one state. And
because Sail registers are `BitVec 64`, the three 64-bit bounds `AluStep.WellFormed` asks for are
**structural** — `BitVec.isLt`, not an assumption about the execution.

That leaves exactly two real hypotheses, and both are stated rather than absorbed:

* the program counter stays inside SP1's 48-bit address space — supplied as an invariant `P` the
  caller must show is preserved by stepping, because it is a fact about the *program*, not about the
  ISA; and
* the decoder never routes an `x0` destination here — those rows belong to the `AluX0` chip, so this
  is a routing condition, not a restriction on what the machine can do.

**What this module does not do** is decode. `decode` is a parameter. `Model/SailDecode.lean`'s
witnesses are each for one hard-coded 32-bit word, so any *instantiation* of this walk currently
carries whatever program restriction those witnesses impose; keeping the decoder abstract here means
that restriction lands in the caller's statement, where it can be read, instead of being baked into
the generator.
-/

namespace SP1Clean.TraceGen

open SP1Clean.Semantics
open LeanRV64D.Defs
open Sail LeanRV64D LeanRV64D.Functions

/-- What a decoder must produce for a row to be routed to the two-register ALU family: the opcode
discriminant and the three register indices. -/
abbrev AluDecoded := ℕ × BitVec 5 × BitVec 5 × BitVec 5

/-- **Read one ALU step off a state.** The pc it fetches from, and the three register contents its
adapter commits — all from the pre-step register file, since the destination write lands after both
operand reads. -/
def aluStepOfState (s : SailState) (d : AluDecoded) : Option AluStep :=
  match s.regs.get? Register.PC, s.get_reg? d.2.2.1, s.get_reg? d.2.2.2, s.get_reg? d.2.1 with
  | some pcv, some bv, some cv, some av =>
      some
        { pc := pcv.toNat, opcode := d.1, a := d.2.1, b := d.2.2.1, c := d.2.2.2,
          bVal := bv.toNat, cVal := cv.toNat, prevAVal := av.toNat }
  | _, _, _, _ => none

/-- **A read step is well-formed.** The three value bounds are structural — Sail registers are
`BitVec 64`. Only the pc bound and the `rd ≠ x0` routing condition are real. -/
theorem aluStepOfState_wellFormed {s : SailState} {d : AluDecoded} {step : AluStep}
    (hread : aluStepOfState s d = some step)
    (hpc : ∀ v, s.regs.get? Register.PC = some v → v.toNat < 2 ^ 48)
    (hrd : d.2.1 ≠ 0) : step.WellFormed := by
  unfold aluStepOfState at hread
  split at hread
  · rename_i pcv bv cv av hpcv _ _ _
    cases hread
    exact
      { pc_lt := hpc pcv hpcv
        a_ne_zero := hrd
        bVal_lt := bv.isLt
        cVal_lt := cv.isLt
        prevAVal_lt := av.isLt }
  · exact absurd hread (by simp)

/-- **The read succeeds exactly when the registers are there.** A guard against the degenerate
reading of `aluStepOfState_wellFormed`, which says nothing about steps that are never produced:
this says the `none` case is genuinely about absent registers and not about some hidden condition
that is never met. -/
theorem aluStepOfState_isSome {s : SailState} {d : AluDecoded}
    (hpc : (s.regs.get? Register.PC).isSome) (hb : (s.get_reg? d.2.2.1).isSome)
    (hc : (s.get_reg? d.2.2.2).isSome) (ha : (s.get_reg? d.2.1).isSome) :
    (aluStepOfState s d).isSome := by
  unfold aluStepOfState
  rcases hpcv : s.regs.get? Register.PC with _ | pcv
  · rw [hpcv] at hpc; simp at hpc
  rcases hbv : s.get_reg? d.2.2.1 with _ | bv
  · rw [hbv] at hb; simp at hb
  rcases hcv : s.get_reg? d.2.2.2 with _ | cv
  · rw [hcv] at hc; simp at hc
  rcases hav : s.get_reg? d.2.1 with _ | av
  · rw [hav] at ha; simp at ha
  simp

/-- `x0` always reads — `get_reg?` answers `0` for index zero without consulting the register map.
So a row whose sources are both `x0` reads as soon as its destination and the pc do. -/
theorem get_reg?_zero (s : SailState) : s.get_reg? 0 = some 0 := by
  simp [SailState.get_reg?]

/-! ## The walk

Forward from a state, one instruction per step, stopping at the first state the decoder declines or
the machine cannot step. Stopping early is the right behaviour rather than a failure mode: a shard
is a *prefix* of an execution, and a decoder that declines is exactly the signal that the next
instruction belongs to another chip family. -/

/-- The ALU steps of at most `n` instructions from `s`. -/
noncomputable def aluStepsFrom (decode : SailState → Option AluDecoded) :
    SailState → ℕ → List AluStep
  | _, 0 => []
  | s, n + 1 =>
      match decode s with
      | none => []
      | some d =>
        match aluStepOfState s d with
        | none => []
        | some step =>
          match Machine.stepOnce s with
          | none => [step]
          | some s' => step :: aluStepsFrom decode s' n

/-- **Every step the walk reads is well-formed**, given an invariant carrying the address-space
bound and a decoder that routes no `x0` destination here. -/
theorem aluStepsFrom_wellFormed {decode : SailState → Option AluDecoded} {P : SailState → Prop}
    (hpc : ∀ s, P s → ∀ v, s.regs.get? Register.PC = some v → v.toNat < 2 ^ 48)
    (hpres : ∀ s s', P s → Machine.stepOnce s = some s' → P s')
    (hrd : ∀ s d, decode s = some d → d.2.1 ≠ 0) :
    ∀ (n : ℕ) (s : SailState), P s → ∀ step ∈ aluStepsFrom decode s n, step.WellFormed := by
  intro n
  induction n with
  | zero => intro s _ step hstep; simp [aluStepsFrom] at hstep
  | succ n ih =>
      intro s hP step hstep
      rw [aluStepsFrom] at hstep
      split at hstep
      · simp at hstep
      · rename_i d hd
        split at hstep
        · simp at hstep
        · rename_i read hread
          split at hstep
          · rw [List.mem_singleton] at hstep
            subst hstep
            exact aluStepOfState_wellFormed hread (hpc s hP) (hrd s d hd)
          · rename_i s' hs'
            rw [List.mem_cons] at hstep
            rcases hstep with rfl | hstep
            · exact aluStepOfState_wellFormed hread (hpc s hP) (hrd s d hd)
            · exact ih s' (hpres s s' hP hs') step hstep


/-- **The walk is bounded by the run.** At most one ALU row per instruction, which is the fact a
shard-size argument needs — and the reason a shard is a prefix rather than a whole execution. -/
theorem aluStepsFrom_length_le (decode : SailState → Option AluDecoded) :
    ∀ (n : ℕ) (s : SailState), (aluStepsFrom decode s n).length ≤ n := by
  intro n
  induction n with
  | zero => intro s; simp [aluStepsFrom]
  | succ n ih =>
      intro s
      rw [aluStepsFrom]
      split
      · simp
      · split
        · simp
        · split
          · simp
          · rename_i s' _
            simpa using Nat.succ_le_succ (ih s')

end SP1Clean.TraceGen
