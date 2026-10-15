import SP1Clean.Model.Core.ExecutionReplay

/-! # Canonical HALT on the complete machine state

HALT observes actual x5/x10/x11, checks the canonical exit range, parks PC, and records the exit
in the evolving host. Writing the zero syscall result back to an already-zero x5 is proved to
preserve the literal Sail register map, not merely its integer-register observations.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Soundness.Target SP1Clean.Machine LeanRV64D LeanRV64D.Defs

/-- The exact effect produced by a permitted HALT call. -/
def HostState.haltExecution (host : HostState) (exit arg2 : BitVec 64) : HostExecution :=
  ⟨.halt, exit, arg2, 0, ⟨{ host with exitCode := some (exit.setWidth 32) }, none⟩⟩

/-- Actual observations and the exit range determine HALT's complete host effect. -/
theorem HostState.run_halt (host : HostState) (policy : HostPolicy) (context : HostReadContext)
    (exit arg2 : BitVec 64) (running : host.exitCode = none)
    (code : context.register 5 = some 0) (a0 : context.register 10 = some exit)
    (a1 : context.register 11 = some arg2)
    (bounds : exit.toNat < policy.characteristic ∧ exit.toNat < 2 ^ 32) :
    host.run policy context = some (host.haltExecution exit arg2) := by
  apply (host.run_eq_some_iff policy context _).mpr
  refine ⟨running, code, a0, a1, rfl, ?_⟩
  simp only [haltExecution, executeKind, bounds, and_self, ↓reduceIte]

/-- HALT's return-register write preserves the entire register map because x5 is already zero. -/
theorem HostState.haltExecution_apply (host : HostState) (source : SailState)
    (pc exit arg2 : BitVec 64) (code : source.get_reg? 5 = some 0) :
    (host.haltExecution exit arg2).apply source pc =
      { source with regs := source.regs.insert Register.PC haltPc } := by
  have same : source.regs.insert Register.x5 0 = source.regs := by
    apply Std.ExtDHashMap.ext_get?
    intro register
    by_cases equal : register = Register.x5
    · subst register
      rw [Std.ExtDHashMap.get?_insert_self]
      exact code.symm
    · simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, Ne.symm equal, ↓reduceDIte]
  simp only [haltExecution, HostExecution.apply, HostExecution.nextPc, ↓reduceIte,
    HostEffect.applyMemory, same]

/-- A permitted HALT is a real stateful execution step with every untouched field retained. -/
theorem ExecutionStep.halt {policy : HostPolicy} {program : GuestProgram}
    (source : ExecutionState) (pc exit arg2 : BitVec 64)
    (running : source.host.exitCode = none) (atPc : source.sail.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some ECALL_ENC)
    (loaded : InstructionBytes.check source.sail.mem.get? pc ECALL_ENC = true)
    (code : source.sail.get_reg? 5 = some 0) (a0 : source.sail.get_reg? 10 = some exit)
    (a1 : source.sail.get_reg? 11 = some arg2)
    (bounds : exit.toNat < policy.characteristic ∧ exit.toNat < 2 ^ 32) :
    ExecutionStep policy program source
      (.syscall ((source.host.haltExecution exit arg2).toEvent source.clock pc))
      ⟨{ source.sail with regs := source.sail.regs.insert Register.PC haltPc },
        { source.host with exitCode := some (exit.setWidth 32) }, source.clock + syscallSchedule.duration⟩ := by
  have step := HostState.step_of_run atPc fetched loaded
    (source.host.run_halt policy (.ofSail source.sail) exit arg2 running code a0 a1 bounds) source.clock
  rw [source.host.haltExecution_apply source.sail pc exit arg2 code] at step
  exact .syscall step

end SP1Clean.Model.Core
