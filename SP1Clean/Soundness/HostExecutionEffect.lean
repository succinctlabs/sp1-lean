import SP1Clean.Model.Core.ExecutionFrame

/-! # Architectural preservation by concrete host execution

The native host interpreter writes PC/x5 and its explicit byte effect. All other integer registers
and the Sail configuration survive, and the checked memory policy protects every program byte.
These compatibility statements consume the circuit-independent proofs in `Model/Core/ExecutionFrame`,
which also prove preservation for whole mixed paths.
-/

namespace SP1Clean.Soundness

open Model.Core Target LeanRV64D.Defs

/-- Concrete syscall execution authenticates architectural observations and preserves all other
registers, configuration, and protected bytes. The RAM write itself remains in the semantic step. -/
theorem hostStep_effect {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : Machine.CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall event) target) :
    event.MatchesStates source.sail target.sail ∧
      (∀ index : BitVec 5, index ≠ 5 → target.sail.get_reg? index = source.sail.get_reg? index) ∧
      (SailConfigured source.sail → SailConfigured target.sail) ∧
      (∀ address, policy.memory.readOnly address = true →
        target.sail.mem.get? address = source.sail.mem.get? address) :=
  step.syscall_sail_frame

/-- Preserving the image's protected bytes preserves the whole committed instruction memory. -/
theorem romLoaded_of_readOnly (image : ProgramImage) (valid : image.Valid) {source target : SailState}
    (preserved : ∀ address, image.readOnly address = true → target.mem.get? address = source.mem.get? address)
    (loaded : RomLoaded (image.toGuestProgram valid) source) : RomLoaded (image.toGuestProgram valid) target :=
  image.romLoaded_of_readOnly valid preserved loaded

end SP1Clean.Soundness
