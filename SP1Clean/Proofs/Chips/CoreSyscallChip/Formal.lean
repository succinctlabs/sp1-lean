import SP1Clean.Native.Chips.CoreSyscallChip.Defs

/-! # Soundness and completeness of the native syscall instruction boundary

The resulting contract includes both the whole instruction chip's semantics and the enforced
eight-code profile. The exact Rust-faithfulness anchor stays on the original instruction circuit;
the additional native lookup is deliberately outside that claim.
-/

namespace SP1Clean.CoreSyscallChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def circuit : GeneralFormalCircuit (ZMod p) SyscallInstrsChip.Inputs unit where
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ :=
    SyscallInstrsChip.RowContract input ∧
      SyscallCodeGuard.Spec ⟨input.op_a_memory.prev_value, input.is_real⟩
  channelsWithRequirements := [Channels.memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [Spec, SyscallInstrsChip.circuit, SyscallCodeGuard.circuit]
    exact h_holds
  completeness := by
    circuit_proof_start [Spec, SyscallInstrsChip.circuit, SyscallCodeGuard.circuit]
    exact h_assumptions
  requirementsChannelsLawful := by
    preserve_tactic_target
    intro input offset
    simp [main, circuit_norm, SyscallInstrsChip.circuit, SyscallCodeGuard.circuit]

end SP1Clean.CoreSyscallChip
