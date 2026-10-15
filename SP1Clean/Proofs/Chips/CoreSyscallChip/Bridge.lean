import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal
import Clean.Air.FlatComponent

/-! # Full-register syscall authentication from raw native AIR

The code guard requires no channel currency. Its conclusion can therefore be recovered before
Memory grounding, independently of the remaining host-effect obligations.
-/

namespace SP1Clean.CoreSyscallChip

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The native code check has no dependency on the instruction's channel guarantees. -/
theorem profile_of_constraints (input : Var SyscallInstrsChip.Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((main input).operations offset).ConstraintsHold env) :
    SyscallCodeGuard.Spec ⟨(eval env input).op_a_memory.prev_value, (eval env input).is_real⟩ := by
  rw [← Circuit.constraintsHold_toFlat_iff] at constraints
  simp only [main, circuit_norm] at constraints
  have guarded := (FlatOperation.constraintsHold_append.mp constraints).2
  have spec := (SyscallCodeGuard.circuit.toSubcircuit offset
    ⟨input.op_a_memory.prev_value, input.is_real⟩).soundness env (by trivial) guarded (by
      simp [FormalAssertion.toSubcircuit, SyscallCodeGuard.circuit, SyscallCodeGuard.main,
        circuit_norm, FlatOperation.interactions])
  convert spec.1 using 1
  have memoryEval (memory : Circuits.Types.RegisterAccessCols (Expression (ZMod p))) :
      (ProvableStruct.eval env memory).prev_value = memory.prev_value.map (Expression.eval env) := by
    cases memory
    simp only [circuit_norm]
  cases input
  simp only [circuit_norm, SyscallCodeGuard.circuit, memoryEval]

/-- Raw constraints authenticate the native profile even before Memory grounding. -/
theorem constraints_profile (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env) :
    SyscallCodeGuard.Spec
      ⟨(({ circuit := circuit } : Component (ZMod p)).rowInput env).op_a_memory.prev_value,
        (({ circuit := circuit } : Component (ZMod p)).rowInput env).is_real⟩ := by
  have spec := profile_of_constraints _ _ env ((Component.constraintsHold_iff env).mp constraints)
  simpa only [Component.rowInput, eval_varFromOffset_valueFromOffset] using spec

/-- The full-code guard retains the original instruction constraints at any input offset. -/
theorem main_constraints_original (input : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
      (holds : ((main input).operations offset).ConstraintsHold env) :
    ((SyscallInstrsChip.circuit.main input).operations offset).ConstraintsHold env := by
  rw [← Circuit.constraintsHold_toFlat_iff] at holds ⊢
  simp only [main, circuit_norm] at holds
  have original := (FlatOperation.constraintsHold_append.mp holds).1
  simpa only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, circuit_norm] using original

/-- Strengthening the instruction component preserves every original assertion and lookup. -/
theorem constraints_original (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env) :
    ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)).operations.ConstraintsHold env := by
  exact (Component.constraintsHold_iff env).mpr
    (main_constraints_original _ _ env ((Component.constraintsHold_iff env).mp constraints))

/-- The additional code lookup changes no channel message or multiplicity. -/
theorem interactions_original :
    ({ circuit := circuit } : Component (ZMod p)).operations.interactions =
      ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)).operations.interactions := by
  rw [Component.interactions_eq, Component.interactions_eq]
  simp only [Component.rowOperations, circuit, main, circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions, FormalAssertion.toSubcircuit_interactions,
    SyscallCodeGuard.circuit, SyscallCodeGuard.main]

theorem width_original : ({ circuit := circuit } : Component (ZMod p)).width =
    ({ circuit := SyscallInstrsChip.circuit } : Component (ZMod p)).width := rfl

end SP1Clean.CoreSyscallChip
