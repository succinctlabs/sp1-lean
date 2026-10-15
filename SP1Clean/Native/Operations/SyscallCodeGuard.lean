import SP1Clean.FormalModel.Contracts.CoreSyscall
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics

/-! # A sound and complete fixed lookup of the native syscall profile

The gate is boolean. Multiplying all four code limbs by it makes padding query canonical HALT,
while active rows query their actual full register. No auxiliary columns or channel assumptions
are needed, and the fixed table has a canonical finite export realization.
-/

namespace SP1Clean.SyscallCodeGuard

open Circuit Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.is_real * (input.is_real - 1))
  lookup SyscallKind.fixedTable.toTable (input.code.map (input.is_real * ·))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := []

omit [Fact (2 ^ 17 < p)] in
@[local circuit_norm] private theorem eval_masked (env : Environment (ZMod p))
    (gate : Expression (ZMod p)) (code : Word (Expression (ZMod p))) :
    (code.map (gate * ·)).map (Expression.eval env) =
      (code.map (Expression.eval env)).map (Expression.eval env gate * ·) := by
  simp only [Vector.map_map, Function.comp_def]
  rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main (fun _ => True) Spec := by
  circuit_proof_start [Spec, Lookup.Soundness, Table.toRaw]
  obtain ⟨binary, member⟩ := h_holds
  refine ⟨?_, ?_⟩
  · simpa only [mul_eq_zero, sub_eq_zero] using binary
  · intro real
    simpa only [real, one_mul, Vector.map_id'] using (SyscallKind.fixedTable_spec _).mp member

theorem completeness : FormalAssertion.Completeness (ZMod p) main (fun _ => True) Spec := by
  circuit_proof_start [Spec, Lookup.Completeness, Table.toRaw]
  obtain ⟨binary, valid⟩ := h_spec
  rcases binary with zero | one
  · have halt_zero : SyscallKind.encode (p := p) .halt = Vector.replicate 4 0 := by
      simp [SyscallKind.encode, SyscallKind.code, Soundness.Target.bitVecToWord]
      rfl
    simpa only [zero, zero_mul, Vector.map_const', halt_zero]
      using And.intro (mul_zero (0 : ZMod p)) (SyscallKind.encode_spec (p := p) .halt)
  · simpa only [one, sub_self, mul_zero, one_mul, Vector.map_id', true_and]
      using (SyscallKind.fixedTable_spec _).mpr (valid one)

def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated, Assumptions := fun _ => True, Spec, soundness, completeness }

end SP1Clean.SyscallCodeGuard
