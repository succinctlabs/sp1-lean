import SP1Clean.FormalModel.Contracts.SailBoundary
import ToClean.Air.PublicVerifier

/-! # Native verifier checks for the supplied Sail frame and endpoints

Snapshot data supplies a finite invariant-field check. Five field equations bind the real
public endpoint to that same target. The circuit has no witness cells. Its verifier adapter adds
twelve interactions on a fresh channel and preserves every existing channel ledger.
-/

namespace SP1Clean.SailBoundary

open Circuit Air.Flat Model.Core Soundness.Target

variable {p : ℕ} [Fact p.Prime]

/-- Validate the target frame and its canonical clock/PC in the actual verifier invocation. -/
def main (source target : ExecutionSnapshot) (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if checkStatic source target then 0 else 1))
  assertZero (input.final_clk_high - .const (target.clock / 2 ^ 24 : ℕ))
  assertZero (input.final_clk_low - .const (target.clock % 2 ^ 24 : ℕ))
  assertZero (input.final_pc0 - .const ((bitVecToWord target.pc)[0]))
  assertZero (input.final_pc1 - .const ((bitVecToWord target.pc)[1]))
  assertZero (input.final_pc2 - .const ((bitVecToWord target.pc)[2]))

/-- Proof-complete static frame and public-endpoint subcircuit. -/
def circuit (source target : ExecutionSnapshot) : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := main source target
  Spec input _ _ := Spec source target input
  ProverAssumptions input _ _ := Spec source target input
  soundness := by
    circuit_proof_start [main]
    obtain ⟨checked, high, low, pc0, pc1, pc2⟩ := h_holds
    refine ⟨?_, ⟨sub_eq_zero.mp high, sub_eq_zero.mp low⟩,
      sub_eq_zero.mp pc0, sub_eq_zero.mp pc1, sub_eq_zero.mp pc2⟩
    by_cases valid : checkStatic source target = true
    · exact valid
    · simp [valid] at checked
  completeness := by
    circuit_proof_start [main]
    obtain ⟨checked, ⟨high, low⟩, pc0, pc1, pc2⟩ := h_assumptions
    exact ⟨by simp [checked], sub_eq_zero.mpr high, sub_eq_zero.mpr low,
      sub_eq_zero.mpr pc0, sub_eq_zero.mpr pc1, sub_eq_zero.mpr pc2⟩

/-- Installable public assertions, retaining every existing physical occurrence. -/
def checker (source target : ExecutionSnapshot) : PublicVerifier (ZMod p) SP1PublicIO where
  name := "sail_boundary"
  circuit := circuit source target
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

/-- The existing SP1 field bound covers all twelve public-check occurrences. -/
theorem count_bound [Fact (2 ^ 25 < p)] (source target : ExecutionSnapshot) :
    (checker (p := p) source target).CountBound := by
  change 2 * 6 < ringChar (ZMod p) ∨ ringChar (ZMod p) = 0
  rw [ZMod.ringChar_zmod_n]
  left
  have := Fact.out (p := 2 ^ 25 < p)
  omega

/-- Raw acceptance of the added assertions is exactly the stated frame/endpoint contract. -/
theorem checks_iff (source target : ExecutionSnapshot) (input : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    (checker source target).Checks input data ↔ Spec source target input := by
  have raw (vars : Var SP1PublicIO (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
      ((main source target vars).operations offset).ConstraintsHold env ↔ Spec source target (eval env vars) := by
    by_cases valid : checkStatic source target = true <;>
      simp [main, circuit_norm, seval, valid, Spec, TargetFor, ResourceBoundary.ClockFor, sub_eq_zero, and_assoc]
  exact (raw (varFromOffset SP1PublicIO 0) (size SP1PublicIO) (Environment.fromInput input data)).trans
    (by rw [ProvableType.eval_fromInput_varFromOffset_zero])

/-- The boundary adds exactly six constant/public assertions and no auxiliary rows or cells. -/
theorem assertion_count (source target : ExecutionSnapshot) (input : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((main source target input).operations offset).constraints.length = 6 := rfl

end SP1Clean.SailBoundary
