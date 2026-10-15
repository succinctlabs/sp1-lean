import SP1Clean.FormalModel.Contracts.LocalCoreBoundary
import ToClean.Air.PublicVerifier

/-! # Public checks for a complete local source

The source snapshot is fixed instance data. Eight assertions check its complete execution
contract, bind the incoming PC and clock, and preserve the clock when stopped. The existing
public-verifier adapter installs these checks through sixteen fresh-channel occurrences, with
no physical table. State limb bounds and ordered Memory boundaries belong to the assembly.
-/

namespace SP1Clean.LocalSourceBoundary

open Circuit Air.Flat Model.Core Soundness

variable {p : ℕ} [Fact p.Prime]

/-- Check source validity, incoming PC and clock, and clock preservation after stopping. -/
def main (image : ProgramImage) (source : ExecutionSnapshot)
    (input : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (.const (if checkExecutionSource image source then 0 else 1))
  assertZero (input.init_clk_high - .const (source.clock / 2 ^ 24 : ℕ))
  assertZero (input.init_clk_low - .const (source.clock % 2 ^ 24 : ℕ))
  assertZero (input.init_pc0 - .const (Target.bitVecToWord source.pc)[0])
  assertZero (input.init_pc1 - .const (Target.bitVecToWord source.pc)[1])
  assertZero (input.init_pc2 - .const (Target.bitVecToWord source.pc)[2])
  let stopped : Expression (ZMod p) := .const (if source.host.exitCode = none then 0 else 1)
  assertZero (stopped * (input.final_clk_high - input.init_clk_high))
  assertZero (stopped * (input.final_clk_low - input.init_clk_low))

/-- Proved source assertions with no private cells, lookups or channel traffic. -/
def circuit (image : ProgramImage) (source : ExecutionSnapshot) :
    GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := main image source
  Spec input _ _ := Spec image source input
  ProverAssumptions input _ _ := Spec image source input
  soundness := by
    circuit_proof_start [main, Spec, SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock]
    obtain ⟨checked, hi, lo, pc0, pc1, pc2, stoppedHi, stoppedLo⟩ := h_holds
    have valid : ExecutionSourceValid image source := by
      by_cases valid : checkExecutionSource image source = true
      · exact (checkExecutionSource_iff image source).mp valid
      · simp [valid] at checked
    refine ⟨valid, ?_, ?_⟩
    · exact ⟨sub_eq_zero.mp hi, sub_eq_zero.mp lo, sub_eq_zero.mp pc0,
        sub_eq_zero.mp pc1, sub_eq_zero.mp pc2⟩
    · intro stopped
      simpa [stopped, sub_eq_zero] using And.intro stoppedHi stoppedLo
  completeness := by
    circuit_proof_start [main, Spec, SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock]
    obtain ⟨valid, binding, stopped⟩ := h_assumptions
    refine ⟨by simp [(checkExecutionSource_iff image source).mpr valid],
      sub_eq_zero.mpr binding.1, sub_eq_zero.mpr binding.2.1,
      sub_eq_zero.mpr binding.2.2.1, sub_eq_zero.mpr binding.2.2.2.1,
      sub_eq_zero.mpr binding.2.2.2.2, ?_, ?_⟩
    · by_cases running : source.host.exitCode = none
      · simp [running]
      · simp [running, (stopped running).1]
    · by_cases running : source.host.exitCode = none
      · simp [running]
      · simp [running, (stopped running).2]

/-- Reuse the generic assertion installer, including automatic channel separation. -/
def checker (image : ProgramImage) (source : ExecutionSnapshot) :
    PublicVerifier (ZMod p) SP1PublicIO where
  name := "sp1.local.source"
  circuit := circuit image source
  assumptions := by intros; trivial
  length_zero := by intros; rfl
  lookups := by intros; rfl
  interactions := by intros; rfl

/-- The existing SP1 field bound covers every physical check occurrence. -/
theorem count_bound [Fact (2 ^ 24 < p)] (image : ProgramImage) (source : ExecutionSnapshot) :
    (checker (p := p) image source).CountBound := by
  change 2 * 8 < ringChar (ZMod p) ∨ ringChar (ZMod p) = 0
  rw [ZMod.ringChar_zmod_n]
  left
  have := Fact.out (p := 2 ^ 24 < p)
  omega

/-- Raw acceptance is exactly the full semantic source contract. -/
theorem checks_iff (image : ProgramImage) (source : ExecutionSnapshot)
    (input : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    (checker image source).Checks input data ↔ Spec image source input := by
  have raw (vars : Var SP1PublicIO (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
      ((main image source vars).operations offset).ConstraintsHold env ↔
        Spec image source (eval env vars) := by
    by_cases valid : checkExecutionSource image source = true
    · by_cases running : source.host.exitCode = none
      · simp [main, circuit_norm, seval, valid, running, Spec,
          (checkExecutionSource_iff image source).mp valid,
          SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock, sub_eq_zero]
      · simp [main, circuit_norm, seval, valid, running, Spec,
          (checkExecutionSource_iff image source).mp valid,
          SP1PublicIO.SourceFor, SP1PublicIO.PreservesStoppedClock, sub_eq_zero, and_assoc]
    · have invalid := mt (checkExecutionSource_iff image source).mpr valid
      simp [main, circuit_norm, seval, valid, Spec, invalid]
  exact (raw (varFromOffset SP1PublicIO 0) (size SP1PublicIO) (Environment.fromInput input data)).trans
    (by rw [ProvableType.eval_fromInput_varFromOffset_zero])

end SP1Clean.LocalSourceBoundary
