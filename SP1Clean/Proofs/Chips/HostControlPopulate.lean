import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Proofs.Chips.HostEnterChip.Formal
import SP1Clean.Model.Core.HostExecutionLaws

/-! # Control-handler rows from successful host execution

The deterministic constructors take an interpreter result and event clock. For HALT and ENTER,
successful dispatch itself discharges the complete handler-domain predicates and computes the
HALT comparison columns. No row contract is supplied to these completeness adapters.
The enclosing event compiler must still match this handoff to its instruction row.
-/

namespace SP1Clean.HostControl

open SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Canonical control-call fields; neither control call uses WRITE's length register. -/
def message (clock : ℕ) (execution : HostExecution) : HostCallChip.Message (ZMod p) :=
  ⟨(clock / 2 ^ 24 : ℕ), (clock % 2 ^ 24 : ℕ), bitVecToWord execution.kind.code,
    bitVecToWord execution.arg1, bitVecToWord execution.arg2, bitVecToWord execution.result, 0⟩

theorem message_clock (clock : ℕ) (execution : HostExecution) (fits : clock < 2 ^ 48) :
    Semantics.clkNat (message (p := p) clock execution).clk_high (message clock execution).clk_low = clock := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have high : clock / 2 ^ 24 < p := by omega
  have low : clock % 2 ^ 24 < p := by omega
  simp only [message, Semantics.clkNat, ZMod.val_natCast_of_lt high, ZMod.val_natCast_of_lt low]
  omega

theorem message_values (clock : ℕ) (execution : HostExecution) :
    Word.toBitVec64 (message (p := p) clock execution).code = execution.kind.code ∧
      Word.toBitVec64 (message (p := p) clock execution).arg1 = execution.arg1 ∧
      Word.toBitVec64 (message (p := p) clock execution).arg2 = execution.arg2 ∧
      Word.toBitVec64 (message (p := p) clock execution).result = execution.result := by
  simp [message, toBitVec64_bitVecToWord]

def halt (clock : ℕ) (execution : HostExecution) : HostHaltChip.Inputs (ZMod p) :=
  HostHaltChip.populate (message clock execution)

def enter (clock : ℕ) (execution : HostExecution) : HostEnterChip.Inputs (ZMod p) := message clock execution

omit [Fact (2 ^ 25 < p)] in
private theorem encode_zero : bitVecToWord (p := p) (BitVec.ofNat 64 0) = 0 := by
  apply Vector.ext
  intro index bounded
  interval_cases index <;> simp [bitVecToWord]

/-- Successful semantic HALT execution is sufficient to construct the complete circuit witness. -/
theorem halt_assumptions_of_run (clock : ℕ) (execution : HostExecution) (kind : execution.kind = .halt)
    (host : HostState) (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) (success : host.run policy context = some execution) :
    HostHaltChip.ProverAssumptions (halt (p := p) clock execution) := by
  have facts := (host.run_eq_some_iff policy context execution).mp success
  have result : execution.result = 0 := by
    simpa [kind, HostState.result, SyscallKind.code] using facts.2.2.2.2.1
  have bounds : execution.arg1.toNat < p ∧ execution.arg1.toNat < 2 ^ 32 := by
    have effect := facts.2.2.2.2.2
    rw [kind, HostState.executeKind, characteristic] at effect
    split_ifs at effect with permitted
    exact permitted
  apply HostHaltChip.populate_assumptions
  refine ⟨?_, ?_, rfl, isU64_bitVecToWord _, ?_⟩
  · simp [message, kind, SyscallKind.code, encode_zero]
  · simp [message, result, encode_zero]
  · change Word.toNat (bitVecToWord execution.arg1) < HostHaltChip.bound p
    rw [← Word.toBitVec64_toNat (isU64_bitVecToWord _), toBitVec64_bitVecToWord]
    exact lt_min_iff.mpr bounds

omit [Fact (2 ^ 25 < p)] in
/-- ENTER needs no witness payload beyond the canonical message produced by successful dispatch. -/
theorem enter_assumptions_of_run (clock : ℕ) (execution : HostExecution)
    (kind : execution.kind = .enterUnconstrained) (host : HostState) (policy : HostPolicy)
    (context : HostReadContext) (success : host.run policy context = some execution) :
    HostEnterChip.Spec (enter (p := p) clock execution) := by
  have facts := (host.run_eq_some_iff policy context execution).mp success
  have result : execution.result = 0 := by simpa [kind, HostState.result] using facts.2.2.2.2.1
  refine ⟨?_, ?_, rfl⟩
  · simp [enter, message, kind, SyscallKind.code, bitVecToWord, HostEnterChip.codeWord]
  · simp [enter, message, result, encode_zero]

end SP1Clean.HostControl
