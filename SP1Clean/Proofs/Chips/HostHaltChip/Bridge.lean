import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Model.Core.HostExecutionLaws

/-! # HALT handlers reach the independent host interpreter

The full dispatch theorem uses authenticated x5/x10/x11 observations and an unstopped host.
The result records the canonical exit and no memory write. Every later host dispatch fails.
Matching the observations and locating the terminal instruction in the State walk are still
whole-machine responsibilities.
-/

namespace SP1Clean.HostHaltChip

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime]

def execution (input : Inputs (ZMod p)) (host : HostState) : HostExecution :=
  ⟨.halt, Word.toBitVec64 input.call.arg1, Word.toBitVec64 input.call.arg2,
    Word.toBitVec64 input.call.result,
    ⟨{ host with exitCode := some ((Word.toBitVec64 input.call.arg1).setWidth 32) }, none⟩⟩

/-- The returned exit's integer value agrees with its canonical public field encoding. -/
theorem exit_value_of_spec (input : Inputs (ZMod p)) (valid : Spec input) :
    ((Word.toNat input.call.arg1 : ℕ) : ZMod p).val =
      ((Word.toBitVec64 input.call.arg1).setWidth 32).toNat := by
  obtain ⟨_, _, _, word, below⟩ := valid
  have bounds := lt_min_iff.mp below
  rw [ZMod.val_natCast_of_lt bounds.1, BitVec.toNat_setWidth,
    Word.toBitVec64_toNat word, Nat.mod_eq_of_lt bounds.2]

theorem executeKind_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (host : HostState) (policy : HostPolicy) (characteristic : policy.characteristic = p)
    (context : HostReadContext) :
    host.executeKind policy context .halt (Word.toBitVec64 input.call.arg1)
      (Word.toBitVec64 input.call.arg2) = some (execution input host).effect := by
  obtain ⟨_, _, _, word, below⟩ := valid
  have bounds := lt_min_iff.mp below
  simp only [HostState.executeKind, characteristic, Word.toBitVec64_toNat word,
    if_pos bounds, execution]

/-- Raw handler meaning plus actual register observations determine the entire dispatch. -/
theorem run_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (host : HostState) (running : host.exitCode = none)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 input.call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.call.arg2)) :
    host.run policy context = some (execution input host) := by
  apply (host.run_eq_some_iff policy context (execution input host)).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, executeKind_of_spec input valid host policy characteristic context⟩
  · simpa [valid.1, Word.toBitVec64, Word.toNat, execution, SyscallKind.code] using code
  · simp [execution, valid.2.1, HostState.result, SyscallKind.code, Word.toBitVec64, Word.toNat]

/-- HALT is terminal in the host interpreter, including when the exit code is zero. -/
theorem stopped_after (input : Inputs (ZMod p)) (host : HostState)
    (policy : HostPolicy) (context : HostReadContext) :
    (execution input host).effect.state.run policy context = none := by
  simp [execution, HostState.run]

end SP1Clean.HostHaltChip
