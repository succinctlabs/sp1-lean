import SP1Clean.Proofs.Chips.HostEnterChip.Formal
import SP1Clean.Model.Core.HostExecutionLaws

/-! # ENTER_UNCONSTRAINED is a zero-effect constrained-replay step

The complete dispatch theorem authenticates the canonical code, both unused guest arguments,
and the zero return. No host field or guest memory changes, and an already halted host cannot
dispatch this call. Unconstrained execution is deliberately outside this native profile.
-/

namespace SP1Clean.HostEnterChip

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def execution (input : Inputs (ZMod p)) (host : HostState) : HostExecution :=
  ⟨.enterUnconstrained, Word.toBitVec64 input.arg1, Word.toBitVec64 input.arg2,
    Word.toBitVec64 input.result, ⟨host, none⟩⟩

private theorem code_value : Word.toBitVec64 (codeWord (R := ZMod p)) = SyscallKind.enterUnconstrained.code := by
  have hp := Fact.out (p := 2 ^ 17 < p)
  have three : (3 : ZMod p).val = 3 := by
    change ((3 : ℕ) : ZMod p).val = 3
    exact ZMod.val_natCast_of_lt (by omega)
  simp [Word.toBitVec64, Word.toNat, codeWord, three, SyscallKind.code]

/-- Matched register observations and the handler contract yield a complete zero-effect call. -/
theorem run_of_spec (input : Inputs (ZMod p)) (valid : Spec input)
    (host : HostState) (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 input.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.arg2)) :
    host.run policy context = some (execution input host) := by
  apply (host.run_eq_some_iff policy context (execution input host)).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, rfl⟩
  · simpa only [valid.1, code_value, execution] using code
  · simp [execution, valid.2.1, HostState.result, Word.toBitVec64, Word.toNat]

end SP1Clean.HostEnterChip
