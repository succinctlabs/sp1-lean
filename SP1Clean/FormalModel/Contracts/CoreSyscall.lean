import SP1Clean.Model.Core.SyscallTable
import SP1Clean.FormalModel.Contracts.SyscallInstrsChip

/-! # Native syscall profile contracts

The profile guard proves that an active row's entire syscall register is a bounded canonical
encoding of one of the eight selected calls. Padding has no code restriction. The whole-chip
contract retains the upstream instruction-row laws and adds this native restriction explicitly.
-/

namespace SP1Clean.SyscallCodeGuard

structure Inputs (F : Type) where
  code : Word F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
    (input.is_real = 1 → input.code.isU64 ∧ Model.Core.SyscallKind.Supported input.code.toBitVec64)

end SP1Clean.SyscallCodeGuard

namespace SP1Clean.CoreSyscallChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def Spec (input : SyscallInstrsChip.Inputs (ZMod p)) : Prop :=
  SyscallInstrsChip.Spec input ∧ SyscallCodeGuard.Spec ⟨input.op_a_memory.prev_value, input.is_real⟩

end SP1Clean.CoreSyscallChip
