import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.BoundedWord

/-! # Native terminal and constrained-replay control calls

HALT accepts canonical exits below both the field characteristic and `2^32`. Its host handler
consumes the instruction handoff; the instruction itself remains the sole Exit sender.
ENTER_UNCONSTRAINED returns zero and has no host or memory effect in constrained replay.
Neither contract imposes a restriction on unused guest arguments.
-/

namespace SP1Clean.HostHaltChip

structure Inputs (F : Type) where
  call : HostCallChip.Message F
  comparison : Circuits.Types.LtOperationUnsigned F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def bound (p : ℕ) : ℕ := min p (2 ^ 32)

def CallSpec {p : ℕ} [Fact p.Prime] (call : HostCallChip.Message (ZMod p)) : Prop :=
  call.code = 0 ∧ call.result = 0 ∧ call.length = 0 ∧
    Word.isU64 call.arg1 ∧ Word.toNat call.arg1 < bound p

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop := CallSpec input.call

end SP1Clean.HostHaltChip

namespace SP1Clean.HostEnterChip

abbrev Inputs := HostCallChip.Message

def codeWord {R : Type} [OfNat R 3] [Zero R] : Word R := #v[3, 0, 0, 0]

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  input.code = codeWord ∧ input.result = 0 ∧ input.length = 0

end SP1Clean.HostEnterChip
