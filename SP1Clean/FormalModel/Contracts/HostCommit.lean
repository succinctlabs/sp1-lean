import SP1Clean.FormalModel.Contracts.HostCall
import SP1Clean.FormalModel.Contracts.ClockOrder
import SP1Clean.FormalModel.Contracts.BoundedWord

/-! # Mutable native commitment-bank updates

A component is specialized to one of two banks and one of eight slots. The selected full syscall
code and register arguments remain constrained; the specialization is only table routing. Each
row consumes the authenticated call and replaces exactly one slot in a clock-ordered bank state.
The original instruction's PublicValues pulls receive per-call matching records, not a claim
that every historical value equals the final bank. Exact upstream public-value binding stays separate.
-/

namespace SP1Clean.HostCommitChip

open Circuit

structure State (F : Type) where
  clk_high : F
  clk_low : F
  values : Vector (Word F) 8
deriving ProvableStruct
provable_struct_eval_lemmas State

structure Inputs (F : Type) where
  call : HostCallChip.Message F
  previous : State F
  comparison : Circuits.Types.LtOperationUnsigned F
  bytes : Circuits.Types.U16toU8Operation F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def codeWord {R : Type} [NatCast R] [Zero R] (deferred : Bool) : Word R :=
  #v[(if deferred then 26 else 16 : ℕ), 0, 0, 0]

def slotWord {R : Type} [NatCast R] [Zero R] (slot : Fin 8) : Word R := #v[(slot.val : ℕ), 0, 0, 0]

def bound (p : ℕ) (deferred : Bool) : ℕ := if deferred then min p (2 ^ 32) else 2 ^ 32

def stateChannel {p : ℕ} [Fact p.Prime] (deferred : Bool) : Channel (ZMod p) State where
  name := if deferred then "sp1.native.deferred_state" else "sp1.native.commit_state"
  Guarantees _ _ := True

def Inputs.next {R : Type} (input : Inputs R) (slot : Fin 8) : State R :=
  ⟨input.call.clk_high, input.call.clk_low, input.previous.values.set slot input.call.arg2⟩

def Inputs.clock {R : Type} (input : Inputs R) : ClockOrder.Inputs R :=
  ⟨input.previous.clk_high, input.previous.clk_low, input.call.clk_high, input.call.clk_low⟩

def Inputs.digest {R : Type} [Sub R] [Mul R]
    (input : Inputs R) (inverse256 : R) : Vector R 4 :=
  #v[input.bytes.low_bytes[0], (input.call.arg2[0] - input.bytes.low_bytes[0]) * inverse256,
     input.bytes.low_bytes[1], (input.call.arg2[1] - input.bytes.low_bytes[1]) * inverse256]

def CallSpec {p : ℕ} [Fact p.Prime] (deferred : Bool) (slot : Fin 8)
    (call : HostCallChip.Message (ZMod p)) : Prop :=
  call.code = codeWord deferred ∧ call.arg1 = slotWord slot ∧
    call.result = codeWord deferred ∧ call.length = 0 ∧
    Word.isU64 call.arg2 ∧ Word.toNat call.arg2 < bound p deferred

def Spec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] (deferred : Bool) (slot : Fin 8)
    (input : Inputs (ZMod p)) : Prop :=
  CallSpec deferred slot input.call ∧ ClockOrder.Spec input.clock ∧
    U16toU8OperationSafe.DecompSpec input.call.arg2 input.bytes

end SP1Clean.HostCommitChip
