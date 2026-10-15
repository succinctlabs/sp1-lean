import SP1Clean.FormalModel.Contracts.HintQueue
import SP1Clean.FormalModel.Contracts.HintReadSpan
import SP1Clean.FormalModel.Contracts.HintReadWord

/-! # HINT_READ call, queue, and complete word endpoints

The handler consumes the current immutable node and authenticates its final word. Its private
word cursor starts at zero and ends at the checked padded count and last written address.
The queue moves to the node's tail without resetting the allocation frontier. Actual node/word
binding and complete RAM execution follow from the enclosing source, cursor, and Memory ledgers.
-/

namespace SP1Clean.HostHintReadChip

open Circuit Model.Core Soundness.Target

structure Inputs (F : Type) where
  call : HostCallChip.Message F
  previous : HostHintQueue.State F
  node : HintQueue.NodeRecord F
  span : HintReadSpan.Inputs F
  lastIndex : fields 3 F
  lastValue : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def codeWord {p : ℕ} [Fact p.Prime] : Word (ZMod p) := bitVecToWord SyscallKind.hintRead.code

def Inputs.clock {F : Type} (input : Inputs F) : ClockOrder.Inputs F :=
  ⟨input.previous.clk_high, input.previous.clk_low, input.call.clk_high, input.call.clk_low⟩

def Inputs.next {F : Type} (input : Inputs F) : HostHintQueue.State F :=
  ⟨input.call.clk_high, input.call.clk_low, input.node.tail, input.previous.allocated⟩

def Inputs.endStep {F : Type} [One F] (input : Inputs F) : HintReadStep.Inputs F :=
  ⟨⟨input.node.pointer, input.lastIndex, input.lastValue, 1⟩,
    input.span.last, input.span.count, input.span.last⟩

def Inputs.first {F : Type} [Zero F] (input : Inputs F) : HintReadWordChip.State F :=
  ⟨input.call.clk_high, input.call.clk_low, input.node.pointer, #v[0, 0, 0], input.span.start⟩

def Inputs.final {F : Type} (input : Inputs F) : HintReadWordChip.State F :=
  ⟨input.call.clk_high, input.call.clk_low, input.node.pointer, input.span.count, input.span.last⟩

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  input.call.code = codeWord ∧ input.call.length = 0 ∧ input.call.result = codeWord ∧
    input.call.arg1 = Address.asWord input.span.start ∧ input.call.arg2 = input.span.length.value ∧
    input.span.length.value = input.node.length ∧ input.previous.head = input.node.pointer ∧
    ClockOrder.Spec input.clock ∧ HintReadSpan.Spec input.span ∧
    HintReadStep.Spec true input.endStep ∧ input.node.Valid

end SP1Clean.HostHintReadChip
