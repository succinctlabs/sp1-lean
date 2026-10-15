import SP1Clean.Proofs.Operations.HintReadStep
import ToClean.Circuit.InteractionRecovery

/-! # The successive word operation's actual ledger

The only non-Byte interaction is one complete immutable word pull, including its end marker.
This equation is used by the physical consumer; no separately supplied word-request list is used.
-/

namespace SP1Clean.HintReadStep

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem main_nonbyte_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) (notByte : target ≠ byteChannel.toRaw) :
    ((main last input).operations offset).interactionsWith target =
      [(HostHintQueue.wordChannel.pulled input.word).toRaw].filter (fun i => decide (i.channel = target)) := by
  have adder (args : Var AddrAddOperation.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      AddrAddOperation.circuit target args (by simpa [AddrAddOperation.circuit, circuit_norm] using notByte)
      List.not_mem_nil (n := n)
  have range (args : Var Word (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      WordRangeCheck.circuit target args List.not_mem_nil List.not_mem_nil (n := n)
  simp only [main, circuit_norm, List.nil_append]
  simp only [List.filter_cons, adder, range, List.append_nil, List.filter_nil, circuit_norm]

theorem main_word_interactions (last : Bool) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main last input).operations offset).interactionsWith HostHintQueue.wordChannel.toRaw =
      [(HostHintQueue.wordChannel.pulled input.word).toRaw] := by
  rw [main_nonbyte_interactions last input offset _ (by
    simp [HostHintQueue.wordChannel, byteChannel, circuit_norm])]
  simp [circuit_norm]

end SP1Clean.HintReadStep
