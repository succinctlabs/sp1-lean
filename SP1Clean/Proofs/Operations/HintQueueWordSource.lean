import SP1Clean.Native.Operations.HintQueueWordSource
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # Source word authentication from actual lookup constraints

The provider publishes exactly one immutable node word and has no incoming channel assumptions.
These local facts are ready for the mixed ensemble's source classification and balance proof;
this module does not assume that such global installation or consumer coverage is already done.
-/

namespace SP1Clean.HostHintQueue

open Circuit Air.Flat Model.Core Model.Core.HintQueue
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
theorem source_word_interactions (hints : List Bytes)
    (input : Var WordRecord (ZMod p)) (offset : ℕ) :
    ((sourceWordMain hints input).operations offset).interactionsWith wordChannel.toRaw =
      [(wordChannel.pushed input).toRaw] := by
  simp [sourceWordMain, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
theorem source_word_values (hints : List Bytes) (input : Var WordRecord (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((sourceWordMain hints input).operations offset).interactionValuesWith wordChannel.toRaw env =
      [wordChannel.pushedValue (Eval.eval env input)] := by
  simp only [Operations.interactionValuesWith, source_word_interactions,
    List.map_cons, List.map_nil, Channel.eval_pushed]

theorem source_word_other_interactions (hints : List Bytes)
    (input : Var WordRecord (ZMod p)) (offset : ℕ)
    (target : RawChannel (ZMod p)) (different : target ≠ wordChannel.toRaw) :
    ((sourceWordMain hints input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil (sourceWord hints).base target input offset
  simpa [sourceWord, circuit_norm] using different

/-- The fixed lookup supplies word meaning without a caller-supplied channel or byte oracle. -/
theorem source_word_spec_of_constraints (hints : List Bytes) (env : Environment (ZMod p))
    (constraints : ({ circuit := sourceWord hints } : Component (ZMod p)).operations.ConstraintsHold env) :
    ({ circuit := sourceWord hints } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := sourceWord hints } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  change selected ∈ [] at member
  exact False.elim (List.not_mem_nil member)

end SP1Clean.HostHintQueue
