module

public import Clean.Circuit.Channel

/-! # Evaluated interactions without local guarantees

Clean provides `Channel.emit` for arbitrary signed multiplicities without assuming the channel's
guarantees, but its evaluated-value helpers cover only pushes and guarantee-bearing pulls.
`emittedValue` and its evaluation law complete that interface. A negative emission still participates
in the same algebraic balance; its semantic meaning can be established later by global grounding.
These additions belong beside `Channel.pushedValue` in `Clean/Circuit/Channel.lean`.
-/

@[expose] public section

namespace Channel

variable {F : Type} [FiniteField F] {Message : TypeMap} [ProvableType Message]

@[circuit_norm]
def emittedValue (channel : Channel F Message) (mult : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := mult
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

theorem eval_emitted {channel : Channel F Message} {mult : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
    (channel.emitted mult msg).toRaw.eval env = channel.emittedValue (env mult) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  congr
  rw [← ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

end Channel
