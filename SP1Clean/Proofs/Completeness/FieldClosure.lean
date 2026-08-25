import Clean.Air.Balance
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.ZMod.Basic

/-! # Field-native closure for aggregate lookup providers

Clean balances a channel in the field: for every concrete message, the sum of interaction
multiplicities is zero.  Aggregate Byte, Range, and Program providers can therefore carry the
natural number of matching unit pulls directly as a field element.  They do not need that natural
number to be the centered integer representative of the field element.

This file proves the generic list algebra for that construction.  Given a list of semantic messages,
it emits one unit pull per occurrence and one aggregate provider interaction per distinct message.
The resulting Clean `balanceOf` is zero at every concrete message.  The corresponding
`BalancedInteractions` theorem requires only Clean's total interaction-count bound; there is no
`signedVal` projection and no per-provider half-field bound.

The construction stays on `Interaction (ZMod p)` and does not introduce another ledger
representation.  The semantic message type is merely a convenient index for constructing typed
channel interactions.  Field balance does not require its concrete encoding to be injective;
`aggregateProviders_messages_nodup` records the stronger, canonical-footprint fact when it is.
-/

namespace SP1Clean.FieldClosure

variable {p : ℕ}
variable {Message : Type*}

/-- One unit consumer interaction for every occurrence in `messages`. -/
def unitPulls
    (pull : Message → Interaction (ZMod p)) (messages : List Message) :
    List (Interaction (ZMod p)) :=
  messages.map pull

/-- One aggregate provider interaction per distinct demanded message.

The provider multiplicity is the exact natural occurrence count cast by the caller's provider
constructor.  Since `List.dedup` contains precisely the messages occurring in `messages`, this emits
no zero-demand provider row. -/
def aggregateProviders
    [DecidableEq Message]
    (provider : Message → ℕ → Interaction (ZMod p)) (messages : List Message) :
    List (Interaction (ZMod p)) :=
  messages.dedup.map fun message => provider message (messages.count message)

/-- Every emitted aggregate provider row has strictly positive natural demand. -/
theorem aggregateProviders_positiveDemand
    [DecidableEq Message]
    (provider : Message → ℕ → Interaction (ZMod p))
    (messages : List Message) {interaction : Interaction (ZMod p)}
    (interaction_mem : interaction ∈ aggregateProviders provider messages) :
    ∃ message ∈ messages,
      interaction = provider message (messages.count message) ∧ 0 < messages.count message := by
  obtain ⟨message, message_mem, rfl⟩ := List.mem_map.mp interaction_mem
  have message_mem' : message ∈ messages := List.mem_dedup.mp message_mem
  exact ⟨message, message_mem', rfl, List.count_pos_iff.mpr message_mem'⟩

/-- With an injective concrete encoding, aggregate provider rows have pairwise-distinct Clean
messages.  Thus `aggregateProviders` is literally one row per nonzero concrete message, not merely
one row per semantic index. -/
theorem aggregateProviders_messages_nodup
    [DecidableEq Message]
    (encode : Message → Array (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (provider_msg : ∀ message demand, (provider message demand).msg = encode message)
    (encode_injective : Function.Injective encode)
    (messages : List Message) :
    ((aggregateProviders provider messages).map fun interaction => interaction.msg).Nodup := by
  simp only [aggregateProviders, List.map_map, Function.comp_def, provider_msg]
  exact List.Nodup.map encode_injective (List.nodup_dedup messages)

/-- The canonical closure footprint is the number of pulls plus the number of distinct demanded
messages. -/
theorem unitPulls_append_aggregateProviders_length
    [DecidableEq Message]
    (pull : Message → Interaction (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (messages : List Message) :
    (unitPulls pull messages ++ aggregateProviders provider messages).length =
      messages.length + messages.dedup.length := by
  simp [unitPulls, aggregateProviders]

/-- Unit pulls contribute the negated natural occurrence count at every concrete Clean message. -/
theorem balanceOf_unitPulls
    [Fact p.Prime]
    (encode : Message → Array (ZMod p))
    (pull : Message → Interaction (ZMod p))
    (pull_msg : ∀ message, (pull message).msg = encode message)
    (pull_mult : ∀ message, (pull message).mult = -1)
    (messages : List Message) (target : Array (ZMod p)) :
    balanceOf (unitPulls pull messages) target =
      -((messages.countP fun message => encode message = target : ℕ) : ZMod p) := by
  induction messages with
  | nil => simp [unitPulls, balanceOf]
  | cons message messages ih =>
      rw [unitPulls, List.map_cons, balanceOf_cons, pull_msg, pull_mult]
      simp only [List.countP_cons]
      by_cases h : encode message = target
      · simp only [h, decide_true, if_true]
        rw [show balanceOf (List.map pull messages) target =
          -((messages.countP fun message => encode message = target : ℕ) : ZMod p) from ih]
        push_cast
        ring
      · simp only [h, decide_false, Bool.false_eq_true, if_false, Nat.add_zero, zero_add]
        exact ih

/-- Aggregate providers contribute the positive natural occurrence count at every concrete message.

Duplicate elimination leaves one provider per semantic message; if several semantic messages have
the same concrete encoding, their counts add to the concrete message's total.  The contribution is
zero when no demanded message has encoding `target`. -/
theorem balanceOf_aggregateProviders
    [Fact p.Prime]
    [DecidableEq Message]
    (encode : Message → Array (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (provider_msg : ∀ message demand, (provider message demand).msg = encode message)
    (provider_mult : ∀ message demand,
      (provider message demand).mult = (demand : ZMod p))
    (messages : List Message) (target : Array (ZMod p)) :
    balanceOf (aggregateProviders provider messages) target =
      ((messages.countP fun message => encode message = target : ℕ) : ZMod p) := by
  simp only [aggregateProviders, balanceOf, List.filter_map, List.map_map]
  simp only [Function.comp_def, provider_msg, provider_mult]
  rw [← List.sum_map_count_dedup_filter_eq_countP
    (fun message => encode message = target) messages]
  simpa only [List.map_map, Function.comp_def] using
    (Nat.cast_list_sum (R := ZMod p)
      ((messages.dedup.filter fun message => encode message = target).map
        fun message => messages.count message)).symm

/-- Unit consumer pulls and their one-row-per-message aggregate closure balance in the field. -/
theorem balanceOf_unitPulls_append_aggregateProviders
    [Fact p.Prime]
    [DecidableEq Message]
    (encode : Message → Array (ZMod p))
    (pull : Message → Interaction (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (pull_msg : ∀ message, (pull message).msg = encode message)
    (pull_mult : ∀ message, (pull message).mult = -1)
    (provider_msg : ∀ message demand, (provider message demand).msg = encode message)
    (provider_mult : ∀ message demand,
      (provider message demand).mult = (demand : ZMod p))
    (messages : List Message) (target : Array (ZMod p)) :
    balanceOf (unitPulls pull messages ++ aggregateProviders provider messages) target = 0 := by
  rw [balanceOf_append,
    balanceOf_unitPulls encode pull pull_msg pull_mult,
    balanceOf_aggregateProviders encode provider provider_msg provider_mult]
  exact neg_add_cancel _

/-- The field-native closure satisfies Clean's channel-balance predicate.

The sole capacity premise is Clean's own bound on the total number of interactions.  In particular,
there is no constraint on the natural count carried by any individual aggregate provider row. -/
theorem balancedInteractions_unitPulls_append_aggregateProviders
    [Fact p.Prime]
    [DecidableEq Message]
    (encode : Message → Array (ZMod p))
    (pull : Message → Interaction (ZMod p))
    (provider : Message → ℕ → Interaction (ZMod p))
    (pull_msg : ∀ message, (pull message).msg = encode message)
    (pull_mult : ∀ message, (pull message).mult = -1)
    (provider_msg : ∀ message demand, (provider message demand).msg = encode message)
    (provider_mult : ∀ message demand,
      (provider message demand).mult = (demand : ZMod p))
    (messages : List Message)
    (length_lt :
      (unitPulls pull messages ++ aggregateProviders provider messages).length < p) :
    BalancedInteractions
      (unitPulls pull messages ++ aggregateProviders provider messages) := by
  constructor
  · left
    simpa only [ZMod.ringChar_zmod_n] using length_lt
  · exact balanceOf_unitPulls_append_aggregateProviders encode pull provider pull_msg pull_mult
      provider_msg provider_mult messages

end SP1Clean.FieldClosure
