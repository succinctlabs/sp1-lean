import SP1Clean.FormalModel.Contracts.HintQueue

/-! # Queue cursors bound to complete persistent stores

The frontier records every allocated node, including unreachable historical nodes. Source and
compiler cursors use the actual store size; empty queues do not reset that size. The private
state channel itself carries no semantic binding.
-/

namespace SP1Clean.HostHintQueue

open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem State.Binds.head_le {state : State (ZMod p)} {store : Store} {hints : List Bytes}
    (binding : state.Binds store hints) : Address.toNat state.head ≤ Address.toNat state.allocated := by
  rw [binding.2.2.1]
  exact binding.2.2.2.bound

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem State.Binds.store_bound {state : State (ZMod p)} {store : Store} {hints : List Bytes}
    (binding : state.Binds store hints) : store.size < 2 ^ 48 := by
  rw [← binding.2.2.1]
  exact Address.toNat_lt binding.2.1

/-- Source and subsequent semantic stores have canonical field cursors under one capacity bound. -/
theorem State.encode_binds (clock : ℕ) {store : Store} {head : ℕ} {hints : List Bytes}
    (current : Represents store head hints) (fits : store.size < 2 ^ 48) :
    (State.encode (p := p) clock head store.size).Binds store hints := by
  refine ⟨Address.bounded_ofNat _, Address.bounded_ofNat _, Address.toNat_ofNat _ fits, ?_⟩
  change Represents store (Address.toNat (Address.ofNat (p := p) head)) hints
  rw [Address.toNat_ofNat _ (by have := current.bound; omega)]
  exact current

/-- Source initialization includes the full node inventory, even when later execution pops it. -/
theorem State.source_binds (clock : ℕ) (hints : List Bytes) (fits : hints.length < 2 ^ 48) :
    (State.encode (p := p) clock (ofList hints).2 hints.length).Binds (ofList hints).1 hints := by
  have size := ofList_size hints
  rw [← size]
  exact State.encode_binds clock (ofList_represents hints) (by omega)

end SP1Clean.HostHintQueue
