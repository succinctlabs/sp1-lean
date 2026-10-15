import SP1Clean.Soundness.HintReadCoverage
import SP1Clean.Proofs.Chips.HostHintReadChip.Bridge
import SP1Clean.Proofs.Chips.HostHintReadChip.Ledger

/-! # HINT_READ coverage with the actual handler endpoints

The word walk now starts and ends at the handler's physical interactions. Authenticated current
queue and immutable records identify its exact node and padded count. The enclosing shard must
still derive these record bindings, local specifications, and each call's projected balance.
-/

namespace SP1Clean.Soundness.HostHintReadCoverage

open Circuit Air.Flat Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def handler : Component (ZMod p) := { circuit := HostHintReadChip.circuit }

def input (env : Environment (ZMod p)) : HostHintReadChip.Inputs (ZMod p) :=
  valueFromOffset HostHintReadChip.Inputs 0 env

theorem handler_cursor (env : Environment (ZMod p)) :
    handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env =
      [HintReadWordChip.stateChannel.pushedValue (input env).first,
       HintReadWordChip.stateChannel.pulledValue (input env).final] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
    (size HostHintReadChip.Inputs)).interactionValuesWith HintReadWordChip.stateChannel.toRaw env = _
  rw [HostHintReadChip.cursor_values, eval_varFromOffset_valueFromOffset]
  rfl

/-- Physical cursor balance requires every word of the handler's actual current hint exactly once. -/
theorem complete_indices (env : Environment (ZMod p)) (tables : List (Table (ZMod p)))
    (data : ProverData (ZMod p)) (valid : handler.Spec env)
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (wordSpecs : HintReadCoverage.Steps tables data)
    (balanced : BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        tables.flatMap (·.interactionsWith data HintReadWordChip.stateChannel.toRaw)))
    (store : Store) (hints : List Bytes) (current : (input env).previous.Binds store hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store) :
    ∃ bytes rest, hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants tables data).map
        fun row => Address.toNat (HintReadCoverage.rowInput row).index).Perm
          (List.range (wordCount bytes)) := by
  obtain ⟨node, rest, _, head, next, _, count⟩ :=
    HostHintReadChip.node_effect_of_spec (input env) valid store hints current header ending
  rw [handler_cursor] at balanced
  have inventory := HintReadCoverage.complete_indices tables data (input env).first (input env).final
    aligned wordSpecs balanced (by simp [HostHintReadChip.Inputs.first, Address.toNat])
  change _ = _ at count
  change List.Perm _ (List.range (Address.toNat (input env).span.count)) at inventory
  rw [count] at inventory
  exact ⟨node.bytes, rest, head, next, inventory⟩

end SP1Clean.Soundness.HostHintReadCoverage
