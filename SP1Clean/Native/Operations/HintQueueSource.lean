import SP1Clean.FormalModel.Contracts.HintQueue
import Clean.Utils.Tactics

/-! # Initial immutable hint nodes from the complete source queue

The fixed lookup is computed from source bytes and supplies one node observation per row.
No witness chooses the node inventory or its lengths. Later allocations must be authorized by
their own providers; this source component only covers the original persistent nodes.
-/

namespace SP1Clean.HostHintQueue

open Circuit SP1Clean.Model.Core SP1Clean.Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def sourceMain (hints : List Bytes) (input : Var NodeRecord (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup (sourceTable hints).toTable input
  nodeChannel.push input

instance sourceElaborated (hints : List Bytes) : ElaboratedCircuit (ZMod p) NodeRecord unit (sourceMain hints) := by
  elaborate_circuit

def source (hints : List Bytes) : GeneralFormalCircuit (ZMod p) NodeRecord unit where
  name := "sp1.native.hint_node.source"
  main := sourceMain hints
  elaborated := sourceElaborated hints
  Spec input _ _ := input.Binds (ofList hints).1
  ProverAssumptions input _ _ := (sourceTable hints).Spec input
  channelsWithRequirements := [nodeChannel.toRaw]
  soundness := by
    circuit_proof_start [sourceMain, nodeChannel]
    exact ⟨(sourceTable_sound hints _ h_holds).2, fun _ _ => (sourceTable_sound hints _ h_holds).1⟩
  completeness := by
    circuit_proof_start [sourceMain, nodeChannel]
    exact h_assumptions

end SP1Clean.HostHintQueue
