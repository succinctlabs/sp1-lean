import SP1Clean.FormalModel.Contracts.HintWords
import Clean.Utils.Tactics

/-! # Fixed source words for immutable hints

The lookup supplies full node contents from the actual source hint list. It includes the final
zero-padded word required by HINT_READ. No witness selects or changes the byte inventory.
Allocation providers and full consumer coverage remain separate from this source component.
-/

namespace SP1Clean.HostHintQueue

open Circuit Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def sourceWordMain (hints : List Bytes) (input : Var WordRecord (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup (sourceWordTable hints).toTable input
  wordChannel.push input

instance sourceWordElaborated (hints : List Bytes) :
    ElaboratedCircuit (ZMod p) WordRecord unit (sourceWordMain hints) := by
  elaborate_circuit

def sourceWord (hints : List Bytes) : GeneralFormalCircuit (ZMod p) WordRecord unit where
  name := "sp1.native.hint_word.source"
  main := sourceWordMain hints
  elaborated := sourceWordElaborated hints
  Spec input _ _ := input.Binds (ofList hints).1
  ProverAssumptions input _ _ := (sourceWordTable hints).Spec input
  channelsWithRequirements := [wordChannel.toRaw]
  soundness := by
    circuit_proof_start [sourceWordMain, wordChannel]
    exact ⟨(sourceWordTable_sound hints _ h_holds).2,
      fun _ _ => (sourceWordTable_sound hints _ h_holds).1⟩
  completeness := by
    circuit_proof_start [sourceWordMain, wordChannel]
    exact h_assumptions

end SP1Clean.HostHintQueue
