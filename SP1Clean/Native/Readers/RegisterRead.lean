import SP1Clean.FormalModel.Contracts.RegisterRead
import SP1Clean.Model.MemoryClock
import SP1Clean.Native.Readers.RegisterAccessCols
import ToClean.Circuit.InteractionRecovery

/-! # A composed register read and unchanged Memory write-back

The timestamp subcircuit supplies the two gap bounds. The Memory pull supplies the old word
and previous low-clock bound; together they establish strict natural time order. The same
received word discharges the push requirement, without a word-bound assumption from the caller.
-/

namespace SP1Clean.Readers.RegisterRead

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  Assumptions input ∧
    RegisterAccessCols.Spec ⟨input.cols, input.is_real, input.clk_target⟩ ∧
    (input.is_real = 1 → Word.isU64 input.cols.prev_value ∧ MemoryMsg.ClkBound input.prior)

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion RegisterAccessCols.circuit ⟨input.cols, input.is_real, input.clk_target⟩
  memoryChannel.pullIf input.is_real input.prior
  memoryChannel.pushIf input.is_real input.pushed

@[local circuit_norm] private theorem timestamp_guarantees :
    (RegisterAccessCols.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw] := rfl

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw, memoryChannel.toRaw]

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun input _ => Assumptions input) (fun input _ _ => Spec input) := by
  circuit_proof_start [RegisterAccessCols.circuit, Inputs.prior, Inputs.pushed,
    memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
  obtain ⟨binary, clock⟩ := h_assumptions
  obtain ⟨timestamp, word⟩ := h_holds
  refine ⟨?_, fun h1 h0 => off_gate_vacuous binary h1 h0, fun _ h0 => ?_⟩
  · intro real
    have old := word (by rw [real])
    have gap := timestamp binary real
    refine ⟨old.1, old.2, ?_⟩
    have order := MemoryClock.lt_of_register_gap _ _ _ old.2 gap.1 gap.2
    dsimp only at order
    simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat]
    omega
  · have real := binary.resolve_left h0
    exact ⟨(word (by rw [real])).1, clock real⟩

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [RegisterAccessCols.circuit, ProverAssumptions, Inputs.prior, Inputs.pushed,
    memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
  exact ⟨⟨h_assumptions.1.1, h_assumptions.2.1⟩, fun real => h_assumptions.2.2 (neg_inj.mp real)⟩

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Assumptions input _ := Assumptions input
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness
  completeness
  channelsWithRequirements := [memoryChannel.toRaw]

end SP1Clean.Readers.RegisterRead
