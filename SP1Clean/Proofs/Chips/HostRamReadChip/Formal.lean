import SP1Clean.Native.Chips.HostRamReadChip.Defs

/-! # Soundness and completeness of shared host reads

The subcircuit establishes the physical RAM access. Whole-word equality rules out writes;
the sharing flag authorizes exactly one additional logical consumer of the same payload.
-/

namespace SP1Clean.HostRamReadChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.ProverAssumptions input.ram ∧
    input.ram.new_value = input.ram.access.prev_value ∧ IsBool input.shared

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [HostRamAccessChip.circuit, Gadgets.Equality.circuit,
    HostRamAccessChip.channel, channel, Inputs.message, HostRamAccessChip.Inputs.clockLow]
  have valid := Spec.message (input := ⟨_, _⟩) h_holds
  exact ⟨h_holds, fun _ _ => valid, fun _ _ => valid⟩

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [HostRamAccessChip.circuit, Gadgets.Equality.circuit,
    HostRamAccessChip.channel, channel]
  exact h_assumptions

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness
  completeness
  channelsWithRequirements :=
    [Channels.memoryChannel.toRaw, HostRamAccessChip.channel.toRaw, channel.toRaw]

end SP1Clean.HostRamReadChip
