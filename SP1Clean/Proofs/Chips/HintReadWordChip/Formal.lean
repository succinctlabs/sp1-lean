import SP1Clean.Native.Chips.HintReadWordChip.Defs

/-! # Soundness and completeness of physical hint word transfers

The complete row means a bounded physical RAM transfer and one successive immutable hint
word. Permission and content authenticity remain balance-derived facts, never channel guarantees.
-/

namespace SP1Clean.HintReadWordChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def ProverAssumptions (last : Bool) (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.ProverAssumptions input.ram ∧ HintReadStep.Spec last (input.step last)

omit [Fact (2 ^ 25 < p)] in
private theorem eval_step (env : Environment (ZMod p)) (last : Bool) (input : Var Inputs (ZMod p)) :
    ProvableStruct.eval env (input.step last) = (ProvableStruct.eval env input).step last := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  cases last <;> simp only [Inputs.step, Inputs.address, circuit_norm]

def circuit (last : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := if last then "sp1.native.hint_read_word.last" else "sp1.native.hint_read_word.next"
  main := main last
  elaborated := elaborated last
  Spec input _ _ := Spec last input
  ProverAssumptions input _ _ := ProverAssumptions last input
  channelsWithRequirements := [Channels.memoryChannel.toRaw, HostRamAccessChip.channel.toRaw,
    HostHintQueue.wordChannel.toRaw, WritePermissionProvider.channel.toRaw, stateChannel.toRaw]
  soundness := by
    circuit_proof_start [HostRamAccessChip.circuit, HintReadStep.circuit,
      HostRamAccessChip.channel, WritePermissionProvider.channel, stateChannel, eval_step]
    exact h_holds
  completeness := by
    circuit_proof_start [HostRamAccessChip.circuit, HintReadStep.circuit,
      HostRamAccessChip.channel, WritePermissionProvider.channel, stateChannel, eval_step]
    exact h_assumptions

end SP1Clean.HintReadWordChip
