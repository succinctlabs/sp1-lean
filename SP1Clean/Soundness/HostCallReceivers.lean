import SP1Clean.Proofs.Chips.HostControlLedger
import SP1Clean.Proofs.Chips.HostCommitChip.Ledger
import SP1Clean.Proofs.Chips.HostHintLengthChip.Ledger
import ToClean.Air.ReceiverView
import SP1Clean.Soundness.HostLocalCore

/-! # Unit receiver views for native host handlers

Each view reads the complete HostCall directly from its own physical row. Its ledger law is
proved from the existing handler circuit, so a heterogeneous installed registry can account
for every call without per-witness equations. WRITE and VERIFY handlers remain unimplemented.
-/

namespace SP1Clean.Soundness.HostCallReceivers

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def halt : ReceiverView (HostCallChip.channel (p := p)) where
  component := { circuit := HostHaltChip.circuit }
  message env := eval env (varFromOffset HostHaltChip.Inputs 0).call
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0)).operations
      (size HostHaltChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostHaltChip.host_values _ _ env

def enter : ReceiverView (HostCallChip.channel (p := p)) where
  component := { circuit := HostEnterChip.circuit }
  message env := eval env (varFromOffset HostEnterChip.Inputs 0)
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostEnterChip.main (varFromOffset HostEnterChip.Inputs 0)).operations
      (size HostEnterChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostEnterChip.host_values _ _ env

def commit (deferred : Bool) (slot : Fin 8) : ReceiverView (HostCallChip.channel (p := p)) where
  component := { circuit := HostCommitChip.circuit deferred slot }
  message env := eval env (varFromOffset HostCommitChip.Inputs 0).call
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostCommitChip.main deferred slot (varFromOffset HostCommitChip.Inputs 0)).operations
      (size HostCommitChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostCommitChip.host_values deferred slot _ _ env

def hintLength (empty : Bool) : ReceiverView (HostCallChip.channel (p := p)) where
  component := { circuit := HostHintLengthChip.circuit empty }
  message env := eval env (varFromOffset HostHintLengthChip.Inputs 0).call
  interactions env := by
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
    change ((HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.Inputs 0)).operations
      (size HostHintLengthChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
    exact HostHintLengthChip.host_values empty _ _ env

/-- The receiver reads the complete call from the physical HALT row. -/
theorem halt_message (env : Environment (ZMod p)) :
    (HostCallReceivers.halt (p := p)).message env = (valueFromOffset HostHaltChip.Inputs 0 env).call := by
  have evaluated (input : Var HostHaltChip.Inputs (ZMod p)) : eval env input.call = (eval env input).call := by
    cases input
    simp only [circuit_norm]
  simp only [HostCallReceivers.halt, evaluated, eval_varFromOffset_valueFromOffset]

omit [Fact (2 ^ 25 < p)] in
/-- ENTER already has exactly the complete call as its input. -/
theorem enter_message (env : Environment (ZMod p)) :
    (HostCallReceivers.enter (p := p)).message env = valueFromOffset HostEnterChip.Inputs 0 env := by
  simp only [HostCallReceivers.enter, eval_varFromOffset_valueFromOffset]

/-- Each commitment receiver reads its row's complete call. -/
theorem commit_message (deferred : Bool) (slot : Fin 8) (env : Environment (ZMod p)) :
    (HostCallReceivers.commit (p := p) deferred slot).message env =
      (valueFromOffset HostCommitChip.Inputs 0 env).call := by
  have evaluated (input : Var HostCommitChip.Inputs (ZMod p)) : eval env input.call = (eval env input).call := by
    cases input
    simp only [circuit_norm]
  simp only [HostCallReceivers.commit, evaluated, eval_varFromOffset_valueFromOffset]

/-- The implemented non-RAM handlers: control, both eight-slot commitment families,
and empty/nonempty HINT_LEN. HINT_READ adds its own receiver and RAM resources. -/
def available : List (ReceiverView (HostCallChip.channel (p := p))) :=
  [halt, enter] ++ (List.ofFn fun slot => commit false slot) ++
    (List.ofFn fun slot => commit true slot) ++ [hintLength false, hintLength true]

/-- All available handlers satisfy the CPU chronology interface by their static channel metadata. -/
theorem auxiliaryInterface : HostLocalCore.AuxiliaryInterface ((available (p := p)).map (·.component)) := by
  apply HostLocalCore.AuxiliaryInterface.of_channels
  · have checked : ((available (p := p)).map (·.component)).all (fun component =>
        !(component.circuit.channelsWithRequirements.map RawChannel.name).contains (Channels.byteChannel (p := p)).toRaw.name) = true := rfl
    intro component member used
    have valid := List.all_eq_true.mp checked component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    rw [present] at valid
    contradiction
  · have checked : ((available (p := p)).map (·.component)).all (fun component =>
        !(component.circuit.channels.map RawChannel.name).contains (Channels.stateChannel (p := p)).toRaw.name) = true := rfl
    intro component member used
    have valid := List.all_eq_true.mp checked component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    rw [present] at valid
    contradiction

end SP1Clean.Soundness.HostCallReceivers
