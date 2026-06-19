import SP1Clean.Model.Channels
import Clean.Air.FlatEnsemble

/-! # `GatedVm` — a gated, clk-ordered VM ensemble (the data layer)

Models SP1's whole machine as a "main-channel" VM **with gated (`±is_real`) multiplicities**: SP1 gates
every state-bus interaction by `is_real` (Rust `adapter/state.rs:82-88`), so padding rows contribute
`mult = 0` and drop out of the LogUp sum. Clean's `VmTables`/balance engine hardwires constant `±1`
multiplicities (a no-padding VM), so `GatedVm` uses a gated-multiplicity form instead and **omits**
`VmTables`' exposure obligations (`tables_channel`/`verifier_channel`/`verifier_requirements`) — those
exist only to feed Clean's VM soundness engine, which is not used here (soundness is supplied at
instantiation, `GatedVm/Formal.lean`).

This file contains the **data**: the structure, its `toEnsemble` into a plain Clean `Air.Flat.Ensemble`
(the multiplicity-general object whose `Statement`/`BalancedChannels` are consumed), and the
`circuit_norm` rfl-lemmas. The faithfulness anchor (SP1's boundary is bus-enforced via a constant-`±1`
verifier on top of gated tables) is discharged in the SP1 instance (`Soundness/SP1GatedVm.lean`). -/

namespace SP1Clean.Soundness

open Air.Flat
open Circuit

variable {F : Type} [Field F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A gated VM machine description: a typed **state channel** (the VM "main channel"), the component
`tables`, the remaining `busChannels` (memory/program/byte, already in `RawChannel` form), and a
boundary `verifier` exposing the public initial/final state. The state channel is exposed gated
(`toRaw` (gated post-#398)) in `toEnsemble`; the tables emit `±is_real` on it (genesis/finalization use constant
`mult = 1`, which is just `is_real = 1` on an always-real boundary row). -/
structure GatedVm (F : Type) [Field F] [DecidableEq F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  {StateMessage : TypeMap}
  [provableState : ProvableType StateMessage]
  /-- the VM "main channel" carrying the machine state (SP1: `StateMsg`). -/
  stateChannel : Channel F StateMessage
  /-- the component tables (SP1: the 22 wired chips as `⟨chip.circuit⟩`). -/
  tables : List (Component F)
  /-- the remaining buses (SP1: memory/program/byte), already raw. -/
  busChannels : List (RawChannel F)
  /-- the boundary/verifier: pushes the public initial state, pulls the public final state. -/
  verifier : GeneralFormalCircuit F PublicIO unit := .empty F PublicIO
  verifier_length_zero : ∀ pi, verifier.localLength pi = 0 := by
    simp only [GeneralFormalCircuit.empty, circuit_norm]

instance (vm : GatedVm F PublicIO) : ProvableType vm.StateMessage := vm.provableState

/-- The plain Clean `Air.Flat.Ensemble` underlying a `GatedVm`: the state channel **gated**
(`toRaw` (gated post-#398)) followed by the other buses, the component tables, and the boundary verifier. We build on
the *plain* ensemble (whose `BalancedChannels`/`Statement` are multiplicity-general), not Clean's
constant-`±1` `VmTables.toEnsemble`. -/
def GatedVm.toEnsemble (vm : GatedVm F PublicIO) : Ensemble F PublicIO where
  tables := vm.tables
  channels := vm.stateChannel.toRaw :: vm.busChannels
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

@[circuit_norm] lemma GatedVm.toEnsemble_tables (vm : GatedVm F PublicIO) :
    vm.toEnsemble.tables = vm.tables := rfl
@[circuit_norm] lemma GatedVm.toEnsemble_channels (vm : GatedVm F PublicIO) :
    vm.toEnsemble.channels = vm.stateChannel.toRaw :: vm.busChannels := rfl
@[circuit_norm] lemma GatedVm.toEnsemble_verifier (vm : GatedVm F PublicIO) :
    vm.toEnsemble.verifier = vm.verifier := rfl

end SP1Clean.Soundness
