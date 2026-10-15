import SP1Clean.Soundness.HostCallLedger
import SP1Clean.Soundness.LocalCoreEventUniqueness

/-! # Instruction clock uniqueness at the host handoff

Projection of the wrapper's physical active rows transfers the proved CPU clock uniqueness.
The primary theorem consumes only State balance and Byte guarantees; the older complete-balance
corollary remains available. `HostLocalCore` installs the wrapper and proves this physical
projection internally, retaining all host RAM effects in the extended Memory ledger.
-/

namespace SP1Clean.Soundness.LocalCore

open Circuit Air.Flat Channels Model.Core NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Exact active-row projection identifies every wrapper call with a distinct actual CPU event.
It neither assumes handler uniqueness nor changes the local shard's arbitrary endpoints. -/
theorem hostCalls_clocks_nodup_of_orderingChannels {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (channels : OrderingChannels witness)
    (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (projected : ((HostCallLedger.activeRows table data).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ((HostCallLedger.calls table data).map HostCallLedger.clock).Nodup := by
  have unique := executionRows_clocks_nodup_of_orderingChannels witness constraints channels
  simp only [executionRows, List.map_append, List.map_map, Function.comp_def] at unique
  have syscalls := (List.nodup_append.mp unique).2.1
  rw [← projected] at syscalls
  simpa only [HostCallLedger.calls, List.map_map, Function.comp_def, ExecutionRow.edge,
    SyscallInstrsChip.statePulledMessage, HostCallLedger.clock, HostCallLedger.call,
    HostCallChip.Inputs.message] using syscalls

/-- Complete channel balance supplies the smaller ordering interface. -/
theorem hostCalls_clocks_nodup {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (projected : ((HostCallLedger.activeRows table data).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real)) :
    ((HostCallLedger.calls table data).map HostCallLedger.clock).Nodup :=
  hostCalls_clocks_nodup_of_orderingChannels witness constraints
    (orderingChannels_of_balanced witness constraints balanced) table data projected

end SP1Clean.Soundness.LocalCore
