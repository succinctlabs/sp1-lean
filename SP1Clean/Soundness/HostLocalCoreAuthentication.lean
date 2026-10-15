import SP1Clean.Soundness.HostLocalCoreLedger
import ToClean.Air.Authentication

/-! # Authentication on fresh host protocols

The complete retained local prefix is silent on a fresh protocol, and the caller checks wrapper
silence. Only the actual appended tables can source its records. Their component-local source
proofs and the original count-bounded balance authenticate all unit pulls, without any caller
ledger equality or physical-table alignment premise.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

theorem authenticated_auxiliary_pull {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}
    {Record : TypeMap} [ProvableType Record]
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (channel : Channel (ZMod p) Record)
    (registered : channel.toRaw ∈ (baseEnsemble image source auxiliary channels names).channels)
    (fresh : channel.toRaw ∉ (LocalCore.ensemble (p := p) image source).channels)
    (permission : channel.toRaw ≠ WritePermissionProvider.channel.toRaw)
    (wrapper : channel.toRaw ∉ (HostCallLedger.producer (p := p)).circuit.channels)
    (property : Record (ZMod p) → Prop)
    (sources : ∀ table ∈ auxiliaryTables witness, table.Authenticates witness.data channel property)
    (balanced : witness.BalancedChannel channel.toRaw)
    (record : Record (ZMod p))
    (member : channel.pulledValue record ∈ witness.interactionsWith channel.toRaw) : property record := by
  have silent : (hostCallTable witness).interactionsWith witness.data channel.toRaw = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    rwa [hostCallTable_component]
  have ledger := interactions_split_new witness channel.toRaw registered fresh permission
  rw [silent, List.nil_append] at ledger
  change BalancedInteractions (witness.interactionsWith channel.toRaw) at balanced
  rw [ledger] at balanced member
  exact authenticated_pull_of_tables (auxiliaryTables witness) witness.data channel property sources balanced record member

end SP1Clean.Soundness.HostLocalCore
