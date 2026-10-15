import SP1Clean.Soundness.HostHintReadExecutionPath

/-! # Protected instruction memory throughout the installed mixed replay

The installed AIR supplies a complete semantic path, its ordinary write permissions and checked
source. The circuit-independent path induction then supplies configuration, protected-byte and
ROM preservation at every prefix, and actual Sail fetch agreement at every executed position.
The final boundary has no next-fetch obligation. Existing preservation statements are retained;
resource bounds and complete outgoing-boundary authentication remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance romLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance romLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

private theorem source_valid
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ExecutionSourceValid image source := by
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness
    (source_interface source.host.io.hints) constraints balanced
  exact (LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte).2.1

/-- Raw installed AIR premises discharge the independent path's source and permission hypotheses. -/
theorem GroundingCarrier.frame_prefix (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cut : ℕ} {target : ExecutionState}
    (replay : carrier.pairedTrajectory valid cut = some target) :
    Target.SailConfigured target.sail ∧ Target.RomLoaded (image.toGuestProgram valid) target.sail ∧
      ∀ address, image.readOnly address = true →
        target.sail.mem.get? address = source.sail.realize.mem.get? address := by
  have checked := source_valid witness constraints balanced
  obtain ⟨_, path, _⟩ := carrier.execution valid constraints balanced
  exact path.frame_prefix valid (carrier.writesPermitted valid constraints balanced)
    (fun _ selected => selected) checked.configured checked.romLoaded replay

/-- Every successful prefix of the installed replay preserves each protected byte exactly. -/
theorem GroundingCarrier.readOnly_prefix (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cut : ℕ} {target : ExecutionState}
    (replay : carrier.pairedTrajectory valid cut = some target)
    (address : ℕ) (readOnly : image.readOnly address = true) :
    target.sail.mem.get? address = source.sail.realize.mem.get? address :=
  (carrier.frame_prefix valid constraints balanced replay).2.2 address readOnly

/-- The incoming boundary's authenticated ROM survives every prefix of the installed replay. -/
theorem GroundingCarrier.romLoaded_prefix (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {cut : ℕ} {target : ExecutionState}
    (replay : carrier.pairedTrajectory valid cut = some target) :
    Target.RomLoaded (image.toGuestProgram valid) target.sail :=
  (carrier.frame_prefix valid constraints balanced replay).2.1

/-- Every actual event of the installed tape fetches its committed word through official Sail. -/
theorem GroundingCarrier.fetch_at (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (cut : ℕ) (active : cut < carrier.events.length) :
    ∃ current pc word, carrier.pairedTrajectory valid cut = some current ∧
      current.sail.regs.get? LeanRV64D.Defs.Register.PC = some pc ∧
      (image.toGuestProgram valid).fetchWord pc = some word ∧
      (LeanRV64D.Functions.fetch ()).run current.sail =
        .ok (LeanRV64D.Defs.FetchResult.F_Base word) current.sail := by
  have checked := source_valid witness constraints balanced
  obtain ⟨_, path, _⟩ := carrier.execution valid constraints balanced
  exact path.fetch_at valid (carrier.writesPermitted valid constraints balanced)
    (fun _ selected => selected) checked.configured checked.romLoaded cut active

end SP1Clean.Soundness.HostHintReadCPU
