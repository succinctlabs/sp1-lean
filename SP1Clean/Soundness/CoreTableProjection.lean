import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.CoreExecutionRow
import SP1Clean.Soundness.MemoryFrontier

/-! # Shared physical ledger projections

These component and list lemmas retain physical occurrences and shared prover data independently
of the enclosing ensemble's source policy. Both boot and local adapters use them; ordering itself
remains the common `StateChronology` argument.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

omit [Fact (2 ^ 24 < p)] in
theorem typedTableInteractions_nil {Message : TypeMap} [ProvableType Message]
    (table : Table (ZMod p)) (data : ProverData (ZMod p)) (channel : Channel (ZMod p) Message)
    (silent : channel.toRaw ∉ table.component.circuit.channels) :
    typedTableInteractionsWith table data channel = [] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw, List.map_nil]
  exact table.interactionsWith_nil_of_channel_not_mem silent

/-- Every component in the fixed Byte/Range batch is silent on other channels. -/
theorem byteProvider_channel_silent (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23)
    (channel : RawChannel (ZMod p)) (different : channel ≠ byteChannel.toRaw) :
    channel ∉ component.circuit.channels := by
  rw [sp1ProviderTables, ← List.map_take] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have prefixEq : ProviderTableId.all.take 23 =
      ByteProviderId.all.map .byte ++ (List.finRange 17).map .range := by decide
  rw [prefixEq] at idMem
  rcases List.mem_append.mp idMem with byte | range
  · obtain ⟨provider, _, rfl⟩ := List.mem_map.mp byte
    cases provider <;> change channel ∉ [byteChannel.toRaw]
    all_goals simpa
  · obtain ⟨width, _, rfl⟩ := List.mem_map.mp range
    change channel ∉ [byteChannel.toRaw]
    simpa

theorem flatMap_split {α β : Type*} (items : List α) (f : α → List β) (start count : ℕ) :
    (items.drop start).flatMap f = ((items.drop start).take count).flatMap f ++
      (items.drop (start + count)).flatMap f := by
  have split := congrArg (List.flatMap f) (List.take_append_drop count (items.drop start))
  simpa only [List.flatMap_append, List.drop_drop, Nat.add_comm] using split.symm

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem flatMap_filter_inactive {α β : Type*} (rows : List α) (keep : α → Bool)
    (f : α → List β) (inactive : ∀ row ∈ rows, keep row = false → f row = []) :
    (rows.filter keep).flatMap f = rows.flatMap f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have rest := ih (fun item member => inactive item (List.mem_cons_of_mem _ member))
    cases active : keep row
    · simp [active, rest, inactive row List.mem_cons_self active]
    · simp [active, rest]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem pushesAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pushesAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (·.memPushes)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pushesAt, Multiset.filter_coe, rowPushesAt]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem pullsAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pullsAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (fun row => row.memPulls.map Prod.fst)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pullsAt, Multiset.filter_coe, rowPullsAt]

/-- Preserving the evaluated State ledger preserves both public endpoints, occurrence for occurrence. -/
theorem verifier_state_interactions_of_values {assembly : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness assembly)
    (same : assembly.verifierOperations.interactionValuesWith stateChannel.toRaw
        (Environment.fromInput witness.publicInput witness.data) =
      sp1StateVerifierProgram.circuitOperations.interactionValuesWith stateChannel.toRaw
        (Environment.fromInput witness.publicInput witness.data)) :
    typedInteractionValuesWith assembly.verifierOperations stateChannel
        (Environment.fromInput witness.publicInput witness.data) =
      [TypedInteraction.pulledIfValue stateChannel 1 (finalBoundaryStateMessage witness.publicInput),
       TypedInteraction.pushedIfValue stateChannel 1 (initialBoundaryStateMessage witness.publicInput)] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, same, ← typedInteractionValuesWith_raw,
    stateVerifier_stateInteractions]
  rfl

end SP1Clean.Soundness.NativeCore
