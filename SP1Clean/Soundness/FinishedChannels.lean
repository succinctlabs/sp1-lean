import SP1Clean.Soundness.SP1Ensemble
import Clean.Air.OrderedChannel

/-! # Finished-channel grounding over the capstone ensemble (W11 Phase 5.4; SC Phase 2a — byte-only)

The byte pull-guarantee grounding for `sp1Ensemble`: from a constraint-satisfying, channel-balanced
ensemble witness, **every** table's `ChannelGuarantees` on `byteChannel` holds — i.e. byte is a
*finished* channel of the capstone. **SC Phase 2a: program is no longer finished here.** After the flip
`programChannel` carries the semantic `ProgTruth` guarantee with `Owed := RowSpec ⇏ ProgTruth`, so it is
not `Consistent`/`Normal` and cannot be grounded by `guarantees_of_requirements_append`; its
`decodedInROM` half is grounded by the timed-channel engine (Phase 5), exactly like `stateChannel`'s
`StateTruth`. Byte is now the sole finished bus.

The engine is Clean's `guarantees_of_requirements_append` (`Clean/Air/OrderedChannel.lean`), applied
per channel to the partition *consumers* (`verifierTable :: witness.tables.take 25` — the boundary
verifier plus the 25 chips, none of which lists byte/program in its `channelsWithRequirements`) vs
*providers* (`witness.tables.drop 25` — the 11 boundary/provider tables, whose pushes prove their
channel `Requirements` in-circuit from constraints alone, via `Table.weakSoundness` with trivial
`Assumptions` and empty `channelsWithGuarantees`; `MemoryFinalizeChip` instead has empty
`channelsWithRequirements`, so its requirements are vacuous). The provider tables' own byte/program
guarantees are vacuous (`Table.guarantees_of_not_mem` — neither channel is in any provider's
`channelsWithGuarantees`), which covers all of `witness.allTables`. -/

namespace SP1Clean.Soundness

open SP1Clean
open Air.Flat
open Circuit
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

-- Same bound as `sp1Ensemble` (`Mul`/`DivRem` carry `Fact (2 ^ 24 < p)`), with the project-standard
-- `Fact (2 ^ 17 < p)` derived locally. KoalaBear satisfies it.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-! ## Channel and channel-list facts -/

/-- The boundary verifier's requirement channels — State only. -/
private lemma verifierTable_cwr (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    witness.verifierTable.component.circuit.channelsWithRequirements =
      [stateChannel.toRaw] := rfl

/-- All 25 chips share the post-flip requirement channels `[state, memory]` (one `rfl` over the
mapped list; cheap lazy projection, no circuit bodies unfolded). -/
private lemma sp1Tables_cwr_eq :
    (sp1Tables (p := p)).map (·.circuit.channelsWithRequirements) =
      List.replicate 25 [stateChannel.toRaw, memoryChannel.toRaw] := rfl

private lemma sp1Tables_cwr : ∀ c ∈ sp1Tables (p := p),
    c.circuit.channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := by
  intro c hc
  have h := List.mem_map_of_mem
    (f := fun c : Component (ZMod p) => c.circuit.channelsWithRequirements) hc
  rw [sp1Tables_cwr_eq] at h
  exact List.eq_of_mem_replicate h

/-- The 11 provider tables' (guarantee, requirement) channel pairs, pinned by one `rfl`: the 8 byte
providers push-prove byte, the program provider push-proves program, the memory boundary provider
push-proves memory, and the finalize table pulls memory owing nothing. -/
private lemma providers_channels_eq :
    (sp1ProviderTables (p := p)).map
      (fun c => (c.circuit.channelsWithGuarantees, c.circuit.channelsWithRequirements)) =
    [([], [byteChannel.toRaw]), ([], [byteChannel.toRaw]), ([], [byteChannel.toRaw]),
     ([], [byteChannel.toRaw]), ([], [byteChannel.toRaw]), ([], [byteChannel.toRaw]),
     ([], [byteChannel.toRaw]), ([], [byteChannel.toRaw]), ([], [programChannel.toRaw]),
     ([], [memoryChannel.toRaw]), ([memoryChannel.toRaw], [])] := rfl

/-- Every provider circuit's `Assumptions` is the structure default `fun _ _ => True`. -/
private lemma providers_assumptions :
    ∀ c ∈ sp1ProviderTables (p := p), ∀ env : Environment (ZMod p), c.Assumptions env := by
  simp only [sp1ProviderTables, List.forall_mem_cons]
  exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ => trivial, List.forall_mem_nil _⟩

/-! ## Positional component identification

`witness.tables_map_component` pins the 36 abstract witness tables to the concrete
`sp1Tables ++ sp1ProviderTables`; `take 25`/`drop 25` splits it into the chip and provider blocks. -/

private lemma mem_take25_component (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    ∀ t ∈ witness.tables.take 25, t.component ∈ sp1Tables (p := p) := by
  intro t ht
  have h := List.mem_map_of_mem (f := (·.component)) ht
  rw [List.map_take, witness.tables_map_component] at h
  exact h

private lemma mem_drop25_component (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    ∀ t ∈ witness.tables.drop 25, t.component ∈ sp1ProviderTables (p := p) := by
  intro t ht
  have h := List.mem_map_of_mem (f := (·.component)) ht
  rw [List.map_drop, witness.tables_map_component] at h
  exact h

/-! ## The provider tables prove their requirements in-circuit -/

/-- **Every provider table proves its `ChannelRequirements` on every channel from its constraints
alone.** The 10 pushers have trivial `Assumptions` and empty `channelsWithGuarantees`, so
`Table.weakSoundness` yields their full `Requirements`; `MemoryFinalizeChip` has empty
`channelsWithRequirements`, so `Table.requirements_of_not_mem_of_constraints` applies. -/
private lemma provider_requirements (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) :
    ∀ t ∈ witness.tables.drop 25, ∀ channel : RawChannel (ZMod p),
      t.ChannelRequirements channel := by
  intro t ht channel
  have hc : t.Constraints := hC _ (witness.mem_allTables_of_mem_tables (List.mem_of_mem_drop ht))
  have hcomp := mem_drop25_component witness _ ht
  have hA : t.Assumptions := fun row _ => providers_assumptions _ hcomp _
  have hpair := List.mem_map_of_mem
    (f := fun c : Component (ZMod p) =>
      (c.circuit.channelsWithGuarantees, c.circuit.channelsWithRequirements)) hcomp
  rw [providers_channels_eq] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  have hcase : t.component.circuit.channelsWithGuarantees = [] ∨
      t.component.circuit.channelsWithRequirements = [] := by tauto
  rcases hcase with hg | hr
  · -- pusher: no guarantees owed anywhere ⟹ `weakSoundness` gives full `Requirements`
    have hg' : t.Guarantees := by
      rw [Table.guarantees_iff_channelGuarantees]
      intro c hcmem
      simp only [Table.channelsWithGuarantees, hg] at hcmem
      simp at hcmem
    exact t.channelRequirements_of_requirements (Table.weakSoundness hA hc hg').2
  · -- finalize table: no requirement channels at all
    refine t.requirements_of_not_mem_of_constraints hc ?_
    simp [Table.channelsWithRequirements, hr]

/-! ## The consumers' pull guarantees, per channel -/

/-- **The engine application.** For any consistent ensemble channel outside the chips'
requirement set `[state, memory]` — i.e. byte or program — the verifier and all 25 chip tables
carry the channel's `Guarantees`: `guarantees_of_requirements_append` on the consumer/provider
partition, with partial balance from the witness's `BalancedChannels` (the partition is a
permutation of `allTables`, so `partialBalancedChannel_of_sublist` transports it). -/
private lemma consumer_guarantees (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) (hB : witness.BalancedChannels)
    (channel : RawChannel (ZMod p)) [channel.Consistent]
    (hchmem : channel ∈ (sp1Ensemble (p := p)).channels)
    (hnr : channel ∉ [stateChannel.toRaw, memoryChannel.toRaw]) :
    ∀ table ∈ witness.verifierTable :: witness.tables.take 25,
      table.ChannelGuarantees channel := by
  have hdata_ts : ∀ t ∈ witness.verifierTable :: witness.tables.take 25,
      t.data = witness.data := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · exact witness.same_data _ (List.mem_of_mem_take ht)
  have hdata_ss : ∀ t ∈ witness.tables.drop 25, t.data = witness.data :=
    fun t ht => witness.same_data _ (List.mem_of_mem_drop ht)
  refine guarantees_of_requirements_append
    (ts := ⟨witness.verifierTable :: witness.tables.take 25, witness.data, hdata_ts⟩)
    (ss := ⟨witness.tables.drop 25, witness.data, hdata_ss⟩) rfl ?_ ?_ ?_
    (fun t ht => provider_requirements witness hC t ht channel)
  · -- consumer constraints
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hC _ witness.mem_allTables_verifierTable
    · exact hC _ (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take ht))
  · -- no consumer lists the channel in its requirements
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [verifierTable_cwr]
      simp [hnr.1]
    · rw [sp1Tables_cwr _ (mem_take25_component witness _ ht)]
      simp [hnr.1, hnr.2]
  · -- partial balance: the partition is a permutation of `allTables`
    refine partialBalancedChannel_of_sublist
      (Ensemble.partialBalancedChannel_of_balancedChannel channel (hB channel hchmem))
      ⟨[], ?_, by simp, by simp⟩
    rw [List.append_nil, Tables.append_tables]
    show (witness.verifierTable :: witness.tables).Perm _
    rw [List.cons_append, List.take_append_drop]

/-! ## The headline theorem -/

/-- **Byte finished-channel grounding (W11 P5.4; SC Phase 2a — byte-only).** From a constraint-satisfying,
channel-balanced `sp1Ensemble` witness, every table — verifier, the 25 chips, and the 11 boundary/provider
tables — carries the byte-channel `Guarantees`. For the verifier and chips this is the balance-driven
engine (`consumer_guarantees`); for the provider tables it is vacuous (byte appears in no provider's
`channelsWithGuarantees`). **Program is no longer grounded here:** after the SC Phase 2a flip
`programChannel` carries the semantic `ProgTruth` guarantee with `Owed := RowSpec ⇏ ProgTruth`, so it is
NOT `Consistent`/`Normal` and cannot be finished by `guarantees_of_requirements_append`; its
`decodedInROM` half is grounded by the timed-channel engine (Phase 5), exactly like `stateChannel`'s
`StateTruth`. Byte stays the sole finished bus. This theorem is a leaf (nothing imports it). -/
theorem sp1_finishedChannel_guarantees (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) (hB : witness.BalancedChannels) :
    ∀ table ∈ witness.allTables,
      table.ChannelGuarantees Channels.byteChannel.toRaw := by
  have hgB := consumer_guarantees witness hC hB byteChannel.toRaw
    (by simp [sp1Ensemble_channels])
    (by simp [Channels.byteChannel_eq_stateChannel_false,
      Channels.byteChannel_eq_memoryChannel_false])
  rw [EnsembleWitness.forall_mem_allTables_iff]
  refine ⟨hgB _ List.mem_cons_self, ?_⟩
  intro table htable
  rw [← List.take_append_drop 25 witness.tables] at htable
  rcases List.mem_append.mp htable with h | h
  · exact hgB _ (List.mem_cons_of_mem _ h)
  · -- provider tables: byte guarantee vacuous (byte is in no provider's `channelsWithGuarantees`)
    have hpair := List.mem_map_of_mem
      (f := fun c : Component (ZMod p) =>
        (c.circuit.channelsWithGuarantees, c.circuit.channelsWithRequirements))
      (mem_drop25_component witness _ h)
    rw [providers_channels_eq] at hpair
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
    have hcwg : table.component.circuit.channelsWithGuarantees = [] ∨
        table.component.circuit.channelsWithGuarantees = [memoryChannel.toRaw] := by tauto
    refine table.guarantees_of_not_mem ?_
    rcases hcwg with hg | hg <;>
      simp only [Table.channelsWithGuarantees, hg] <;>
      simp [Channels.byteChannel_eq_memoryChannel_false]

end SP1Clean.Soundness
