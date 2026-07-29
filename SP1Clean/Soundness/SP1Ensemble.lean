import SP1Clean.Soundness.WitnessDecode
import SP1Clean.Soundness.GatedVm.Capstone
import SP1Clean.Model.BalanceBridge
import SP1Clean.Model.InteractionProjection
import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import SP1Clean.FormalModel.Contracts.PublicValues
import Clean.Air.FlatEnsemble

/-! # The supported native SP1 machine as a plain Clean `Ensemble`

This module packages the 25 supported instruction tables and 11 native provider/boundary tables over
the four SP1 buses, together with the pull-final/push-init State verifier. It also proves the
physical-table alignment and typed-interaction partition used by the timed grounding capstone in
`Soundness/AIR.lean`.

**Why a plain `Ensemble`, not a `SoundEnsemble`/`addVm`.** `SoundEnsemble.addTable` demands each
table's `channelsWithGuarantees ⊆ finished`; post-flip every chip's is `[byte, program, memory]`, and
`memoryChannel` can never be a *finished* channel (chips pull-then-push it — the circular VM-channel
shape, `Clean/Air/Vm.lean` top doc). Nor can `addVm` compose it (single-VM-channel engine; State and
Memory are both VM-shaped). A plain `Ensemble` carries no composition obligations — its `Statement`
supplies exactly the constraints + four-bus balance the capstone consumes — and the per-channel
soundness facts are proven separately (byte/program grounding via the finished-channel machinery;
State via the trail; memory `isU64` via the boundary balance). The multi-VM `VmTables` composition
(roadmap W11 path A) was evaluated and **rejected** (consolidation proposal §3.2 — a timeless engine
cannot express memory currency); its de-risk spike `Soundness/StateVm.lean` has been deleted.

The former unconditional Eulerian-trail wrapper was retired. It tried to derive semantic chip Specs
from only `Constraints ∧ BalancedChannels`, even though those Specs require program/provider binding
and the timestamp premise made explicit by `SupportedCoreNativeRelation`. The current capstone proves
ordered State and Memory grounding directly from that honest relation; no witness-dependent semantic
fact is hidden in an ensemble-level `Assumptions := True`. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open Air.Flat
open Circuit
open Sail LeanRV64D LeanRV64D.Functions

-- `Mul` (wired into `sp1Tables`) carries `Fact (2 ^ 24 < p)`; the whole machine is stated under the
-- stronger bound with the project-standard `Fact (2 ^ 17 < p)` derived locally. KoalaBear satisfies it.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-! ## The public input: the committed initial/final machine state

`SP1PublicIO` carries the two State-bus endpoints — the verifier-committed initial `(clk, pc)` and final
`(clk, pc)`. The layout mirrors `Channels.StateMsg` (arity 5: `clk_high, clk_low, pc0, pc1, pc2`) at each
end, so the boundary keys are a direct `.val` projection (`initEntryOf`/`finalEntryOf`). `clk_low` is the
pre-folded low clock (`clk_0_16 + clk_16_24 * 65536`). The structure itself lives on the formal-model
audit surface in `FormalModel/Contracts/PublicValues.lean`. -/

/-- The State-bus key of the public **initial** state — the `.val` list matching `Channels.StateMsg`'s
`toElements` order, i.e. the genesis key the boundary verifier produces under `toAccess`. -/
def initEntryOf (pi : SP1PublicIO (ZMod p)) : List ℕ :=
  [pi.init_clk_high.val, pi.init_clk_low.val, pi.init_pc0.val, pi.init_pc1.val, pi.init_pc2.val]

/-- The State-bus key of the public **final** state. -/
def finalEntryOf (pi : SP1PublicIO (ZMod p)) : List ℕ :=
  [pi.final_clk_high.val, pi.final_clk_low.val, pi.final_pc0.val, pi.final_pc1.val, pi.final_pc2.val]

/-! ## The boundary verifier

`sp1StateVerifier` is the genesis/finalization circuit: a true `pull` of the public **final** state
followed by a true `push` of the public **initial** state (SP1's bus-enforced boundary, `../sp1
record.rs eval_state` `send_state(.,pc_start,1)` + `receive_state(.,next_pc,1)`). Under `toAccess`
these are exactly the `[+1 init, -1 final]` boundary entries `gatedExecution_of_specs_and_balance`'s
`h_bal` assumes (the decode-seam `List.Perm` absorbs the pull-first ordering). The pull/push shape is
Clean-idiomatic — it exposes the loop-closing `[pulled final, pushed init]` pair. No witness cells
(`localLength = 0`); the `Spec` is `True` (the meaning is carried by the trace-level balance). -/
@[circuit_norm]
def sp1StateVerifierMain (pi : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  Channels.stateChannel.pull
    ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩
  Channels.stateChannel.push
    ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩

instance sp1StateVerifierElaborated :
    ElaboratedCircuit (ZMod p) SP1PublicIO unit sp1StateVerifierMain where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [Channels.stateChannel.toRaw]
  channelsLawful := by simp [circuit_norm, sp1StateVerifierMain, Channels.stateChannel]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_channelsWithGuarantees_eq :
    ((sp1StateVerifierElaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [Channels.stateChannel.toRaw] :=
  rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_localLength_eq (x : Var SP1PublicIO (ZMod p)) :
    (sp1StateVerifierElaborated (p := p)).localLength x = 0 := rfl

theorem sp1StateVerifier_soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) sp1StateVerifierMain
      (fun _ _ => True) (fun _ _ _ => True) := by
  circuit_proof_start
  simp [circuit_norm, Channels.stateChannel]

/-- The structural boundary circuit needs no semantic prover assumption. -/
def sp1StateVerifierProverAssumptions (_pi : SP1PublicIO (ZMod p))
    (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop := True

set_option linter.unusedSectionVars false in
theorem sp1StateVerifier_completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) sp1StateVerifierMain
      sp1StateVerifierProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp [circuit_norm, Channels.stateChannel]

/-- The SP1 boundary verifier as a `GeneralFormalCircuit`: pulls the public final state, pushes the
public initial state, and exposes the loop-closing structural State pair. -/
def sp1StateVerifier : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := sp1StateVerifierMain
  elaborated := sp1StateVerifierElaborated
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  ProverAssumptions := sp1StateVerifierProverAssumptions
  soundness := sp1StateVerifier_soundness
  completeness := sp1StateVerifier_completeness
  channelsWithRequirements := []
  requirementsChannelsLawful := fun pi offset => by
    simp only [circuit_norm, sp1StateVerifierMain, Channels.stateChannel]
  exposedChannels := fun pi _ =>
    expose Channels.stateChannel
      [ Channels.stateChannel.pulled ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩,
        Channels.stateChannel.pushed ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩ ]
  exposedChannels_eq := by
    intro pi offset
    rw [Operations.exposedChannelsLawful_expose]
    simp only [sp1StateVerifierMain, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The verifier's exact syntactic State pair, exposed without unfolding its formal-circuit record. -/
theorem sp1StateVerifierMain_stateInteractions (pi : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((sp1StateVerifierMain pi).operations offset).interactionsWith Channels.stateChannel.toRaw =
      [(Channels.stateChannel.pulled
        ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩).toRaw,
       (Channels.stateChannel.pushed
        ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩).toRaw] := by
  simp [sp1StateVerifierMain, circuit_norm]

/-! ## The SP1 machine as a plain Clean `Ensemble` -/

/-- The Clean-table projection of the 25-entry `supportedChips` descriptor. Every chip's verified
`circuit` is wrapped as a Clean AIR `Component` (`⟨chip.circuit⟩`). -/
def sp1Tables : List (Component (ZMod p)) :=
  (supportedChips (p := p)).map (·.table)

/-- Regression guard for the descriptor's Clean-table projection.  `sp1Tables` and `allChipKinds` now
come from the same entries, so semantic and circuit wiring cannot drift as independent lists. -/
theorem sp1Tables_length : (sp1Tables (p := p)).length = 25 := rfl

/-- The 11 in-circuit boundary/provider tables: the 8 byte providers (the five `ByteChip` opcode
tables + the three range tables), the program-ROM provider, and the two memory boundary tables
(init-push + finalize-pull, W11 Phase 4). Every one proves its pushes' channel `Guarantees`
in-circuit (`channelsWithGuarantees = []` for the pushers — providers assume nothing), which is what
grounds the chips' byte/program/memory pulls at the capstone. -/
def sp1ProviderTables : List (Component (ZMod p)) :=
  [⟨ByteChip.U8Range.circuit⟩, ⟨ByteChip.MSB.circuit⟩, ⟨ByteChip.AndByte.circuit⟩,
   ⟨ByteChip.OrByte.circuit⟩, ⟨ByteChip.XorByte.circuit⟩,
   ⟨RangeChip.circuit8⟩, ⟨RangeChip.circuit13⟩, ⟨RangeChip.circuit16⟩,
   ⟨ProgramProviderChip.circuit⟩,
   ⟨MemoryProviderChip.circuit⟩, ⟨MemoryFinalizeChip.circuit⟩]

/-- Regression guard: the boundary/provider table count (8 byte + program + 2 memory). -/
theorem sp1ProviderTables_length : (sp1ProviderTables (p := p)).length = 11 := rfl

/-- Boundary/provider circuits do not declare the State channel.  The public State verifier is the
sole non-instruction contributor to that channel. -/
theorem sp1ProviderTables_stateChannel_not_mem :
    ∀ component ∈ sp1ProviderTables (p := p),
      Channels.stateChannel.toRaw ∉ component.circuit.channels := by
  intro component componentMem
  fin_cases componentMem <;>
    simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, ByteChip.MSB.circuit,
      ByteChip.AndByte.circuit, ByteChip.OrByte.circuit, ByteChip.XorByte.circuit,
      RangeChip.circuit8, RangeChip.circuit13, RangeChip.circuit16,
      RangeChip.circuit,
      ProgramProviderChip.circuit, MemoryProviderChip.circuit, MemoryFinalizeChip.circuit,
      circuit_norm]

/-- **The SP1 machine as a plain Clean `Ensemble`**: the 25 chips + the 11 boundary/provider tables,
the four gated buses (State first — the trail's main channel), and the pull-final/push-init boundary
verifier. Its `Statement` (per-table constraints + per-channel balance) is everything the capstone
consumes; the per-channel soundness facts are proven separately (see the module doc). -/
def sp1Ensemble : Ensemble (ZMod p) SP1PublicIO where
  tables := sp1Tables ++ sp1ProviderTables
  channels :=
    [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
     Channels.programChannel.toRaw, Channels.memoryChannel.toRaw]
  verifier := sp1StateVerifier
  verifier_length_zero := fun _ => rfl

@[circuit_norm] lemma sp1Ensemble_tables :
    (sp1Ensemble (p := p)).tables = sp1Tables ++ sp1ProviderTables := rfl
@[circuit_norm] lemma sp1Ensemble_channels :
    (sp1Ensemble (p := p)).channels =
      [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
       Channels.programChannel.toRaw, Channels.memoryChannel.toRaw] := rfl
@[circuit_norm] lemma sp1Ensemble_verifier :
    (sp1Ensemble (p := p)).verifier = sp1StateVerifier := rfl

/-! ## Physical instruction-table alignment -/

/-- The deterministic decoder's 25 descriptors align positionally with the first 25 physical
witness tables, and both evaluate with the witness's shared prover data.  This is the generic
`InstructionTablesAligned` premise needed to identify decoded-row emissions with Clean's actual table
interactions. -/
theorem witness_instructionTables_aligned
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    InstructionTablesAligned witness.data (supportedChips (p := p))
      (witness.tables.take 25) := by
  unfold InstructionTablesAligned
  rw [List.forall₂_iff_get]
  have tablesLength : witness.tables.length = 36 := by
    rw [← witness.same_length]
    rfl
  constructor
  · simp [supportedChips_length, tablesLength]
  · intro i chipBound tableBound
    have iLt25 : i < 25 := by simpa only [supportedChips_length] using chipBound
    have instructionBound : i < (sp1Tables (p := p)).length := by
      simpa only [sp1Tables_length] using iLt25
    have witnessBound : i < witness.tables.length := by omega
    simp only [List.get_eq_getElem, List.getElem_take]
    constructor
    · have ensembleBound : i < (sp1Ensemble (p := p)).tables.length := by
        rw [sp1Ensemble_tables]
        simp only [List.length_append, sp1Tables_length, sp1ProviderTables_length]
        omega
      have circuitEq := witness.same_circuits i ensembleBound
      change witness.tables[i].component = (supportedChips (p := p))[i].table
      have descriptorEq : (sp1Ensemble (p := p)).tables[i] =
          (supportedChips (p := p))[i].table := by
        change (sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i] = _
        rw [List.getElem_append_left instructionBound]
        simp only [sp1Tables, List.getElem_map]
        rfl
      exact circuitEq.symm.trans descriptorEq
    · change witness.tables[i].data = witness.data
      exact witness.same_data witness.tables[i] (List.getElem_mem witnessBound)

/-- Every canonical decoded instruction row satisfies the constraints of its exact physical Clean
table row.  This is the common starting point for row-local AIR facts; downstream proofs never need
to reopen `same_circuits` or reason positionally about the 36-table witness again. -/
theorem decodedInstructionRow_constraints
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables) :
    decoded.chip.table.operations.ConstraintsHold
      (decoded.environment witness.data) := by
  apply constraints_of_mem_decodeInstructionTables witness.data
    (witness_instructionTables_aligned witness)
  · intro table tableMem
    exact constraints table
      (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take tableMem))
  · exact decodedMem

/-- Every physical table after the stable 25-chip prefix is one of the eleven declared provider or
boundary components. -/
theorem witness_providerTable_component_mem
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    ∀ table ∈ witness.tables.drop 25,
      table.component ∈ sp1ProviderTables (p := p) := by
  intro table tableMem
  have componentMem := List.mem_map_of_mem (f := (·.component)) tableMem
  rw [List.map_drop, witness.tables_map_component] at componentMem
  exact componentMem

/-- The decoder's typed interaction list is exactly the actual interaction list of the first 25
physical witness tables. -/
theorem decodedWitnessInstructionInteractionsWith_eq_tables
    {Message : TypeMap} [ProvableType Message]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (channel : Channel (ZMod p) Message) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables channel =
      (witness.tables.take 25).flatMap (typedTableInteractionsWith · channel) :=
  decodedInstructionInteractionsWith_eq_tables witness.data channel
    (witness_instructionTables_aligned witness)

/-- Exact typed partition of the ensemble interaction list into verifier boundary, decoded
instruction rows, and the eleven provider/boundary tables. -/
theorem typedEnsembleInteractionsWith_partition
    {Message : TypeMap} [ProvableType Message]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (channel : Channel (ZMod p) Message) :
    typedEnsembleInteractionsWith witness channel =
      typedTableInteractionsWith witness.verifierTable channel ++
        decodedWitnessInstructionInteractionsWith witness.data witness.tables channel ++
          (witness.tables.drop 25).flatMap (typedTableInteractionsWith · channel) := by
  rw [decodedWitnessInstructionInteractionsWith_eq_tables]
  unfold typedEnsembleInteractionsWith EnsembleWitness.allTables
  simp only [List.flatMap_cons]
  rw [List.append_assoc, ← List.flatMap_append, List.take_append_drop]

/-- Clean balance transported to the proof-carrying typed interaction view. -/
theorem typedInteractions_balanced
    {Message : TypeMap} [ProvableType Message]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels) (channel : Channel (ZMod p) Message)
    (channelMem : channel.toRaw ∈ (sp1Ensemble (p := p)).channels) :
    BalancedInteractions
      ((typedEnsembleInteractionsWith witness channel).map TypedInteraction.raw) := by
  rw [typedEnsembleInteractionsWith_raw, ← EnsembleWitness.interactionsWith_allTablesWitness]
  exact balanced channel.toRaw channelMem

/-- **The balanced State-trail intermediate spec.** Over the public initial/final state, there is a heterogeneous trace
whose every real row reaches its RISC-V Sail spec and whose `current → next` transitions compose into a
valid execution trail from the public `pc_start` to the public `next_pc` — i.e. a `GatedExecution`
between the public endpoints. -/
def balancedStateTrailSpec : SP1PublicIO (ZMod p) → Prop := fun pi =>
  ∃ rows : List (ChipRow p), GatedExecution rows (initEntryOf pi) (finalEntryOf pi)

/-! ## Frozen Eulerian-path compatibility

The timed-grounding capstone no longer uses this section. It remains as a small compatibility adapter:
given an explicit `DecodedRowsSound` certificate, Clean State balance yields the older
`GatedExecution` trail. The certificate is deliberately not claimed to follow from the raw ensemble
statement; its semantic contents belong to the stronger witness relations in `Soundness/AIR.lean`. -/

/-- Facts needed to adapt a deterministically decoded witness to the frozen Eulerian trail:

* `rows`/`data` — the heterogeneous trace decoded from the witness's 25 **chip** tables
  (`same_circuits` + `valueFromOffset`) and the shared prover data; the 11 boundary/provider tables
  (`sp1ProviderTables`) decode to no `ChipRow` and emit no State interactions;
* `spec_holds` — every decoded row satisfies its semantic chip contract;
* `is_real_binary` — binary gating, from each chip's `is_real · (is_real − 1) = 0` constraint;
* `state_accesses_perm` — the **decode correspondence** the proven balance translation consumes: the
  native State-bus access list (the per-row `stateLookups` aggregate plus the public `±1` boundary) is
  a permutation of the `Interaction.toAccess`-image of the witness's Clean-side State-channel
  interactions. Per row this is `stateLookups_eq_emitted` (`Soundness/StateConsistency.lean`) lifted
  over the table flatMap, plus the verifier's boundary pull/push (`sp1StateVerifierMain` — under
  `toAccess` exactly the `(final, -1)`/`(init, +1)` entries); a permutation because the witness lists
  the verifier's interactions first.

This witness-dependent certificate is an explicit premise, not an `Assumptions := True` consequence
of the raw ensemble. -/
structure DecodedRowsSound (witness : EnsembleWitness (sp1Ensemble (p := p))) : Prop where
  spec_holds : ∀ r ∈ decodedChipRows witness.data witness.tables, r.chipSpec witness.data
  is_real_binary : ∀ r ∈ (decodedChipRows witness.data witness.tables).map ChipRow.view,
    r.is_real = 0 ∨ r.is_real = 1
  state_accesses_perm :
      (aggregateChipRows ((decodedChipRows witness.data witness.tables).map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf witness.publicInput, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf witness.publicInput, (-1 : ℤ))]).Perm
        ((witness.interactionsWith Channels.stateChannel.toRaw).map Interaction.toAccess)

/-- **W1a, proven: Clean State-channel balance ⇒ native gated State-bus balance.** From Clean's
`BalancedInteractions` over the (single-channel) State interactions — one instantiation of
`witness.BalancedChannels` — and the decode correspondence (`DecodedRowsSound.state_accesses_perm`),
conclude the native `isConsistentBalanced` of the decoded access list: exactly the `h_bal` hypothesis
of `gatedExecution_of_specs_and_balance`. The field → ℤ core is
`isConsistentBalanced_of_balancedInteractions` (`Model/BalanceBridge.lean`); the `{-1, 0, 1}`
multiplicity bound is native — `±is_real.val` with `is_real` binary (`stateLookups_mult_binary`) plus
the constant-`±1` boundary. Axiom-clean (clean-3). -/
theorem sp1_state_balance_of_balancedInteractions
    (pi : SP1PublicIO (ZMod p)) (rows : List (ChipRow p))
    (hbin : ∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1)
    (interactions : List (Interaction (ZMod p)))
    (h_channel : ∀ i ∈ interactions, i.channel = Channels.stateChannel.toRaw)
    (h_balanced : BalancedInteractions interactions)
    (h_perm : (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf pi, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf pi, (-1 : ℤ))]).Perm
        (interactions.map Interaction.toAccess)) :
    isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf pi, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf pi, (-1 : ℤ))]) := by
  refine isConsistentBalanced_of_balancedInteractions _ interactions
    Channels.stateChannel.toRaw h_channel h_perm h_balanced ?_
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · -- chip-row contributions carry `±is_real.val` with `is_real` binary
    obtain ⟨v, hv, hav⟩ := List.mem_flatMap.mp ha
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    exact stateLookups_mult_binary hp v (hbin v hv) a hav
  · -- the two constant-`±1` boundary entries
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [multOf]

/-- Assemble an explicit decoded-row certificate and Clean State balance into the three premises of
the frozen `gatedExecution_of_specs_and_balance` theorem. -/
theorem sp1_gatedExecution_prereqs (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (decodedSound : DecodedRowsSound witness) (hB : witness.BalancedChannels) :
    ∃ (rows : List (ChipRow p)) (data : ProverData (ZMod p)),
      (∀ r ∈ rows, r.chipSpec data) ∧
      (∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1) ∧
      isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf witness.publicInput, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf witness.publicInput, (-1 : ℤ))]) := by
  let rows := decodedChipRows witness.data witness.tables
  obtain ⟨h_spec, hbin, h_corr⟩ := decodedSound
  -- instantiate the balanced channels at the State channel (the ensemble channel-list head)
  have h_balanced : BalancedInteractions
      (witness.interactionsWith Channels.stateChannel.toRaw) := by
    rw [← EnsembleWitness.interactionsWith_allTablesWitness]
    exact hB Channels.stateChannel.toRaw (List.mem_cons_self ..)
  exact ⟨rows, witness.data, h_spec, hbin,
    sp1_state_balance_of_balancedInteractions witness.publicInput rows hbin _
      (fun i hi => EnsembleWitness.channel_eq_of_mem_interactionsWith hi) h_balanced h_corr⟩

/-- The frozen Eulerian-path compatibility result, with its semantic decode facts explicit.

This is intentionally not an `Ensemble.Soundness` theorem: `DecodedRowsSound` is witness-dependent
and does not follow from the raw ensemble algebra without the semantic provider/timestamp premises
used by the current timed-grounding capstone. -/
theorem balanced_state_trail_of_decoded_rows_sound
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (decodedSound : DecodedRowsSound witness) (balanced : witness.BalancedChannels) :
    balancedStateTrailSpec witness.publicInput := by
  obtain ⟨rows, data, spec, binary, stateBalance⟩ :=
    sp1_gatedExecution_prereqs witness decodedSound balanced
  exact ⟨rows, gatedExecution_of_specs_and_balance rows data
    (initEntryOf witness.publicInput) (finalEntryOf witness.publicInput)
    spec binary stateBalance⟩

end SP1Clean.Soundness
