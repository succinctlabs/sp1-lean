import SP1Clean.Soundness.ChipRegistry
import SP1Clean.Soundness.GatedVm.Capstone
import SP1Clean.Model.BalanceBridge
import SP1Clean.Model.InteractionProjection
import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import Clean.Air.FlatEnsemble

/-! # SP1 as a plain Clean `Ensemble` — the final, gated whole-machine capstone (W11 Phase 5)

The whole-machine soundness object for SP1, re-based from the bespoke `GatedVm` data structure onto
Clean's native `Air.Flat.Ensemble`: 25 chip tables + 11 in-circuit boundary/provider tables over the
four buses, with the pull-final/push-init State boundary verifier. From the ensemble `Statement`
(per-table constraints + balanced channels) over the public initial/final machine state, there is a
valid RISC-V-Sail execution trail from `pc_start` to `next_pc`, with every real instruction
Sail-correct — the Eulerian-trail machinery (`GatedVm/{Chain,StateBridge,Capstone,SailDispatch}.lean`,
the `GatedVm` *namespace*) is unchanged; only the ensemble packaging is now Clean-native.

**Why a plain `Ensemble`, not a `SoundEnsemble`/`addVm`.** `SoundEnsemble.addTable` demands each
table's `channelsWithGuarantees ⊆ finished`; post-flip every chip's is `[byte, program, memory]`, and
`memoryChannel` can never be a *finished* channel (chips pull-then-push it — the circular VM-channel
shape, `Clean/Air/Vm.lean` top doc). Nor can `addVm` compose it (single-VM-channel engine; State and
Memory are both VM-shaped). A plain `Ensemble` carries no composition obligations — its `Statement`
supplies exactly the constraints + four-bus balance the capstone consumes — and the per-channel
soundness facts are proven separately (byte/program grounding via the finished-channel machinery;
State via the trail; memory `isU64` via the boundary balance). The `sp1StateVmEnsemble` `addVm`
composition stays parked in `Soundness/StateVm.lean` pending the multi-VM `VmTables` generalization
(roadmap W11 path A).

**Trust boundary / residue.** The `soundness` *assembly* is sorry-free: it threads the two ensemble
prerequisites into the gated capstone. The bridge from the Clean ensemble `Statement` to those
prerequisites, `sp1_gatedExecution_prereqs`, is itself a **proven** assembly of two named pieces:
* (a) **proven (W1a)** — `sp1_state_balance_of_balancedInteractions`: the Clean `BalancedInteractions`
  → native `isConsistentBalanced` State-bus translation, via the generic `toAccess` adapter
  `isConsistentBalanced_of_balancedInteractions` (`Model/BalanceBridge.lean`) + the native
  `{-1, 0, 1}` multiplicity bound (`stateLookups_mult_binary`);
* (b)+(c) **the seam (W1b/W1c, the sole residual `sorry`)** — `sp1_witness_decode`: the 36-table
  witness → `ChipRow` decode bundle `SP1WitnessDecode`, carrying per-table `Component.weakSoundness`
  for the 25 chips (the 11 provider tables decode to no `ChipRow` and contribute no State
  interactions), each chip's `isU64` operand-`Assumptions` recovery from the memory-bus balance
  against the init/finalize boundary tables (`Soundness/MemoryIsU64.lean`,
  `memBalanceHyps_of_boundary`), the byte/program pull guarantees from the finished-channel grounding,
  the binary gating, and the State-bus decode correspondence (`stateLookups_eq_emitted` lifted over
  the table flatMap + the verifier boundary) that (a) consumes.
Closing the seam yields a fully axiom-clean `sp1FormalEnsemble` with no further structural work. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open Air.Flat
open Circuit
open Sail LeanRV64D LeanRV64D.Functions

-- `Mul` (wired into `sp1Tables`) carries `Fact (2 ^ 24 < p)`; the whole machine is stated under the
-- stronger bound with the project-standard `Fact (2 ^ 17 < p)` derived locally. KoalaBear satisfies it.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## The public input: the committed initial/final machine state

`SP1PublicIO` carries the two State-bus endpoints — the verifier-committed initial `(clk, pc)` and final
`(clk, pc)`. The layout mirrors `Channels.StateMsg` (arity 5: `clk_high, clk_low, pc0, pc1, pc2`) at each
end, so the boundary keys are a direct `.val` projection (`initEntryOf`/`finalEntryOf`). `clk_low` is the
pre-folded low clock (`clk_0_16 + clk_16_24 * 65536`). -/
structure SP1PublicIO (F : Type) where
  init_clk_high : F
  init_clk_low : F
  init_pc0 : F
  init_pc1 : F
  init_pc2 : F
  final_clk_high : F
  final_clk_low : F
  final_pc0 : F
  final_pc1 : F
  final_pc2 : F
deriving ProvableStruct

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
Clean-idiomatic — it exposes the loop-closing `[pulled final, pushed init]` pair `VmTables` wants, so
the same verifier serves `sp1StateVmSpike` (`Soundness/StateVm.lean`). No witness cells
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
  -- SC Phase 2c: the boundary pull of the **final** state receives `StateTruth` (the semantic capstone
  -- conclusion — grounded by the engine, honestly supplied on the completeness side); so `stateChannel`
  -- joins `channelsWithGuarantees`.
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

/-- SC Phase 2c: the honest prover supplies the final-state pull's `StateTruth` — the real terminal state
of the committed program's execution (engine-grounded on the soundness side; the semantic capstone
conclusion). -/
def sp1StateVerifierProverAssumptions (pi : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  SP1Clean.Semantics.StateTruth
    (⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩ :
      Channels.StateMsg (ZMod p)) data

set_option linter.unusedSectionVars false in
theorem sp1StateVerifier_completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) sp1StateVerifierMain
      sp1StateVerifierProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [circuit_norm, Channels.stateChannel, sp1StateVerifierProverAssumptions] at h_assumptions ⊢
  exact h_assumptions

/-- The SP1 boundary verifier as a `GeneralFormalCircuit`: pulls the public final state (receiving its
`StateTruth`), pushes the public initial state, exposing the loop-closing `[pulled final, pushed init]`
State pair. -/
def sp1StateVerifier : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := sp1StateVerifierMain
  elaborated := sp1StateVerifierElaborated
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  ProverAssumptions := sp1StateVerifierProverAssumptions
  soundness := sp1StateVerifier_soundness
  completeness := sp1StateVerifier_completeness
  channelsWithRequirements := [Channels.stateChannel.toRaw]
  exposedChannels := fun pi _ =>
    Channels.stateChannel.expose
      [ Channels.stateChannel.pulled ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩,
        Channels.stateChannel.pushed ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩ ]
  exposedChannels_eq := by
    intro pi offset
    simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
      List.map_cons, List.map_nil]
    simp [circuit_norm, sp1StateVerifierMain, VmChannel.pulled, VmChannel.pushed]

/-! ## The SP1 machine as a plain Clean `Ensemble` -/

/-- The 25 capstone-wired chips, each a `GeneralFormalCircuit` wrapped as a Clean AIR `Component`
(`⟨chip.circuit⟩`). Order mirrors `ChipRegistry.allChipKinds`. Every chip's `circuit` is `sorry`-free
in **both** soundness and completeness, so `#print axioms` on this `def` shows **no** `sorryAx` (only
`bv_decide`'s `ofReduceBool`/`trustCompiler` ride along, via `Mul`/`Bitwise` soundness). The capstone's
lone `sorryAx` enters separately, through the decode-seam premise `sp1_witness_decode`. -/
def sp1Tables : List (Component (ZMod p)) :=
  [⟨AddChip.circuit⟩, ⟨AddiChip.circuit⟩, ⟨AddwChip.circuit⟩, ⟨SubChip.circuit⟩, ⟨SubwChip.circuit⟩,
   ⟨BitwiseChip.circuit⟩, ⟨LtChip.circuit⟩, ⟨ShiftLeftChip.circuit⟩, ⟨ShiftRightChip.circuit⟩,
   ⟨JalChip.circuit⟩, ⟨JalrChip.circuit⟩, ⟨BranchChip.circuit⟩, ⟨UTypeChip.circuit⟩,
   ⟨LoadByteChip.circuit⟩, ⟨LoadHalfChip.circuit⟩, ⟨LoadWordChip.circuit⟩, ⟨LoadDoubleChip.circuit⟩,
   ⟨LoadX0Chip.circuit⟩, ⟨StoreByteChip.circuit⟩, ⟨StoreHalfChip.circuit⟩, ⟨StoreWordChip.circuit⟩,
   ⟨StoreDoubleChip.circuit⟩, ⟨MulChip.circuit⟩, ⟨DivRemChip.circuit⟩, ⟨AluX0Chip.circuit⟩]

/-- Regression guard: the capstone-wired table count matches `allChipKinds_length` (25). A chip is
fully wired only when it appears in **both** `allChipKinds` and `sp1Tables` — this `rfl` plus
`allChipKinds_length` keeps the two lists from drifting apart silently (as happened when `DivRem`
was registered but not wired, 2026-06). -/
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

/-- Scaffold ensemble assumptions — `True`. The chip operand `isU64` assumptions are not expressible on
`SP1PublicIO`; they are recovered per-witness from the memory-bus balance inside the decode seam
`sp1_witness_decode` (W1c). -/
def sp1Assumptions : SP1PublicIO (ZMod p) → Prop := fun _ => True

/-- **The meaningful SP1 spec.** Over the public initial/final state, there is a heterogeneous trace
whose every real row reaches its RISC-V Sail spec and whose `current → next` transitions compose into a
valid execution trail from the public `pc_start` to the public `next_pc` — i.e. a `GatedExecution`
between the public endpoints. -/
def sp1Spec : SP1PublicIO (ZMod p) → Prop := fun pi =>
  ∃ rows : List (ChipRow p), GatedExecution rows (initEntryOf pi) (finalEntryOf pi)

/-! ## The capstone premise, split: the decode seam (W1b/W1c) + the proven balance translation (W1a)

`sp1_gatedExecution_prereqs` used to be one monolithic `sorry`. It is now a **proven** assembly of
* `sp1_witness_decode` — the **W1b/W1c decode seam**, the sole remaining `sorry`: the 36-table
  witness → `ChipRow` decode bundle `SP1WitnessDecode`, and
* `sp1_state_balance_of_balancedInteractions` — **W1a, proven, axiom-clean**: Clean
  `BalancedInteractions` on the State channel ⇒ native `isConsistentBalanced` of the decoded access
  list, through the generic adapter in `Model/BalanceBridge.lean`. -/

/-- **The witness → trace decode bundle (the W1b/W1c seam).** Everything about a constraint-satisfying,
channel-balanced witness that requires *decoding the tables into `ChipRow`s*:

* `rows`/`data` — the heterogeneous trace decoded from the witness's 25 **chip** tables
  (`same_circuits` + `valueFromOffset`) and the shared prover data; the 11 boundary/provider tables
  (`sp1ProviderTables`) decode to no `ChipRow` and emit no State interactions;
* `spec_holds` — per-row chip `Spec`, from per-table `Component.weakSoundness` under
  `witness.Constraints`, with each chip's byte/program pull guarantees grounded against the provider
  tables and its `isU64` operand `Assumptions` recovered from the memory-bus balance against the
  init/finalize boundary (`Soundness/MemoryIsU64.lean`, `memBalanceHyps_of_boundary`, W1c);
* `is_real_binary` — binary gating, from each chip's `is_real · (is_real − 1) = 0` constraint;
* `state_accesses_perm` — the **decode correspondence** the proven balance translation consumes: the
  native State-bus access list (the per-row `stateLookups` aggregate plus the public `±1` boundary) is
  a permutation of the `Interaction.toAccess`-image of the witness's Clean-side State-channel
  interactions. Per row this is `stateLookups_eq_emitted` (`Soundness/StateConsistency.lean`) lifted
  over the table flatMap, plus the verifier's boundary pull/push (`sp1StateVerifierMain` — under
  `toAccess` exactly the `(final, -1)`/`(init, +1)` entries); a permutation because the witness lists
  the verifier's interactions first.

(A one-constructor `Prop` inductive, Exists-style, because the bundle carries data (`rows`/`data`)
alongside the proofs; consume it with `obtain ⟨rows, data, h_spec, hbin, h_corr⟩`.) -/
inductive SP1WitnessDecode (witness : EnsembleWitness (sp1Ensemble (p := p))) : Prop where
  | mk
    (rows : List (ChipRow p))
    (data : ProverData (ZMod p))
    (spec_holds : ∀ r ∈ rows, r.chipSpec data)
    (is_real_binary : ∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1)
    (state_accesses_perm :
      (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf witness.publicInput, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf witness.publicInput, (-1 : ℤ))]).Perm
        ((witness.interactionsWith Channels.stateChannel.toRaw).map Interaction.toAccess))

/-- **The decode seam (roadmap W1b + W1c; the sole residual `sorry`).** From the ensemble `Statement`'s
per-table constraints and balanced channels, decode the witness into `SP1WitnessDecode`: the 25-chip
`witness.tables ↔ List (ChipRow p)` decode (`same_circuits` + `valueFromOffset`; the 11 provider tables
contribute no `ChipRow` and no State interactions), per-table `Component.weakSoundness` for
`spec_holds` (byte/program pull guarantees grounded against the provider tables; the `isU64` operand
`Assumptions` recovered from the memory-bus balance against the init/finalize boundary), the binary
gating, and the per-row `stateLookups_eq_emitted` correspondence lifted over the table flatMap (+ the
verifier boundary). -/
theorem sp1_witness_decode (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) (hB : witness.BalancedChannels) :
    SP1WitnessDecode witness := by
  sorry

/-- **W1a, proven: Clean State-channel balance ⇒ native gated State-bus balance.** From Clean's
`BalancedInteractions` over the (single-channel) State interactions — one instantiation of
`witness.BalancedChannels` — and the decode correspondence (`SP1WitnessDecode.state_accesses_perm`),
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

/-- **The witness → gated-capstone bridge (assembled; `sorry`-free given the decode seam).** From the
ensemble `Statement`'s per-table constraints and balanced channels, the heterogeneous trace decoded
from the witness satisfies the three hypotheses of `gatedExecution_of_specs_and_balance`: per-row chip
`Spec`s, binary `is_real` gating, and the gated State-bus balance with the public
genesis/finalization boundary. Assembly: the W1b/W1c seam `sp1_witness_decode` supplies rows/data,
`chipSpec`s, gating, and the State-bus decode correspondence; the proven W1a translation
`sp1_state_balance_of_balancedInteractions` turns `witness.BalancedChannels` — instantiated at the
State channel, the head of the ensemble's four-channel list — into the native gated balance. -/
theorem sp1_gatedExecution_prereqs (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hC : witness.Constraints) (hB : witness.BalancedChannels) :
    ∃ (rows : List (ChipRow p)) (data : ProverData (ZMod p)),
      (∀ r ∈ rows, r.chipSpec data) ∧
      (∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1) ∧
      isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf witness.publicInput, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf witness.publicInput, (-1 : ℤ))]) := by
  obtain ⟨rows, data, h_spec, hbin, h_corr⟩ := sp1_witness_decode witness hC hB
  -- instantiate the balanced channels at the State channel (the ensemble channel-list head)
  have h_balanced : BalancedInteractions
      (witness.interactionsWith Channels.stateChannel.toRaw) := by
    rw [← EnsembleWitness.interactionsWith_allTablesWitness]
    exact hB Channels.stateChannel.toRaw (List.mem_cons_self ..)
  exact ⟨rows, data, h_spec, hbin,
    sp1_state_balance_of_balancedInteractions witness.publicInput rows hbin _
      (fun i hi => EnsembleWitness.channel_eq_of_mem_interactionsWith hi) h_balanced h_corr⟩

/-- **SP1 as a Clean `FormalEnsemble`** — the final whole-machine soundness object, now a direct
literal over `sp1Ensemble` (the bespoke `GatedVm.toFormalEnsemble` packaging is retired; discharging
the `Statement` existential is the `rintro` line). Its `soundness` is the **sorry-free** assembly of
the gated capstone `gatedExecution_of_specs_and_balance` with `sp1_gatedExecution_prereqs` — itself
proven, modulo the single isolated decode seam `sp1_witness_decode`. -/
def sp1FormalEnsemble : FormalEnsemble (ZMod p) SP1PublicIO where
  ensemble := sp1Ensemble
  Assumptions := sp1Assumptions
  Spec := sp1Spec
  soundness := by
    rintro publicInput _hA ⟨witness, rfl, hC, hB⟩
    obtain ⟨rows, data, h_spec, hbin, h_bal⟩ := sp1_gatedExecution_prereqs witness hC hB
    exact ⟨rows, gatedExecution_of_specs_and_balance rows data
      (initEntryOf witness.publicInput) (finalEntryOf witness.publicInput) h_spec hbin h_bal⟩

/-- **The final whole-machine capstone.** Whole-machine soundness as a Clean ensemble soundness: the
public-input assumptions plus the raw ensemble statement (per-table constraints + balanced channels)
imply the meaningful `sp1Spec` (a valid RISC-V-Sail execution trail from the public `pc_start` to the
public `next_pc`). -/
theorem sp1_machine_soundness :
    (sp1Ensemble (p := p)).Soundness (sp1Assumptions (p := p)) (sp1Spec (p := p)) :=
  (sp1FormalEnsemble (p := p)).soundness

end SP1Clean.Soundness
