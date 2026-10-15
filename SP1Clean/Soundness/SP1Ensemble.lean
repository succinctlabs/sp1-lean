import SP1Clean.Soundness.WitnessDecode
import SP1Clean.Model.BalanceBridge
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.ProviderTableId
import SP1Clean.Proofs.Chips.ByteChip.ByteChip
import SP1Clean.Proofs.Chips.ByteChip.RangeChip
import SP1Clean.Proofs.Chips.ProgramProviderChip
import SP1Clean.Proofs.Chips.MemoryProviderChip
import SP1Clean.Proofs.Chips.MemoryFinalizeChip
import SP1Clean.Proofs.Chips.StateBumpChip.Formal
import SP1Clean.Proofs.Chips.MemoryBumpChip.Formal
import SP1Clean.Proofs.Chips.HaltChip.Formal
import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal
import SP1Clean.FormalModel.Contracts.PublicValues
import ToClean.Circuit.VerifierInteractions
import Clean.Air.FlatEnsemble

/-! # The supported native SP1 machine as a plain Clean `Ensemble`

This module packages the 25 supported instruction tables and 30 native provider/boundary tables over
seven channels, together with the pull-final/push-init State verifier. It also proves the
physical-table alignment and typed-interaction partition used by the timed grounding capstone in
`Soundness/AIR.lean`.

**Why a plain `Ensemble`, not a `SoundEnsemble`/`addVm`.** `SoundEnsemble.addTable` demands each
table's `channelsWithGuarantees ⊆ finished`; post-flip every chip's is `[byte, program, memory]`, and
`memoryChannel` can never be a *finished* channel (chips pull-then-push it — the circular VM-channel
shape, `Clean/Air/Vm.lean` top doc). Nor can `addVm` compose it (single-VM-channel engine; State and
Memory are both VM-shaped). A plain `Ensemble` carries no composition obligations — its `Statement`
supplies the constraints and channel balance — and the per-channel
soundness facts are proven separately (byte/program grounding via the finished-channel machinery;
State via the trail; memory `isU64` via the boundary balance). The SP1 argument needs an explicitly
ordered execution and per-location memory history in addition to Clean's channel-level results.

`SupportedCoreNativeRelation` supplies the semantic program/provider binding and restricts the
syscall table to inactive rows. These are separate from `Ensemble.Statement`; neither follows
from constraints and balance alone. Memory timestamp bounds are derived by the grounding proof. -/

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
end. `clk_low` is the pre-folded low clock (`clk_0_16 + clk_16_24 * 65536`). The structure itself lives
on the formal-model audit surface in `FormalModel/Contracts/PublicValues.lean`; the typed boundary
messages the capstone consumes are `initialBoundaryStateMessage`/`finalBoundaryStateMessage`
(`Soundness/TypedState.lean`). -/

/-! ## The boundary verifier

`sp1StateVerifier` is the genesis/finalization circuit: a true `pull` of the public **final** state
followed by a true `push` of the public **initial** state (SP1's bus-enforced boundary, `../sp1
record.rs eval_state` `send_state(.,pc_start,1)` + `receive_state(.,next_pc,1)`). These are exactly
the `[+1 init, -1 final]` boundary contributions the trail engine's endpoint balance consumes
(`TypedState.realDecodedStateMessages_perm`). The pull/push shape is Clean-idiomatic — it exposes the
loop-closing `[pulled final, pushed init]` pair. No witness cells (`localLength = 0`).

**W3 D5-A**: the row also pulls the twelve byte range checks over the split-limb public boundary —
per end, the two 16-bit `Range` checks (`clk_0_16`, `clk_32_48`), the `U8Range` pair
(`clk_24_32`, `clk_16_24`) in the exact public-value interaction's operand order, and the three
16-bit pc checks — so `Spec` is now
`SP1StateBoundary.LimbBounds`: every committed limb's canonicity is proved in-circuit, which is the
goodness-filter base case (the pushed initial State message is canonical by construction, with no
`InitialBoundaryFacts` premise). The pulls are ungated (the boundary row is always live, gate `1`),
matching the always-on State pair. -/
@[circuit_norm]
def sp1StateVerifierMain (pi : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  Channels.stateChannel.pull
    ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩
  Channels.stateChannel.push
    ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩
  Channels.byteChannel.pull
    (⟨6, pi.init_clk_0_16, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.init_clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨3, 0, pi.init_clk_24_32, pi.init_clk_16_24⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.init_pc0, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.init_pc1, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.init_pc2, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.final_clk_0_16, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.final_clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨3, 0, pi.final_clk_24_32, pi.final_clk_16_24⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.final_pc0, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.final_pc1, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  Channels.byteChannel.pull
    (⟨6, pi.final_pc2, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  -- The exit binding (halt-table wave): the verifier's row is exactly the public input
  -- (`verifier_length_zero`), so it can witness no gate cell — the pull is **ungated**. The halt
  -- table pushes the reduced `x10` word when real and the zero code when padding; balance then
  -- forces `exit_code = reduce(a0)` on halting shards and `exit_code = 0` on ordinary shards.
  Channels.exitChannel.pull (⟨pi.exit_code⟩ : Channels.ExitMsg (Expression (ZMod p)))

instance sp1StateVerifierElaborated :
    ElaboratedCircuit (ZMod p) SP1PublicIO unit sp1StateVerifierMain where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees :=
    [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw, Channels.exitChannel.toRaw]
  channelsLawful := by
    preserve_tactic_target
    simp [circuit_norm, sp1StateVerifierMain, Channels.stateChannel, Channels.byteChannel,
      Channels.exitChannel]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_channelsWithGuarantees_eq :
    ((sp1StateVerifierElaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw, Channels.exitChannel.toRaw] :=
  rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_localLength_eq (x : Var SP1PublicIO (ZMod p)) :
    (sp1StateVerifierElaborated (p := p)).localLength x = 0 := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- `16 < p` for the byte-table width-column round-trip. -/
private lemma h16p' [Fact (2 ^ 17 < p)] : (16 : ℕ) < p := by
  have := Fact.out (p := 2 ^ 17 < p); omega

theorem sp1StateVerifier_soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) sp1StateVerifierMain
      (fun _ _ => True) (fun pi _ _ => pi.LimbBounds) := by
  circuit_proof_start
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  simp only [circuit_norm, SP1StateBoundary.LimbBounds, Channels.stateChannel,
    Channels.byteChannel, Channels.exitChannel] at h_holds ⊢
  obtain ⟨i016, i3248, ipair, ipc0, ipc1, ipc2, f016, f3248, fpair, fpc0, fpc1, fpc2⟩ := h_holds
  exact ⟨(byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact i016),
    ((byteRowSpec_u8range_pair _ _).mp ipair).2,
    ((byteRowSpec_u8range_pair _ _).mp ipair).1,
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact i3248),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact ipc0),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact ipc1),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact ipc2),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact f016),
    ((byteRowSpec_u8range_pair _ _).mp fpair).2,
    ((byteRowSpec_u8range_pair _ _).mp fpair).1,
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact f3248),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact fpc0),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact fpc1),
    (byteRowSpec_range _ h16p').mp (by rw [Nat.cast_ofNat]; exact fpc2)⟩

/-- The boundary row's prover obligation: the committed limbs really are in range (the honest
public values are produced limb-wise from genuine 48-bit clocks and pcs). -/
def sp1StateVerifierProverAssumptions (pi : SP1PublicIO (ZMod p))
    (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop := pi.LimbBounds

theorem sp1StateVerifier_completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) sp1StateVerifierMain
      sp1StateVerifierProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
  simp only [sp1StateVerifierProverAssumptions, SP1StateBoundary.LimbBounds] at h_assumptions
  obtain ⟨i016, i1624, i2432, i3248, ipc0, ipc1, ipc2,
    f016, f1624, f2432, f3248, fpc0, fpc1, fpc2⟩ := h_assumptions
  simp only [circuit_norm, Channels.stateChannel, Channels.byteChannel, Channels.exitChannel]
  exact ⟨(byteRowSpec_range _ h16p').mpr i016,
    (byteRowSpec_range _ h16p').mpr i3248,
    (byteRowSpec_u8range_pair _ _).mpr ⟨i2432, i1624⟩,
    (byteRowSpec_range _ h16p').mpr ipc0,
    (byteRowSpec_range _ h16p').mpr ipc1,
    (byteRowSpec_range _ h16p').mpr ipc2,
    (byteRowSpec_range _ h16p').mpr f016,
    (byteRowSpec_range _ h16p').mpr f3248,
    (byteRowSpec_u8range_pair _ _).mpr ⟨f2432, f1624⟩,
    (byteRowSpec_range _ h16p').mpr fpc0,
    (byteRowSpec_range _ h16p').mpr fpc1,
    (byteRowSpec_range _ h16p').mpr fpc2⟩

/-- The SP1 boundary verifier as a `GeneralFormalCircuit`: pulls the public final state, pushes the
public initial state, range-checks every committed limb on the Byte bus (`Spec = LimbBounds`), and
exposes the loop-closing structural State pair. -/
def sp1StateVerifier : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := sp1StateVerifierMain
  elaborated := sp1StateVerifierElaborated
  Assumptions := fun _ _ => True
  Spec := fun pi _ _ => pi.LimbBounds
  ProverAssumptions := sp1StateVerifierProverAssumptions
  soundness := sp1StateVerifier_soundness
  completeness := sp1StateVerifier_completeness
  channelsWithRequirements := []
  requirementsChannelsLawful := fun pi offset => by
    preserve_tactic_target
    simp only [circuit_norm, sp1StateVerifierMain, Channels.stateChannel, Channels.byteChannel,
      Channels.exitChannel]
    intro channel h
    tauto
  exposedChannels := fun pi _ =>
    expose Channels.stateChannel
      [ Channels.stateChannel.pulled ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩,
        Channels.stateChannel.pushed ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩ ] ++
    expose Channels.exitChannel
      [ Channels.exitChannel.pulled (⟨pi.exit_code⟩ : Channels.ExitMsg (Expression (ZMod p))) ]
  exposedChannels_eq := by
    preserve_tactic_target
    intro pi offset
    unfold Operations.ExposedChannelsLawful
    intro exposed exposedMem
    simp only [expose, List.mem_append, List.mem_singleton] at exposedMem
    rcases exposedMem with rfl | rfl <;>
      simp only [sp1StateVerifierMain, circuit_norm,
        Channels.byteChannel_eq_stateChannel_false,
        Channels.byteChannel_eq_exitChannel_false,
        Channels.stateChannel_eq_exitChannel_false,
        Channels.exitChannel_eq_stateChannel_false]

omit [Fact (2 ^ 24 < p)] in
/-- The verifier's exact syntactic State pair, exposed without unfolding its formal-circuit record. -/
theorem sp1StateVerifierMain_stateInteractions (pi : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((sp1StateVerifierMain pi).operations offset).interactionsWith Channels.stateChannel.toRaw =
      [(Channels.stateChannel.pulled
        ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩).toRaw,
       (Channels.stateChannel.pushed
        ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩).toRaw] := by
  simp [sp1StateVerifierMain, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
/-- The verifier's exact syntactic Exit pull — the ungated `⟨exit_code⟩` consumption the halt
table's pushes balance against. -/
theorem sp1StateVerifierMain_exitInteractions (pi : Var SP1PublicIO (ZMod p)) (offset : ℕ) :
    ((sp1StateVerifierMain pi).operations offset).interactionsWith Channels.exitChannel.toRaw =
      [(Channels.exitChannel.pulled
        (⟨pi.exit_code⟩ : Channels.ExitMsg (Expression (ZMod p)))).toRaw] := by
  simp [sp1StateVerifierMain, circuit_norm]

/-- The same boundary contract through Clean's separate, interaction-only public verifier. -/
def sp1StateVerifierProgram : Verifier.Program (ZMod p) SP1PublicIO where
  main input := Verifier.ofInteractions ((sp1StateVerifierMain input).operations 0).interactions (by
    intro interaction member env
    simp only [sp1StateVerifierMain, circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AbstractInteraction.Requirements, AbstractInteraction.Guarantees, ChannelInteraction.toRaw,
        Channels.stateChannel, Channels.byteChannel, Channels.exitChannel, Channel.toRaw, circuit_norm])
  Spec input _ := input.LimbBounds
  soundness := by
    intro env guarantees
    have original : ((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations 0).FullGuarantees env := by
      simpa only [Operations.FullGuarantees, Verifier.ofInteractions_interactions] using guarantees
    have checked : ((sp1StateVerifierMain (varFromOffset SP1PublicIO 0)).operations 0).ConstraintsHold env := by
      simp [sp1StateVerifierMain, circuit_norm]
    exact (sp1StateVerifier.original_full_soundness 0 env (varFromOffset SP1PublicIO 0)
      trivial checked original).1

/-! ## The SP1 machine as a plain Clean `Ensemble` -/

/-- Stable cardinalities used by positional decoder and provider-partition proofs. The two complete
counts come from the role-specific neutral inventories; the intermediate constants name semantic
prefixes within the provider segment. -/
def instructionTableCount : ℕ := InstructionChipId.count
def byteProviderTableCount : ℕ := 6
def rangeProviderTableCount : ℕ := 17
def preprocessedProviderTableCount : ℕ := 24
def nonBumpProviderTableCount : ℕ := 26
def stateSilentProviderTableCount : ℕ := 27
def providerTableCount : ℕ := ProviderTableId.count
def ensembleTableCount : ℕ := NativeTableId.all.length

/-- The complete fixed-width realization of SP1's preprocessed Range table, ordered by width
`0, …, 16`. -/
def sp1RangeProviderTables : List (Component (ZMod p)) :=
  RangeChip.allWidths.map fun width => { circuit := RangeChip.circuitFor width }

theorem sp1RangeProviderTables_length : (sp1RangeProviderTables (p := p)).length = 17 := by
  simp [sp1RangeProviderTables, RangeChip.allWidths]

/-- Layer-local realization of a neutral provider/boundary identity as its verified Clean table.
Unlike the identity, this map deliberately imports circuits; it remains total and contains no
instruction-routing cases. -/
def providerTableFor : ProviderTableId → Component (ZMod p)
  | .byte .u8Range => { circuit := ByteChip.U8Range.circuit }
  | .byte .msb => { circuit := ByteChip.MSB.circuit }
  | .byte .andByte => { circuit := ByteChip.AndByte.circuit }
  | .byte .orByte => { circuit := ByteChip.OrByte.circuit }
  | .byte .xorByte => { circuit := ByteChip.XorByte.circuit }
  | .byte .ltu => { circuit := ByteChip.Ltu.circuit }
  | .range width => { circuit := RangeChip.circuitFor width }
  | .program => { circuit := ProgramProviderChip.circuit }
  | .memoryInit => { circuit := MemoryProviderChip.circuit }
  | .memoryFinalize => { circuit := MemoryFinalizeChip.circuit }
  | .memoryBump => { circuit := MemoryBumpChip.circuit }
  | .stateBump => { circuit := StateBumpChip.circuit }
  | .halt => { circuit := HaltChip.circuit }
  | .syscallInstrs => { circuit := SyscallInstrsChip.circuit }

/-- The 30 in-circuit boundary/provider tables: six `ByteChip` opcode tables, the complete
17-member fixed-width Range family, the program-ROM provider, the two memory boundary tables
(init-push + finalize-pull), the two SP1 system tables MemoryBump (position 51: the
register-record timestamp refreshes) and StateBump (position 52: the clock/pc re-limbing rows that
allow clock and pc limb normalization), the Halt table (position 53: the halting shard's ECALL
witness row), and the `SyscallInstrs` table (position 54: SP1's whole syscall chip).
MemoryBump, StateBump, and SyscallInstrs have whole-table faithfulness anchors. Every pusher proves
its pushes' channel `Guarantees` in-circuit, which is what
grounds the chips' byte/program/memory pulls at the capstone. -/
def sp1ProviderTables : List (Component (ZMod p)) :=
  ProviderTableId.all.map (providerTableFor (p := p))

/-- The identity-derived provider list reduces to the established physical witness order. This
keeps existing position-sensitive consumers auditable without maintaining a second registry. -/
theorem sp1ProviderTables_explicit :
    sp1ProviderTables (p := p) =
      [{ circuit := ByteChip.U8Range.circuit }, { circuit := ByteChip.MSB.circuit }, { circuit := ByteChip.AndByte.circuit },
       { circuit := ByteChip.OrByte.circuit }, { circuit := ByteChip.XorByte.circuit }, { circuit := ByteChip.Ltu.circuit }] ++
        sp1RangeProviderTables ++
      [{ circuit := ProgramProviderChip.circuit }, { circuit := MemoryProviderChip.circuit },
       { circuit := MemoryFinalizeChip.circuit }, { circuit := MemoryBumpChip.circuit },
       { circuit := StateBumpChip.circuit }, { circuit := HaltChip.circuit }, { circuit := SyscallInstrsChip.circuit }] := by
  rfl

/-- Pointwise positional coverage, including out-of-bounds provider positions. -/
@[simp] theorem sp1ProviderTables_getElem? (i : ℕ) :
    (sp1ProviderTables (p := p))[i]? =
      (ProviderTableId.all[i]?).map (providerTableFor (p := p)) := by
  simp [sp1ProviderTables]

/-- Regression guard: the boundary/provider table count (6 byte + 17 range + program + 2 memory +
2 bump + halt + syscallInstrs). -/
theorem sp1ProviderTables_length : (sp1ProviderTables (p := p)).length = 30 := by
  simp [sp1ProviderTables]

/-- Every boundary/provider circuit before the bump/halt tail — positions 25–51 — stays off the
State channel. StateBump (52), Halt (53), and SyscallInstrs (54) form the remaining State-contributing
tail. The `take 27` prefix supports the typed State decomposition. -/
theorem sp1ProviderTables_stateChannel_not_mem :
    ∀ component ∈ (sp1ProviderTables (p := p)).take stateSilentProviderTableCount,
      Channels.stateChannel.toRaw ∉ component.circuit.channels := by
  intro component componentMem
  rw [sp1ProviderTables_explicit] at componentMem
  fin_cases componentMem <;>
    simp [GeneralFormalCircuit.channels, ByteChip.U8Range.circuit, ByteChip.MSB.circuit,
      ByteChip.AndByte.circuit, ByteChip.OrByte.circuit, ByteChip.XorByte.circuit,
      ByteChip.Ltu.circuit, RangeChip.circuitFor, RangeChip.circuit,
      ProgramProviderChip.circuit, MemoryProviderChip.circuit, MemoryFinalizeChip.circuit,
      MemoryBumpChip.circuit, circuit_norm]

/-- The 25 instruction and 30 provider/system tables, seven channels, and boundary verifier.
State, Byte, Program, and Memory carry the ordinary instruction interactions. Exit binds the public
exit code. SyscallInstrs also uses SP1's Syscall channel and the native PublicValues channel.
The current soundness relation restricts SyscallInstrs to inactive rows, making the latter two
ledgers empty. Its semantic boundary binding is an additional premise beyond `Statement`. -/
def sp1Ensemble : Ensemble (ZMod p) SP1PublicIO where
  tables := sp1Tables ++ sp1ProviderTables
  channels :=
    [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
     Channels.programChannel.toRaw, Channels.memoryChannel.toRaw,
     Channels.exitChannel.toRaw, Channels.syscallChannel.toRaw,
     Channels.publicValuesChannel.toRaw]
  unique_names := by exact of_decide_eq_true rfl
  verifier := sp1StateVerifierProgram

@[circuit_norm] lemma sp1Ensemble_tables :
    (sp1Ensemble (p := p)).tables = sp1Tables ++ sp1ProviderTables := rfl
@[circuit_norm] lemma sp1Ensemble_channels :
    (sp1Ensemble (p := p)).channels =
      [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
       Channels.programChannel.toRaw, Channels.memoryChannel.toRaw,
       Channels.exitChannel.toRaw, Channels.syscallChannel.toRaw,
       Channels.publicValuesChannel.toRaw] := rfl
@[circuit_norm] lemma sp1Ensemble_verifier :
    (sp1Ensemble (p := p)).verifier = sp1StateVerifierProgram := rfl

/-! ## Physical instruction-table alignment -/

/-- The deterministic decoder's 25 descriptors align positionally with the first 25 physical
witness tables, and both evaluate with the witness's shared prover data.  This is the generic
`InstructionTablesAligned` premise needed to identify decoded-row emissions with Clean's actual table
interactions. -/
theorem witness_instructionTables_aligned
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    InstructionTablesAligned (supportedChips (p := p)) (witness.tables.take 25) := by
  apply InstructionTablesAligned.of_components
  change (witness.tables.take 25).map (·.component) = sp1Tables
  have aligned := congrArg (List.take 25) witness.tables_map_component
  simpa only [← List.map_take, sp1Ensemble_tables,
    ← sp1Tables_length (p := p), List.take_left'] using aligned

/-- Every canonical decoded instruction row satisfies the constraints of its exact physical Clean
table row.  This is the common starting point for row-local AIR facts; downstream proofs never need
to reopen `same_circuits` or reason positionally about the full witness again. -/
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
      (List.mem_of_mem_take tableMem)
  · exact decodedMem

/-- Every physical table after the stable 25-chip prefix is one of the 30 declared provider or
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
      (witness.tables.take 25).flatMap (typedTableInteractionsWith · witness.data channel) :=
  decodedInstructionInteractionsWith_eq_tables witness.data channel
    (witness_instructionTables_aligned witness)

/-- Exact typed partition of the ensemble interaction list into verifier boundary, decoded
instruction rows, and the 30 provider/boundary tables. -/
theorem typedEnsembleInteractionsWith_partition
    {Message : TypeMap} [ProvableType Message]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (channel : Channel (ZMod p) Message) :
    typedEnsembleInteractionsWith witness channel =
      typedInteractionValuesWith (sp1Ensemble (p := p)).verifierOperations channel
          (Environment.fromInput witness.publicInput witness.data) ++
        decodedWitnessInstructionInteractionsWith witness.data witness.tables channel ++
          (witness.tables.drop 25).flatMap (typedTableInteractionsWith · witness.data channel) := by
  rw [decodedWitnessInstructionInteractionsWith_eq_tables]
  unfold typedEnsembleInteractionsWith
  rw [List.append_assoc, ← List.flatMap_append, List.take_append_drop]

/-- Clean balance transported to the proof-carrying typed interaction view. -/
theorem typedInteractions_balanced
    {Message : TypeMap} [ProvableType Message]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels) (channel : Channel (ZMod p) Message)
    (channelMem : channel.toRaw ∈ (sp1Ensemble (p := p)).channels) :
    BalancedInteractions
      ((typedEnsembleInteractionsWith witness channel).map TypedInteraction.raw) := by
  rw [typedEnsembleInteractionsWith_raw]
  exact balanced channel.toRaw channelMem

end SP1Clean.Soundness
