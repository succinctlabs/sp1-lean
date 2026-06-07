import SP1Clean.Soundness.ChipRegistry
import SP1Clean.Soundness.GatedVm.Capstone
import SP1Clean.Soundness.GatedVm.Formal
import SP1Clean.Soundness.GatedVm.BalanceMod
import SP1Clean.Foundations.InteractionProjection
import Clean.Air.FlatEnsemble

/-! # SP1 as a Clean `FormalEnsemble` — the final, gated whole-machine ensemble

The realized whole-machine soundness object for SP1, built on the **gated VM** path (`GatedVm/`). It
packages the axiom-clean gated capstone `gatedExecution_of_specs_and_balance` (`GatedVm/Capstone.lean`)
into a Clean `Air.Flat.FormalEnsemble` via `GatedVm.toFormalEnsemble` (`GatedVm/Formal.lean`), carrying a
**meaningful** spec: from the ensemble `Statement` (per-table constraints + balanced channels) over the
public initial/final machine state, there is a valid RISC-V-Sail execution trail from the public
`pc_start` to the public `next_pc`, with every real instruction Sail-correct.

This replaces the earlier `Soundness/FlatEnsemble.lean` plain-path scaffold (`PublicIO := unit`,
`Spec := True`, two scaffold `sorry`s) — see `docs/roadmap.md` §B5.

**Trust boundary / residue.** The `soundness` *assembly* is sorry-free: it threads the two ensemble
prerequisites into the gated capstone. The remaining bridge from the Clean ensemble `Statement` to those
prerequisites is the single isolated premise `sp1_gatedExecution_prereqs` (`sorry`), which bundles the
project's checklist §B5 residue:
* (a) the Clean `BalancedInteractions` → native `isConsistentBalanced` State-bus translation (via
  `isConsistentBalanced_of_intCast_zero` + `stateLookups_eq_emitted` + the verifier boundary), and
* (b)+(c) the 22-chip witness → `ChipRow` decode + per-table `Component.weakSoundness` + each chip's
  `isU64` operand-`Assumptions` recovery from the memory-bus balance.
Closing it yields a fully axiom-clean `sp1FormalEnsemble` with trust *below* the bespoke capstone, with
no further structural work. -/

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

`sp1Verifier` is the genesis/finalization circuit: it emits a constant-`+1` State **send** of the public
initial state and a constant-`-1` State **receive** of the public final state (SP1's bus-enforced
boundary, `../sp1 record.rs eval_state` `send_state(.,pc_start,1)` + `receive_state(.,next_pc,1)`). These
are exactly the `[+1 init, -1 final]` boundary term that `gatedExecution_of_specs_and_balance`'s `h_bal`
assumes; a `.empty` verifier would omit them. The emits add no witness cells, so `localLength = 0`. The
`Spec` is `True` (the meaning is carried by the trace-level balance, not a per-row guarantee). -/
@[circuit_norm]
def sp1VerifierMain (pi : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  Channels.stateChannel.emitGated (1 : Expression (ZMod p))
    ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩
  Channels.stateChannel.emitGated (-1 : Expression (ZMod p))
    ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩

instance sp1VerifierElaborated : ElaboratedCircuit (ZMod p) SP1PublicIO unit sp1VerifierMain where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := []
  channelsWithRequirements := [Channels.stateChannel.toRawGated]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1Verifier_channelsWithGuarantees_eq :
    ((sp1VerifierElaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1Verifier_channelsWithRequirements_eq :
    ((sp1VerifierElaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [Channels.stateChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1Verifier_localLength_eq (x : Var SP1PublicIO (ZMod p)) :
    (sp1VerifierElaborated (p := p)).localLength x = 0 := rfl

omit [Fact (2 ^ 24 < p)] in
theorem sp1Verifier_soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) sp1VerifierMain
      (fun _ _ => True) (fun _ _ _ => True) := by
  -- both emits carry the trivial State guarantee (`StateMsg.Spec = True`); the `-1` (final) requirement
  -- is vacuous (`mult = -1`), the `+1` (init) one owes only `True`.
  circuit_proof_start
  simp only [circuit_norm, Channels.stateChannel, Channels.StateMsg.Spec]

omit [Fact (2 ^ 24 < p)] in
theorem sp1Verifier_completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) sp1VerifierMain
      (fun _ _ _ => True) (fun _ _ _ => True) := by
  circuit_proof_start

/-- The SP1 boundary verifier as a `GeneralFormalCircuit`: emits the constant-`±1` State boundary. -/
def sp1Verifier : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := sp1VerifierMain
  elaborated := sp1VerifierElaborated
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  soundness := sp1Verifier_soundness
  completeness := sp1Verifier_completeness

/-! ## The SP1 machine as a gated VM -/

/-- The 24 capstone-wired chips, each a `GeneralFormalCircuit` wrapped as a Clean AIR `Component`
(`⟨chip.circuit⟩`). Order mirrors `Soundness/AllChips.lean`'s `allChipsTrace`. DivRem is excluded
exactly as in `ChipRegistry.allChipKinds` (its soundness is still `sorry`). `Mul`'s `circuit` carries a
completeness `sorry` (like ShiftLeft/ShiftRight/Branch), but the ensemble soundness consumes only each
`Component`'s constraints/channels, never its `completeness` proof — so it does not enter the capstone
axioms. -/
def sp1Tables : List (Component (ZMod p)) :=
  [⟨AddChip.circuit⟩, ⟨AddiChip.circuit⟩, ⟨AddwChip.circuit⟩, ⟨SubChip.circuit⟩, ⟨SubwChip.circuit⟩,
   ⟨BitwiseChip.circuit⟩, ⟨LtChip.circuit⟩, ⟨ShiftLeftChip.circuit⟩, ⟨ShiftRightChip.circuit⟩,
   ⟨JalChip.circuit⟩, ⟨JalrChip.circuit⟩, ⟨BranchChip.circuit⟩, ⟨UTypeChip.circuit⟩,
   ⟨LoadByteChip.circuit⟩, ⟨LoadHalfChip.circuit⟩, ⟨LoadWordChip.circuit⟩, ⟨LoadDoubleChip.circuit⟩,
   ⟨LoadX0Chip.circuit⟩, ⟨StoreByteChip.circuit⟩, ⟨StoreHalfChip.circuit⟩, ⟨StoreWordChip.circuit⟩,
   ⟨StoreDoubleChip.circuit⟩, ⟨MulChip.circuit⟩, ⟨AluX0Chip.circuit⟩]

/-- **The SP1 machine as a `GatedVm`.** The typed State channel (the VM main channel), the 24 chip
tables, the remaining three buses (Byte/Program/Memory in gated raw form), and the constant-`±1` boundary
`sp1Verifier`. Its `toEnsemble.channels` is the four-channel list
`[stateChannel, byteChannel, programChannel, memoryChannel].toRawGated` (the same model the chips emit
on). -/
def sp1GatedVm : GatedVm (ZMod p) SP1PublicIO where
  stateChannel := Channels.stateChannel
  tables := sp1Tables
  busChannels :=
    [Channels.byteChannel.toRawGated, Channels.programChannel.toRawGated,
     Channels.memoryChannel.toRawGated]
  verifier := sp1Verifier
  verifier_length_zero := fun _ => rfl

/-- Scaffold ensemble assumptions — `True`. The chip operand `isU64` assumptions are not expressible on
`SP1PublicIO`; they are recovered per-witness from the memory-bus balance inside
`sp1_gatedExecution_prereqs`. -/
def sp1Assumptions : SP1PublicIO (ZMod p) → Prop := fun _ => True

/-- **The meaningful SP1 spec.** Over the public initial/final state, there is a heterogeneous trace
whose every real row reaches its RISC-V Sail spec and whose `current → next` transitions compose into a
valid execution trail from the public `pc_start` to the public `next_pc` — i.e. a `GatedExecution`
between the public endpoints. -/
def sp1Spec : SP1PublicIO (ZMod p) → Prop := fun pi =>
  ∃ rows : List (ChipRow p), GatedExecution rows (initEntryOf pi) (finalEntryOf pi)

/-- **The witness → gated-capstone bridge (the sole residual `sorry`).** From the ensemble `Statement`'s
per-table constraints and balanced channels, the heterogeneous trace decoded from the witness satisfies
the three hypotheses of `gatedExecution_of_specs_and_balance`: per-row chip `Spec`s, binary `is_real`
gating, and the gated State-bus balance with the public genesis/finalization boundary.

This is the project's checklist §B5 residue, bundled:
* (a) `witness.BalancedChannels` → `isConsistentBalanced (… ++ boundary)` — the Clean
  `BalancedInteractions` (over evaluated `Interaction (ZMod p)` per `Array`) → native
  `isConsistentBalanced` (over `LookupKey`) translation, via `isConsistentBalanced_of_intCast_zero`
  (`BalanceMod.lean`) + `stateLookups_eq_emitted` lifted over the table flatMap + the verifier's two
  `emitGated ±1` boundary interactions under `toAccess`;
* (b)+(c) `witness.Constraints` → per-row `chipSpec` — the 24-chip `witness.tables ↔ List (ChipRow p)`
  decode (`same_circuits` + `valueFromOffset`), per-table `Component.weakSoundness`, and each chip's
  `isU64` operand `Assumptions` recovered from the memory-bus balance. -/
theorem sp1_gatedExecution_prereqs (witness : EnsembleWitness (sp1GatedVm (p := p)).toEnsemble)
    (hC : witness.Constraints) (hB : witness.BalancedChannels) :
    ∃ (rows : List (ChipRow p)) (data : ProverData (ZMod p)),
      (∀ r ∈ rows, r.chipSpec data) ∧
      (∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1) ∧
      isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntryOf witness.publicInput, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntryOf witness.publicInput, (-1 : ℤ))]) := by
  sorry

/-- **SP1 as a Clean `FormalEnsemble`** — the final whole-machine soundness object. Its `soundness` is the
**sorry-free** assembly of the gated capstone `gatedExecution_of_specs_and_balance` with the single
isolated prerequisite `sp1_gatedExecution_prereqs`. -/
def sp1FormalEnsemble : FormalEnsemble (ZMod p) SP1PublicIO :=
  (sp1GatedVm (p := p)).toFormalEnsemble sp1Assumptions sp1Spec (by
    intro witness _hA hC hB
    obtain ⟨rows, data, h_spec, hbin, h_bal⟩ := sp1_gatedExecution_prereqs witness hC hB
    exact ⟨rows, gatedExecution_of_specs_and_balance rows data
      (initEntryOf witness.publicInput) (finalEntryOf witness.publicInput) h_spec hbin h_bal⟩)

/-- **The final whole-machine capstone.** Whole-machine soundness as a Clean ensemble soundness: the
public-input assumptions plus the raw ensemble statement (per-table constraints + balanced channels)
imply the meaningful `sp1Spec` (a valid RISC-V-Sail execution trail from the public `pc_start` to the
public `next_pc`). -/
theorem sp1_machine_soundness :
    (sp1GatedVm (p := p)).toEnsemble.Soundness (sp1Assumptions (p := p)) (sp1Spec (p := p)) :=
  (sp1FormalEnsemble (p := p)).soundness

end SP1Clean.Soundness
