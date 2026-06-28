import SP1Clean.Soundness.SP1GatedVm
import SP1Clean.Proofs.Chips.ByteChip.Ensemble
import SP1Clean.Proofs.Chips.ProgramProviderEnsemble
import Clean.Air.Vm

/-! # Phase A — the State-bus `VmTables` de-risk spike

Validates that Clean's native State-bus VM soundness engine (`VmTables` + `SoundEnsemble.addVm`)
integrates with SP1's chips and the byte/program provider ensembles — **without** replacing the live
GatedVm capstone (`sp1_machine_soundness`), which is untouched.

The spike stands up `sp1StateVmSpike : VmTables` with a single table (`AddChip`), a fresh boundary
verifier `sp1StateVerifier` (pull final, push init — the VmTables loop closure, distinct from the
GatedVm `sp1Verifier`'s `emit ±1`), chains the byte + program finished channels into a `SoundEnsemble`,
and applies `addVm` to produce a `SoundVmEnsemble`. Phase A3 flips `tables := sp1Tables` once all 25
chips expose the State pair. We deliberately stop at `SoundVmEnsemble` (no `.toFormal`, which re-introduces
the per-table `Assumptions`/memory-isU64 seam). -/

namespace SP1Clean.Soundness

open Circuit Air.Flat
open SP1Clean.Channels (stateChannel byteChannel programChannel StateMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `addVm` needs `ringChar F ≠ 2`; for `ZMod p` with `p` an odd prime that is `p ≠ 2`. -/
local instance : Fact (ringChar (ZMod p) ≠ 2) :=
  ⟨by rw [ZMod.ringChar_zmod_n]; have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact (2 ^ 17 < p)] in
/-- The State↔Program bus distinctness `Model/Channels.lean` doesn't pre-instantiate (it only ships the
pairs its `interactionsWith` filters compare); the `addVm` channel-disjointness obligations need both
orderings. Same name-difference proof as the `*_eq_*_false` family there. -/
@[circuit_norm] lemma stateChannel_eq_programChannel_false :
    ((stateChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  have : (stateChannel (p := p)).toRaw.name = (programChannel (p := p)).toRaw.name := by rw [he]
  simp [Channel.toRaw_name, Channels.stateChannel, Channels.programChannel] at this

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma programChannel_eq_stateChannel_false :
    ((programChannel (p := p)).toRaw = (stateChannel (p := p)).toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  have : (programChannel (p := p)).toRaw.name = (stateChannel (p := p)).toRaw.name := by rw [he]
  simp [Channel.toRaw_name, Channels.stateChannel, Channels.programChannel] at this

/-! ## The VmTables boundary verifier -/

/-- The VmTables boundary verifier `main`: a true `pull` of the public **final** state followed by a
true `push` of the public **init** state — the loop-closing boundary `VmTables.verifier_channel` wants
(`[pulled final, pushed init]`). (Contrast `sp1VerifierMain`, which `emit`s `±1` for the GatedVm balance;
that has `assumeGuarantees = false` and no `exposedChannels`, so it does not satisfy the VmTables shape.) -/
@[circuit_norm]
def sp1StateVerifierMain (pi : Var SP1PublicIO (ZMod p)) : Circuit (ZMod p) Unit := do
  stateChannel.pull ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩
  stateChannel.push ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩

instance sp1StateVerifierElaborated :
    ElaboratedCircuit (ZMod p) SP1PublicIO unit sp1StateVerifierMain where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_channelsWithGuarantees_eq :
    ((sp1StateVerifierElaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1StateVerifier_localLength_eq (x : Var SP1PublicIO (ZMod p)) :
    (sp1StateVerifierElaborated (p := p)).localLength x = 0 := rfl

theorem sp1StateVerifier_soundness :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) sp1StateVerifierMain
      (fun _ _ => True) (fun _ _ _ => True) := by
  circuit_proof_start
  simp [circuit_norm, Channels.stateChannel, Channels.StateMsg.Spec]

set_option linter.unusedSectionVars false in
theorem sp1StateVerifier_completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) sp1StateVerifierMain
      (fun _ _ _ => True) (fun _ _ _ => True) := by
  circuit_proof_start
  simp [circuit_norm, Channels.stateChannel, Channels.StateMsg.Spec]

/-- The VmTables boundary verifier as a `GeneralFormalCircuit`, exposing `[pulled final, pushed init]`
on the State channel. -/
def sp1StateVerifier : GeneralFormalCircuit (ZMod p) SP1PublicIO unit where
  main := sp1StateVerifierMain
  elaborated := sp1StateVerifierElaborated
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  soundness := sp1StateVerifier_soundness
  completeness := sp1StateVerifier_completeness
  channelsWithRequirements := [stateChannel.toRaw]
  exposedChannels := fun pi _ =>
    expose stateChannel
      [ pulled ⟨pi.final_clk_high, pi.final_clk_low, pi.final_pc0, pi.final_pc1, pi.final_pc2⟩,
        pushed ⟨pi.init_clk_high, pi.init_clk_low, pi.init_pc0, pi.init_pc1, pi.init_pc2⟩ ]
  exposedChannels_eq := by
    intro pi offset
    simp [circuit_norm, sp1StateVerifierMain]

/-- The `is_real` selector of any `AddChip.main` row is boolean, read off the inline
`assertZero (is_real*(is_real-1))` gate that survives into `ConstraintsHold.Shallow` (the gate is a
top-level assert, kept inline precisely so it is visible to the shallow constraints — see
`Native/Chips/AddChip/Defs.lean`). Stated over an **abstract** `input`/`offset` (as `AddChip.soundness`'s
`circuit_proof_start` does) so `circuit_norm` decomposes `main` cheaply — the concrete
`varFromOffset`/`size` form chokes `whnf`. -/
private lemma addChip_main_is_real_bool (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((AddChip.main input).operations offset)) :
    Expression.eval env input.is_real = 0 ∨ Expression.eval env input.is_real = 1 := by
  -- The shallow constraints collapse (subcircuits → `True`) to exactly the inline gate.
  simp only [AddChip.main, circuit_norm] at h
  exact bool_of_mul_pred h

/-! ## The State VM (1-table spike) -/

set_option maxHeartbeats 1000000 in
/-- The SP1 State bus as a Clean `VmTables`, with a single table (`AddChip`) for the de-risk spike.
Phase A3 flips `tables := sp1Tables` once all 25 chips expose the State `[pulledIf, pushedIf]` pair.
`tables_channel` is discharged from AddChip's `exposedChannels` field + its inline `is_real` gate;
`verifier_channel`/`verifier_requirements` are trivial (`StateMsg.Spec = True`). -/
def sp1StateVmSpike : VmTables (ZMod p) SP1PublicIO where
  channel := stateChannel
  tables := [⟨AddChip.circuit⟩]
  verifier := sp1StateVerifier
  verifier_length_zero := by simp [circuit_norm, sp1StateVerifier]
  tables_channel := by
    -- `tables = [⟨AddChip.circuit⟩]`, so `List.Forall` is the single conjunct (singleton special-case).
    -- `apply Exists.intro` postpones the witness metavars so the membership proof fixes them.
    show ∃ _ _ _, _ ∧ _
    apply Exists.intro
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    · -- membership: AddChip exposes exactly `[pulledIf is_real cur, pushedIf is_real next]` on State.
      -- This fixes the three existential witnesses (`enabled := is_real`, `pull`/`push` the State rows).
      simp only [Component.rowInputVar_mk, Component.rowOffset_mk, AddChip.circuit]
      exact (mem_expose_pullIf_pushIf _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · -- booleanity of `enabled = is_real`: reduce the component `rowOperations` to `AddChip.main`'s
      -- ops over the abstract row input, then read the inline gate (the helper above).
      intro env h
      rw [Component.rowOperations_mk, show (AddChip.circuit (p := p)).main = AddChip.main from rfl] at h
      exact addChip_main_is_real_bool _ _ _ h
  verifier_channel := by simp [circuit_norm, sp1StateVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, sp1StateVerifier, sp1StateVerifierMain, Channels.stateChannel,
      Channels.StateMsg.Spec]

/-! ## The byte+program `SoundEnsemble` base + the `addVm` spike -/

/-- The byte- and program-finished base ensemble: chain the in-circuit program-ROM provider onto the
byte provider ensemble and finish `programChannel`. `finished = [program, byte]`. -/
def byteProgramEnsemble : SoundEnsemble (ZMod p) SP1PublicIO :=
  ByteChip.byteProviderEnsemble SP1PublicIO
    |>.addTable ⟨ProgramProviderChip.circuit⟩
        (by simp [circuit_norm, ProgramProviderChip.circuit, ByteChip.byteProviderEnsemble])
        (by simp [circuit_norm, ProgramProviderChip.circuit, ByteChip.byteProviderEnsemble])
    |>.addFinishedChannel programChannel.toRaw

/-- **The de-risk spike payoff.** `addVm` applies the State-bus VM to the byte+program-finished base,
producing a `SoundVmEnsemble` — validating the full `VmTables → addVm → SoundVmEnsemble` API against a
real SP1 chip and the real byte/program providers (memory stays an open requirement). -/
def sp1StateVmEnsemble : SoundVmEnsemble (ZMod p) SP1PublicIO :=
  byteProgramEnsemble.addVm sp1StateVmSpike
    (by simp [circuit_norm, sp1StateVmSpike, byteProgramEnsemble, ByteChip.byteProviderEnsemble,
        ProgramProviderChip.circuit, ByteChip.U8Range.circuit, ByteChip.MSB.circuit,
        ByteChip.AndByte.circuit, ByteChip.OrByte.circuit, ByteChip.XorByte.circuit,
        RangeChip.circuit8, RangeChip.circuit13, RangeChip.circuit16, RangeChip.circuit])
    (by simp [circuit_norm, sp1StateVmSpike, sp1StateVerifier, AddChip.circuit, AddChip.elaborated,
        byteProgramEnsemble, ByteChip.byteProviderEnsemble])
    (by simp [circuit_norm, sp1StateVmSpike, sp1StateVerifier, AddChip.circuit,
        byteProgramEnsemble, ByteChip.byteProviderEnsemble, ProgramProviderChip.circuit])

/-- The State VM channel is sound: from a constraint-satisfying, channel-balanced witness over the
byte+program-finished ensemble plus the State VM, the verifier's guarantees hold. The validated
`VmTables`/`addVm` integration. -/
theorem sp1StateVm_spike_sound : (sp1StateVmEnsemble (p := p)).ensemble.SoundVmChannel :=
  (sp1StateVmEnsemble (p := p)).soundVmChannel

end SP1Clean.Soundness
