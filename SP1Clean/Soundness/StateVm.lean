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
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel StateMsg)

-- Stated under the capstone bound `Fact (2 ^ 24 < p)` (the same `sp1Tables`/`sp1GatedVm` use, needed by
-- `Mul`/`DivRem`), with the project-standard `Fact (2 ^ 17 < p)` derived locally. The 1-table spike only
-- needed `2 ^ 17`; the full 25-table flip pulls in `Mul`/`DivRem`, which carry the stronger bound.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance sp1State_2_17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- `addVm` needs `ringChar F ≠ 2`; for `ZMod p` with `p` an odd prime that is `p ≠ 2`. -/
local instance : Fact (ringChar (ZMod p) ≠ 2) :=
  ⟨by rw [ZMod.ringChar_zmod_n]; have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact (2 ^ 24 < p)] in
/-- The State↔Program bus distinctness `Model/Channels.lean` doesn't pre-instantiate (it only ships the
pairs its `interactionsWith` filters compare); the `addVm` channel-disjointness obligations need both
orderings. Same name-difference proof as the `*_eq_*_false` family there. -/
@[circuit_norm] lemma stateChannel_eq_programChannel_false :
    ((stateChannel (p := p)).toRaw = (programChannel (p := p)).toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro he
  have : (stateChannel (p := p)).toRaw.name = (programChannel (p := p)).toRaw.name := by rw [he]
  simp [Channel.toRaw_name, Channels.stateChannel, Channels.programChannel] at this

omit [Fact (2 ^ 24 < p)] in
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

/-! ## Per-chip `enabled`-booleanity helpers

Each reads the inline `assertZero (enabled*(enabled-1))` gate that survives into
`ConstraintsHold.Shallow` (subcircuits collapse), mirroring `addChip_main_is_real_bool` from the
1-table spike. `tauto` picks the gate conjunct out of the chip-specific shallow conjunction. -/

private lemma add_enabled_bool (input : Var AddChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((AddChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [AddChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma addi_enabled_bool (input : Var AddiChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((AddiChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [AddiChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma addw_enabled_bool (input : Var AddwChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((AddwChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [AddwChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma sub_enabled_bool (input : Var SubChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((SubChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [SubChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma subw_enabled_bool (input : Var SubwChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((SubwChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [SubwChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma bitwise_enabled_bool (input : Var BitwiseChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((BitwiseChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [BitwiseChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma lt_enabled_bool (input : Var LtChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LtChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [LtChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma shiftLeft_enabled_bool (input : Var ShiftLeftChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((ShiftLeftChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [ShiftLeftChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma shiftRight_enabled_bool (input : Var ShiftRightChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((ShiftRightChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [ShiftRightChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma jal_enabled_bool (input : Var JalChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((JalChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [JalChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma jalr_enabled_bool (input : Var JalrChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((JalrChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [JalrChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma branch_enabled_bool (input : Var BranchChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((BranchChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  -- Branch's `is_real` gate is split: `assertZero (is_real - sum)` (h.1) + `assertZero (sum*(sum-1))`
  -- (h.2). `sum ∈ {0,1}` from h.2; `is_real = sum` from h.1 ⟹ `is_real ∈ {0,1}`.
  simp only [BranchChip.main, circuit_norm] at h
  rcases bool_of_mul_pred h.2 with hs | hs
  · exact Or.inl (by linear_combination h.1 + hs)
  · exact Or.inr (by linear_combination h.1 + hs)

private lemma uType_enabled_bool (input : Var UTypeChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((UTypeChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [UTypeChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma loadByte_enabled_bool (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LoadByteChip.main input).operations offset)) :
    Expression.eval env (input.is_lb + input.is_lbu) = 0 ∨ Expression.eval env (input.is_lb + input.is_lbu) = 1 := by
  simp only [LoadByteChip.main, circuit_norm] at h ⊢
  exact bool_of_mul_pred (by tauto)

private lemma loadHalf_enabled_bool (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LoadHalfChip.main input).operations offset)) :
    Expression.eval env (input.is_lh + input.is_lhu) = 0 ∨ Expression.eval env (input.is_lh + input.is_lhu) = 1 := by
  simp only [LoadHalfChip.main, circuit_norm] at h ⊢
  exact bool_of_mul_pred (by tauto)

private lemma loadWord_enabled_bool (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LoadWordChip.main input).operations offset)) :
    Expression.eval env (input.is_lw + input.is_lwu) = 0 ∨ Expression.eval env (input.is_lw + input.is_lwu) = 1 := by
  simp only [LoadWordChip.main, circuit_norm] at h ⊢
  exact bool_of_mul_pred (by tauto)

private lemma loadDouble_enabled_bool (input : Var LoadDoubleChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LoadDoubleChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [LoadDoubleChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma loadX0_enabled_bool (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((LoadX0Chip.main input).operations offset)) :
    Expression.eval env (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) = 0 ∨ Expression.eval env (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) = 1 := by
  simp only [LoadX0Chip.main, circuit_norm] at h ⊢
  exact bool_of_mul_pred (by tauto)

private lemma storeByte_enabled_bool (input : Var StoreByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((StoreByteChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [StoreByteChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma storeHalf_enabled_bool (input : Var StoreHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((StoreHalfChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [StoreHalfChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma storeWord_enabled_bool (input : Var StoreWordChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((StoreWordChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [StoreWordChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

private lemma storeDouble_enabled_bool (input : Var StoreDoubleChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((StoreDoubleChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [StoreDoubleChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma mul_enabled_bool (input : Var MulChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((MulChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [MulChip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

set_option maxHeartbeats 4000000 in
private lemma divRem_enabled_bool (input : Var DivRemChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((DivRemChip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  -- DivRem's `is_real` gate (`E355 = is_real * (is_real - 1)`) lives inside `assertZeros (ownAsserts cols)`;
  -- unfold to the per-assert conjunction (`forAllNoOffset_map_assert`) and pull out the `E355` conjunct,
  -- mirroring `DivRemChip/Soundness/Tail.lean`'s `h_own` extraction.
  simp only [DivRemChip.main, circuit_norm] at h
  simp only [DivRemChip.assertZeros, DivRemChip.forAllNoOffset_map_assert, DivRemChip.ownAsserts,
    List.forall_mem_cons] at h
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23, e29, e35, e41, e47, e48, e49, e51, e54, e57, e59,
    e61, e64, e67, e69, e70, e71, e73, e76, e79, e81, e83, e86, e89, e91, e96, e99, e103, e105, e107,
    e109, e111, e113, e115, e117, e119, e154, e157, e160, e163, e167, e171, e175, e179, e184, e189,
    e194, e199, e204, e209, e214, e219, e225, e228, e230, e232, e234, e236, e238, e240, e242, e244,
    e247, e250, e253, e256, e259, e262, e265, e268, e270, e272, e274, e276, e278, e280, e282, e284,
    e286, e288, e299, e300, e301, e302, e305, e307, e309, e311, e313, e315, e317, e319, e321, e323,
    e325, e327, e329, e331, e333, e335, e337, e339, e341, e343, e345, e347, e349, e351, e353, e355,
    e357, e359, e367, eopa0⟩ := h
  have hb := e355; simp only [circuit_norm] at hb; exact bool_of_mul_pred hb

private lemma aluX0_enabled_bool (input : Var AluX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (h : ConstraintsHold.Shallow env ((AluX0Chip.main input).operations offset)) :
    Expression.eval env (input.is_real) = 0 ∨ Expression.eval env (input.is_real) = 1 := by
  simp only [AluX0Chip.main, circuit_norm] at h
  exact bool_of_mul_pred (by tauto)

/-! ## Per-chip channel rfl-lemmas (cheap lazy projection; avoid unfolding the huge circuits) -/

private lemma add_cwg : (AddChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma add_cwr : (AddChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma addi_cwg : (AddiChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma addi_cwr : (AddiChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma addw_cwg : (AddwChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma addw_cwr : (AddwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma sub_cwg : (SubChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma sub_cwr : (SubChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma subw_cwg : (SubwChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma subw_cwr : (SubwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma bitwise_cwg : (BitwiseChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma bitwise_cwr : (BitwiseChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma lt_cwg : (LtChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma lt_cwr : (LtChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma shiftLeft_cwg : (ShiftLeftChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma shiftLeft_cwr : (ShiftLeftChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma shiftRight_cwg : (ShiftRightChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma shiftRight_cwr : (ShiftRightChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma jal_cwg : (JalChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma jal_cwr : (JalChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma jalr_cwg : (JalrChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma jalr_cwr : (JalrChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma branch_cwg : (BranchChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma branch_cwr : (BranchChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma uType_cwg : (UTypeChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma uType_cwr : (UTypeChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadByte_cwg : (LoadByteChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadByte_cwr : (LoadByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadHalf_cwg : (LoadHalfChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadHalf_cwr : (LoadHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadWord_cwg : (LoadWordChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadWord_cwr : (LoadWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadDouble_cwg : (LoadDoubleChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadDouble_cwr : (LoadDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadX0_cwg : (LoadX0Chip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma loadX0_cwr : (LoadX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeByte_cwg : (StoreByteChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeByte_cwr : (StoreByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeHalf_cwg : (StoreHalfChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeHalf_cwr : (StoreHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeWord_cwg : (StoreWordChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeWord_cwr : (StoreWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeDouble_cwg : (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma storeDouble_cwr : (StoreDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma mul_cwg : (MulChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma mul_cwr : (MulChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma divRem_cwg : (DivRemChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma divRem_cwr : (DivRemChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma aluX0_cwg : (AluX0Chip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
private lemma aluX0_cwr : (AluX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] := rfl

/-- Per-table `tables_channel` recipe: postpone the three exposed-pair witnesses, close membership
from the chip's `exposedChannels` field, and close `enabled ∈ {0,1}` via the chip's booleanity helper. -/
local macro "stateTableCase" circ:term " => " hlp:term : tactic =>
  `(tactic|
    (apply Exists.intro; apply Exists.intro; apply Exists.intro; apply And.intro
     · simp only [Component.rowInputVar_mk, Component.rowOffset_mk, $circ:term]
       exact (mem_expose_pullIf_pushIf _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
     · intro env h
       rw [Component.rowOperations_mk] at h
       exact $hlp _ _ _ h))

/-! ## The State VM (full 25-table set) -/

set_option maxHeartbeats 4000000 in
/-- The SP1 State bus as a Clean `VmTables`, over the **full** `sp1Tables` (all 25 chips). Each table's
`tables_channel` conjunct is discharged from the chip's `exposedChannels` State pair + its inline
`enabled` gate (the per-chip booleanity helpers above); `verifier_channel`/`verifier_requirements` are
trivial (`StateMsg.Spec = True`). -/
def sp1StateVmSpike : VmTables (ZMod p) SP1PublicIO where
  channel := stateChannel
  tables := sp1Tables
  verifier := sp1StateVerifier
  verifier_length_zero := by simp [circuit_norm, sp1StateVerifier]
  tables_channel := by
    simp only [sp1Tables, List.Forall]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    stateTableCase AddChip.circuit => add_enabled_bool
    stateTableCase AddiChip.circuit => addi_enabled_bool
    stateTableCase AddwChip.circuit => addw_enabled_bool
    stateTableCase SubChip.circuit => sub_enabled_bool
    stateTableCase SubwChip.circuit => subw_enabled_bool
    stateTableCase BitwiseChip.circuit => bitwise_enabled_bool
    stateTableCase LtChip.circuit => lt_enabled_bool
    stateTableCase ShiftLeftChip.circuit => shiftLeft_enabled_bool
    stateTableCase ShiftRightChip.circuit => shiftRight_enabled_bool
    stateTableCase JalChip.circuit => jal_enabled_bool
    stateTableCase JalrChip.circuit => jalr_enabled_bool
    stateTableCase BranchChip.circuit => branch_enabled_bool
    stateTableCase UTypeChip.circuit => uType_enabled_bool
    stateTableCase LoadByteChip.circuit => loadByte_enabled_bool
    stateTableCase LoadHalfChip.circuit => loadHalf_enabled_bool
    stateTableCase LoadWordChip.circuit => loadWord_enabled_bool
    stateTableCase LoadDoubleChip.circuit => loadDouble_enabled_bool
    stateTableCase LoadX0Chip.circuit => loadX0_enabled_bool
    stateTableCase StoreByteChip.circuit => storeByte_enabled_bool
    stateTableCase StoreHalfChip.circuit => storeHalf_enabled_bool
    stateTableCase StoreWordChip.circuit => storeWord_enabled_bool
    stateTableCase StoreDoubleChip.circuit => storeDouble_enabled_bool
    stateTableCase MulChip.circuit => mul_enabled_bool
    stateTableCase DivRemChip.circuit => divRem_enabled_bool
    stateTableCase AluX0Chip.circuit => aluX0_enabled_bool
  verifier_channel := by simp [circuit_norm, sp1StateVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, sp1StateVerifier, sp1StateVerifierMain, Channels.stateChannel,
      Channels.StateMsg.Spec]

private lemma sp1StateVmSpike_channel : (sp1StateVmSpike (p := p)).channel = stateChannel := rfl
private lemma sp1StateVmSpike_tables : (sp1StateVmSpike (p := p)).tables = sp1Tables := rfl
private lemma sp1StateVmSpike_verifier : (sp1StateVmSpike (p := p)).verifier = sp1StateVerifier := rfl

/-! ## The byte+program `SoundEnsemble` base + the full-VM `addVm` -/

/-- The byte- and program-finished base ensemble: chain the in-circuit program-ROM provider onto the
byte provider ensemble and finish `programChannel`. `finished = [program, byte]`. -/
def byteProgramEnsemble : SoundEnsemble (ZMod p) SP1PublicIO :=
  ByteChip.byteProviderEnsemble SP1PublicIO
    |>.addTable ⟨ProgramProviderChip.circuit⟩
        (by simp [circuit_norm, ProgramProviderChip.circuit, ByteChip.byteProviderEnsemble])
        (by simp [circuit_norm, ProgramProviderChip.circuit, ByteChip.byteProviderEnsemble])
    |>.addFinishedChannel programChannel.toRaw

/- **W11 MEMORY-FLIP — PARKED (M5 seam).** The Option-B memory flip makes every chip **pull** the memory
bus (to derive operand `isU64`), so `memoryChannel` now sits in each chip's `channelsWithGuarantees` (see the
updated `*_cwg` lemmas above). Clean's `addVm` obligation `grts_subset_finished` requires each VM table's
guarantees ⊆ `stateChannel :: finished`, but `memoryChannel` is neither the State VM channel nor a *finished*
channel — and it **cannot** be finished, because memory is itself a pull-then-push VM channel, not a
`SoundChannel` (`Air/Vm.lean` top doc). So `sp1StateVmEnsemble`/`sp1StateVm_sound` are genuinely unprovable
as-is; restoring them needs Clean's `VmTables` generalized to multi-step / multi-VM-channel so memory becomes
a *second* VM channel added alongside State (roadmap W11 "path A"). The 25-table `sp1StateVmSpike` (the
`VmTables` def itself, over the untouched State `exposedChannels`) and `byteProgramEnsemble` are KEPT above
and still build — this parks only the final `addVm` composition and its soundness corollary.

set_option maxHeartbeats 4000000 in
def sp1StateVmEnsemble : SoundVmEnsemble (ZMod p) SP1PublicIO :=
  byteProgramEnsemble.addVm sp1StateVmSpike
    (by
      simp only [circuit_norm, sp1StateVmSpike_channel, byteProgramEnsemble, ByteChip.byteProviderEnsemble,
        ProgramProviderChip.circuit, ByteChip.U8Range.circuit, ByteChip.MSB.circuit,
        ByteChip.AndByte.circuit, ByteChip.OrByte.circuit, ByteChip.XorByte.circuit,
        RangeChip.circuit8, RangeChip.circuit13, RangeChip.circuit16, RangeChip.circuit]
      refine ⟨?_, ?_⟩
      · intro hn; exact absurd hn (by decide : ¬ ("SP1State" = "SP1Program"))
      · intro hn; exact absurd hn (by decide : ¬ ("SP1State" = "SP1Byte")))
    (by
      refine ⟨by simp [circuit_norm, sp1StateVmSpike_verifier, sp1StateVerifier], ?_⟩
      simp only [sp1StateVmSpike_tables, sp1StateVmSpike_channel, sp1Tables, List.forall_mem_cons,
        add_cwg, addi_cwg, addw_cwg, sub_cwg, subw_cwg, bitwise_cwg, lt_cwg, shiftLeft_cwg, shiftRight_cwg, jal_cwg, jalr_cwg, branch_cwg, uType_cwg, loadByte_cwg, loadHalf_cwg, loadWord_cwg, loadDouble_cwg, loadX0_cwg, storeByte_cwg, storeHalf_cwg, storeWord_cwg, storeDouble_cwg, mul_cwg, divRem_cwg, aluX0_cwg]
      simp [circuit_norm, byteProgramEnsemble, ByteChip.byteProviderEnsemble, ProgramProviderChip.circuit])
    (by
      simp only [sp1StateVmSpike_tables, sp1StateVmSpike_verifier, sp1Tables, sp1StateVerifier,
        List.forall_mem_cons, add_cwr, addi_cwr, addw_cwr, sub_cwr, subw_cwr, bitwise_cwr, lt_cwr, shiftLeft_cwr, shiftRight_cwr, jal_cwr, jalr_cwr, branch_cwr, uType_cwr, loadByte_cwr, loadHalf_cwr, loadWord_cwr, loadDouble_cwr, loadX0_cwr, storeByte_cwr, storeHalf_cwr, storeWord_cwr, storeDouble_cwr, mul_cwr, divRem_cwr, aluX0_cwr]
      simp [circuit_norm, byteProgramEnsemble, ByteChip.byteProviderEnsemble, ProgramProviderChip.circuit])

theorem sp1StateVm_sound : (sp1StateVmEnsemble (p := p)).ensemble.SoundVmChannel :=
  (sp1StateVmEnsemble (p := p)).soundVmChannel

@[deprecated sp1StateVm_sound (since := "2026-06-28")]
theorem sp1StateVm_spike_sound : (sp1StateVmEnsemble (p := p)).ensemble.SoundVmChannel :=
  sp1StateVm_sound
-/

end SP1Clean.Soundness
