import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels
import SP1Clean.Extracted.RTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `RegisterAccessTimestamp` reader — one operand's timestamp columns as a Clean `FormalCircuit`

The genuinely-tiny (2-column) inner block of SP1's `RegisterAccessCols`
(`Extracted/RTypeReader.lean`): `{prev_low, diff_low_limb}`. Its own file (one circuit per file, like
`Readers/CPUState.lean`).

SP1's `eval_register_access_*` emits, per operand, two byte-bus timestamp checks
(`crates/core/machine/src/air/memory.rs`), modelled here as **`byteChannel.pull`s**
(`Model/Channels.lean`, the faithful Clean `Channel` for SP1's `send_byte` into the preprocessed
`ByteChip`), both gated by `is_real`:

- a 16-bit `Range` check on `diff_low_limb`, and
- a `U8Range` (`< 256`) check on the scaled high part
  `(clk_target - prev_low - 1 - diff_low_limb) * 65536⁻¹`.

Each is a `byteChannel.pull ⟨op, is_real·value, width, 0⟩`: a pull (multiplicity `-1`) hands soundness
the channel's `Guarantees = ByteRowSpec` of the message *for free* (the in-circuit byte-op correctness),
which the proof projects through `byteRowSpec_range`/`byteRowSpec_u8range_pair`. Gating stays in the message
(`is_real·value`): on `is_real = 1` the real bound, on `is_real = 0` the vacuous zero-row. Because a pull
can't carry a gated multiplicity (Clean fires `Guarantees` only at `mult = -1`), the byte-op correctness
is *assumed* from the channel — discharged at the ensemble/balance level (the absent `ByteChip`
provider), threaded as `Soundness/ByteConsistency.lean`'s `TraceByteLink`, exactly as the State bus
threads `TraceStateLink`. See `docs/bus-model.md` §5.

`clk_target` is the operand's access clock (`clk_low + 4/3/2` for op_a/op_b/op_c) — a cross-block
input. The witnessed columns are computed from it (`prev_low := clk_target - 1`, `diff := 0`, so the
scaled numerator is `0`), which makes completeness hold for every `clk_target`. The `.memory`
interactions are off-chip membership (trace-level, `Soundness/MemoryConsistency.lean`), so this
sub-circuit emits no lookup for them. `Readers/RegisterAccessCols.lean` wraps this with `prev_value`
and `RTypeReader` composes that 3× — factoring the register-access columns into sub-circuits is the
idiomatic fix for the inline-22-column `circuit_proof_start` cost (each sub-circuit is a `circuit_norm`
black box, à la `Clean/Gadgets/Keccak/KeccakRound.lean`). -/

namespace SP1Clean.Readers.RegisterAccessTimestamp

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `cols` block (`prev_low`, `diff_low_limb`) is an **input** (the composing chip witnesses it);
`main` witnesses nothing and imposes the two `is_real`-gated byte checks over `input.cols.*`: a 16-bit
`Range` on `diff_low_limb` and a `U8Range` (`< 256`) on the scaled high part `(clk_target - prev_low - 1 -
diff) * 65536⁻¹`. Each is a `byteChannel.pullIf` (mult `-is_real`, **raw** value — `toRaw` (gated post-#398)),
handing soundness the `ByteRowSpec` guarantee on real rows; on padding (`mult = 0`) it owes nothing. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- Local, shallow `is_real` boolean gate (faithful — SP1's `eval_register_access_*` `assert_bool`);
  -- kept inline (`assertZero`, not `=== 0`) so it is visible to `ConstraintsHold.Shallow`, discharging the
  -- off-gate byte-pull `Requirements` without keeping `byteChannel` in `channelsWithRequirements`.
  assertZero (input.is_real * (input.is_real - 1))
  byteChannel.pullIf input.is_real
    (⟨6, cols.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨3, 0, (input.clk_target - cols.prev_low - 1 - cols.diff_low_limb) *
      (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- the two timestamp byte checks are gated receives (mult `-is_real`): they give the `ByteRowSpec`
  -- guarantee on real rows AND impose a padding requirement, so `byteChannel` is in BOTH lists.
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    change Operations.ChannelsLawful
      ([.assert _, .interact _, .interact _] : Operations (ZMod p)) [byteChannel.toRaw]
    refine ⟨by simp only [circuit_norm], ?_, by simp only [circuit_norm]⟩
    · intro env
      rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
      intro interaction h_interaction
      simp only [circuit_norm] at h_interaction
      rcases h_interaction with rfl | rfl <;>
        exact Or.inl (List.mem_singleton_self byteChannel.toRaw)

-- Expose the declared channel list + `localLength` as `@[circuit_norm]` rfl-lemmas so the composing
-- `RegisterAccessCols` reader's `channelsLawful` / `circuit_proof_start` is discharged automatically.
-- (`channelsWithRequirements` now lives on `circuit` below; Clean's generic `channelsWithRequirements_def`
-- reduces it, so no per-reader rfl-lemma is needed.)
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees
      : List (RawChannel (ZMod p))) = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl


/-- `is_real` is binary — the precondition for the genuinely `is_real`-gated byte receives.
Discharged by the chip's gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  -- `Spec` = the two byte bounds (`is_real`-gated), derived from the gated-receive guarantees (which fire
  -- at `mult = -1`, i.e. `is_real = 1`); post-#398 a receive owes no padding requirement at all.
  circuit_proof_start
  simp only [circuit_norm, byteChannel] at h_holds ⊢
  -- The two trailing conjuncts are the byte pulls' own `Requirements` (post-`cedc171b`): each fires only
  -- at an off-gate multiplicity (`-is_real ∉ {0,-1}`), impossible under the binary `Assumptions` — vacuous.
  refine ⟨fun hr1 => ?_, fun h1 h0 => off_gate_vacuous h_assumptions h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions h1 h0⟩
  have hneg : - input_is_real = -1 := by rw [hr1]
  exact ⟨(byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact h_holds.2.1 hneg),
    ((byteRowSpec_u8range_pair _ _).mp (h_holds.2.2 hneg)).1⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  -- The two byte pulls' completeness obligation (their `ByteRowSpec` guarantee) only fires on real rows
  -- (`-is_real = -1`); there the `Spec` byte bounds supply it.
  circuit_proof_start
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_, ?_⟩
  · rcases h_assumptions with h | h <;> simp only [h, sub_self, mul_zero, zero_mul]
  · intro hneg
    simpa only [Nat.cast_ofNat] using (byteRowSpec_range _ sixteen_lt).mpr (h_spec (neg_inj.mp hneg)).1
  · intro hneg
    exact (byteRowSpec_u8range_pair _ _).mpr
      ⟨(h_spec (neg_inj.mp hneg)).2, by rw [ZMod.val_zero]; norm_num⟩

/-- The inner timestamp reader as a Clean `FormalAssertion`: takes the chip-owned `cols` block plus
`is_real`/`clk_target`, imposes the two `is_real`-gated byte checks, with `Spec` the two byte bounds. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate byte-pull `Requirements` are now discharged by the
  -- inline `is_real` boolean gate in `main`, so `channelsWithRequirements` is empty (this leaf reader emits
  -- only on `byteChannel`, which moves to a Clean `SoundEnsemble` byte provider later).
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      change Operations.RequirementsChannelsLawful
        ([.assert _, .interact _, .interact _] : Operations (ZMod p)) [byteChannel.toRaw] []
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨by simp only [circuit_norm], ?_, ?_⟩
      · intro channel h_channel
        -- `circuit_norm` collapses the duplicated `byteChannel` alternatives (`or_self`), so this
        -- leaves a single equation rather than the two-way disjunction the explicit list left.
        simp only [circuit_norm] at h_channel
        subst h_channel
        exact Or.inl (List.mem_singleton_self byteChannel.toRaw)
      · intro env h_constraints
        have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
            (ProvableStruct.eval env input_var).is_real = 1 := by
          apply bool_of_mul_pred
          simpa only [circuit_norm] using h_constraints.1
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [circuit_norm] at h_interaction
        rcases h_interaction with rfl | rfl <;> right <;>
          rw [ChannelInteraction.toRaw_requirements] <;>
          intro h1 h0 <;>
          simp only [circuit_norm] at h1 h0 <;>
          exact off_gate_vacuous h_bool h1 h0 }

-- This leaf reader emits only on `byteChannel`, so its interactions are empty on the Memory/Program
-- channels — the bottom-up base case that lets `RegisterAccessCols`/`RTypeReader` drop this sub-reader's
-- contribution when computing their own `interactionsWith memory/program`. Stated in `circuit.main` form
-- (the shape `Channels.interactionsWith_subcircuit_formal` leaves when a parent composes this reader).
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (n : ℕ) :
    Operations.interactionsWith (SP1Clean.Channels.memoryChannel (p := p)).toRaw
      (circuit.main input n).2 = [] := by
  simp [circuit_norm, circuit, elaborated, main]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma interactionsWith_program_eq (input : Var Inputs (ZMod p)) (n : ℕ) :
    Operations.interactionsWith (SP1Clean.Channels.programChannel (p := p)).toRaw
      (circuit.main input n).2 = [] := by
  simp [circuit_norm, circuit, elaborated, main]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.RegisterAccessTimestamp
