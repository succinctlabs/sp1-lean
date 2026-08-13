import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.JTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `JTypeReader` reader — the J-type register-adapter per-row checks as a Clean `GeneralFormalCircuit`

The register adapter for **J-type** instructions (JAL, AUIPC): a destination write `op_a` (= rd) plus
**two immediates** `op_b_imm`/`op_c_imm` (no register reads). SP1's `JTypeReader::eval`
(`crates/core/machine/src/adapter/register/j_type.rs`, mirrored in `Extracted/JTypeReader.lean`) emits
per row:

- the **program** send (instruction fetch), gated by `is_trusted`, carrying `op_b_imm`/`op_c_imm` with
  `imm_b = imm_c = 1`;
- for op_a (rd write), two **memory** interactions, gated by `is_real`; and
- for op_a, two **byte** timestamp checks, gated by `is_real`.

The genuine per-row constraints are the single `RegisterAccessCols` timestamp check (composed as a
`subcircuit`), the four `op_a_0 * op_a_write_value_i = 0` zeroing gates (`rd = x0 ⇒ write 0`), and the
two selector gates emitted upstream for `is_real`/`is_trusted`. In particular, there is no standalone
`op_a_0` boolean assertion: upstream derives that fact from the Program row on trusted rows.
The `.program`/`.memory` interactions' meaning is the trace-level multiset balance. -/

namespace SP1Clean.Readers.JTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose a single `RegisterAccessCols` for op_a (write at `clk_low + 4`) for the timestamp byte checks;
impose the four zeroing gates; emit the Program bus (`imm_b = imm_c = 1`, op_b/op_c the immediate words)
and the op_a read-prior Memory interaction. The Program guarantee supplies `op_a_0` booleanity on
trusted rows, exactly as in the upstream AIR. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  -- W11 polarity flip: the Program-bus instruction fetch is now a **`pullIf`** (the ROM provider pushes &
  -- proves `ProgramMsg.RowSpec`; this reader pulls & *derives* it — the decode bounds flow into the `Spec`).
  -- Local shallow `is_trusted` boolean gate so the pull's off-gate `Requirements` are vacuous, letting
  -- `programChannel` drop from `channelsWithRequirements`. Both operand-`b`/`c` slots carry immediate words
  -- (`op_b_imm`/`op_c_imm`) with `imm_b = imm_c = 1`. `op_a` is the rd register index.
  assertZero (input.is_trusted * (input.is_trusted - 1))
  programChannel.pullIf input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b_imm, cols.op_c_imm, cols.op_a_0, 1, 1⟩ :
      ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- op_a (rd). **W11 polarity flip + Option B (pure read):** the *read-prior* is now a `pullIf` (the chip
  -- *derives* `MemoryMsg.isU64` of op_a's `prev_value`). op_a's write **push** is factored OUT into
  -- `Readers/RegisterWrite.circuit`, composed by the chip *after* its operation (so the reader owes no
  -- `isU64 wv`; the op_a write's `isU64` flows value→push at the chip level, breaking the old circularity).
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (composed `RegisterAccessCols` checks) + `programChannel` (W11 program flip — now
  -- **pulled**) + `memoryChannel` (W11 memory flip — the op_a read-prior `pullIf` derives `MemoryMsg.isU64`,
  -- so it joins `channelsWithGuarantees`). This reader has **no** memory push (the op_a write is
  -- factored into `Readers/RegisterWrite`); `memoryChannel` stays declared in the bundle's
  -- `channelsWithRequirements` below.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    dsimp only [Operations.ChannelsLawful]
    refine ⟨by simp only [circuit_norm, main, RegisterAccessCols.circuit], ?_,
      by simp only [circuit_norm, main, RegisterAccessCols.circuit]⟩
    intro env
    rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
    intro interaction h_interaction
    simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_interaction
    rcases h_interaction with rfl | rfl
    · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real`/`is_trusted` binary — the precondition for the `is_real`-gated byte receives (threaded into
the composed `RegisterAccessCols`) + the program-pull `is_trusted` gate. Discharged by the chip's binary
gates. The decode bounds are NOT assumed — they are **derived** into the `Spec` (W11 flip). No `isU64 wv`
conjunct: this reader is a **pure read** (Option B) — the op_a write **push** is factored out into
`Readers/RegisterWrite.circuit`, which the composing chip discharges with `isU64 value` from its
operation; so the lone memory interaction here is the op_a read-prior pull (no write to range-check). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

/-! ### `ProverData`-lifted forms

The reader keeps a uniform `GeneralFormalCircuit` interface, but its contract is row-local.  Committed-ROM
membership is a global preprocessing/balance fact rather than a prover assumption of this circuit. -/

/-- The soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- The soundness spec, lifted to ignore the `unit` output and `ProverData`. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- The row-local completeness assumption. -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Assumptions input ∧ Spec input

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  -- `h_holds`: the `RegisterAccessCols` sub, the inline `is_trusted` gate `h_trust`, the **program pull's
  -- guarantee** `h_prog` (`ProgramMsg.RowSpec`, including `op_a_0` booleanity), the zeroing gates, then
  -- the **memory pull's guarantee** `h_mem_a` (`MemoryMsg.isU64` of op_a's `prev_value`, and — G1 —
  -- `MemoryMsg.ClkBound` of its `prev_low` access clock).
  simp only [circuit_norm, AssumptionsD, SpecD, memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound,
    programChannel] at h_holds h_assumptions ⊢
  obtain ⟨h_rac_a, h_trust, h_prog, z0, z1, z2, z3, h_mem_a⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- Spec: decode bounds (from program pull) + op_a `isU64` **and** its prior record's 24-bit clock bound
  -- (from the memory pull — the whole-`Word` message and the message's `clk_low` *being* the block's
  -- `prev_low` make the pull guarantee pair the Spec conjunct pair verbatim). Requirements: rac (Or.inr),
  -- program off-gate (vacuous), mem pull off-gate (vacuous). This reader has **no** memory push (op_a's
  -- write is factored into `Readers/RegisterWrite.circuit`), so it owes no `ClkBound` `Assumptions`.
  refine ⟨⟨⟨z0, z1, z2, z3⟩, (fun ht => ?_),
      h_rac_a h_assumptions.1, fun ht => ?_,
      fun ht2 => h_mem_a (by rw [show input_is_real = 1 from ht2])⟩,
    Or.inr h_assumptions.1,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0⟩
  · exact (h_prog (by rw [show input_is_trusted = 1 from ht])).2.2.2.2
  -- Decode bounds are exactly the structural Program-channel guarantee.
  · obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [show input_is_trusted = 1 from ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust⟩ := h_assumptions
  -- `h_spec` supplies the zeroing gates `z*`, Program-derived conditional `op_a_0` binary `hbin`,
  -- the `RegisterAccessCols`
  -- sub-`Spec`, the gated decode bounds (now dropped — the program **pull** is supplied by `h_prog`'s
  -- `ProgTruth`, not derived from the Spec), and (W11 memory) the op_a `isU64` `hisu` — discharging the
  -- memory **pull** (the push does NOT appear in completeness goals).
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hdec, hisu⟩ := h_spec
  -- `hbin`/`htrust` carry `{record}.field` projections; `dsimp` iota-reduces them to the destructured
  -- atoms so the `rw`-gates below match.
  dsimp only at hbin htrust
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  refine ⟨⟨hreal, hrac_a⟩, ?_, ?_, z0, z1, z2, z3, ?_⟩
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · -- Prove the structural Program row from the semantic reader Spec.
    intro ht
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    exact ⟨ha, hp0, hp1, hp2, hbin (neg_inj.mp ht)⟩
  · -- mem pull: the guarantee pair (`isU64` of the whole `Word`, `ClkBound` of the message's `clk_low`,
    -- which *is* the block's `prev_low`) is the Spec's op_a conjunct pair verbatim.
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => hisu (neg_inj.mp hneg)

/-- The native J-type reader as a Clean `GeneralFormalCircuit`: composes a single `RegisterAccessCols`
for op_a, imposes the zeroing gates, and emits the Program/Memory buses. `op_a_0` booleanity is obtained
from the Program guarantee on trusted rows rather than strengthened locally. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit :=
  -- `byteChannel` dropped (W11 Phase 0c); `programChannel` dropped (W11 flip — now pulled, its off-gate
  -- requirement vacuous via the inline `is_trusted` gate). Only the Memory bus's requirements remain.
  { main, elaborated,
    Assumptions := AssumptionsD, Spec := SpecD,
    ProverAssumptions := ProverAssumptionsD, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨by simp only [circuit_norm, main, RegisterAccessCols.circuit], ?_, ?_⟩
      · intro channel h_channel
        simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_channel
        rcases h_channel with rfl | rfl
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact Or.inr List.mem_cons_self
      · intro env h_constraints
        rw [constraintsHold_shallow_iff_forall_mem] at h_constraints
        have h_trusted : (ProvableStruct.eval env input_var).is_trusted = 0 ∨
            (ProvableStruct.eval env input_var).is_trusted = 1 :=
          bool_of_mul_pred (by
            simpa only [circuit_norm] using h_constraints.1
              (input_var.is_trusted * (input_var.is_trusted - 1))
              (by simp only [circuit_norm, main, RegisterAccessCols.circuit,
                    Operations.shallowConstraints, List.mem_cons]))
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_interaction
        rcases h_interaction with rfl | rfl
        · right
          rw [ChannelInteraction.toRaw_requirements]; intro h1 h0
          simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_trusted h1 h0
        · exact Or.inl List.mem_cons_self }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.JTypeReader

/-! ## Reader-local Program-fetch interface

The named Program payload plus the exact `main`-level and compositional subcircuit projections of
this reader's one Program pull.  Chip `exposedChannels_eq` proofs and `Soundness/TypedProgram.lean`
consume these instead of re-normalizing the reader; the `SP1Clean.Soundness` namespace preserves the
established names. -/

namespace SP1Clean.Soundness

open Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- J-type reader payload: both operand words are immediates. -/
def jTypeProgramMessage (input : Var Readers.JTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    input.cols.op_b_imm, input.cols.op_c_imm, input.cols.op_a_0, 1, 1⟩

theorem jTypeReader_programInteractions (input : Var Readers.JTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.JTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (jTypeProgramMessage input)).toRaw] := by
  simp only [Readers.JTypeReader.circuit, Readers.JTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, jTypeProgramMessage]

theorem jTypeReader_programInteractions_subcircuit
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.JTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (jTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    Readers.JTypeReader.circuit programChannel.toRaw input offset ops _
    (jTypeReader_programInteractions input offset)

/-- J-type reader raw Memory list: the lone op_a (rd) read-prior pull (both operand slots carry
immediates; the op_a write push is factored into `Readers/RegisterWrite`). -/
def jTypeMemoryInteractions (input : Var Readers.JTypeReader.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [(memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_a_memory.access_timestamp.prev_low, input.cols.op_a, 0, 0,
       input.cols.op_a_memory.prev_value⟩).toRaw]

theorem jTypeReader_memoryInteractions (input : Var Readers.JTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.JTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        memoryChannel.toRaw =
      jTypeMemoryInteractions input := by
  simp only [Readers.JTypeReader.circuit, Readers.JTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, jTypeMemoryInteractions]

theorem jTypeReader_memoryInteractions_subcircuit
    (input : Var Readers.JTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
        (.subcircuit ((Readers.JTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      jTypeMemoryInteractions input ++ Operations.interactionsWith memoryChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.JTypeReader.circuit memoryChannel.toRaw input offset ops _
    (jTypeReader_memoryInteractions input offset)

end SP1Clean.Soundness
