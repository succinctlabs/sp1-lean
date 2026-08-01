import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.ITypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ITypeReaderImmutable` reader — the store-adapter per-row checks as a Clean `GeneralFormalCircuit`

The register adapter for **stores** (and any I-type op where `op_a` is a source read): `op_a` = rs2 read,
`op_b` = rs1 read, `op_c_imm` = immediate. Reuses the `Extracted.ITypeReader` column struct. SP1's
`ITypeReaderImmutable::eval` (`crates/core/machine/src/adapter/register/i_type.rs`, mirrored in
`Extracted/ITypeReaderImmutable.lean`) has op_a as a **read**: the receive carries `prev_value`, the
`op_a_0` zeroing gates pin the *read* value of `x0` to `0` (`op_a_0 * prev_value_i = 0`), and there is
no `wv*` write value. As upstream, `op_a_0` booleanity comes from the Program row rather than a
standalone reader assertion. -/

namespace SP1Clean.Readers.ITypeReaderImmutable

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Compose a `RegisterAccessCols` per operand (op_a read at `clk_low + 4`, op_b read at `clk_low + 3`)
for the timestamp byte checks; impose the four read-zeroing gates (`op_a_0 * prev_value_i = 0`);
emit the Program bus (`imm_c = 1`) and the four Memory **read** interactions. The Program guarantee
supplies `op_a_0` booleanity on trusted rows. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  -- W11 polarity flip: the Program-bus instruction fetch is now a **`pullIf`** (the ROM provider pushes &
  -- proves `ProgramMsg.RowSpec`; this reader pulls & *derives* it — the decode bounds flow into the `Spec`).
  -- Local shallow `is_trusted` boolean gate so the pull's off-gate `Requirements` are vacuous, letting
  -- `programChannel` drop from `channelsWithRequirements`. op_a is a source **read** (rs2), op_b the rs1
  -- register index; the operand-`c` slots carry the immediate word `op_c_imm` with `imm_c = 1`.
  assertZero (input.is_trusted * (input.is_trusted - 1))
  programChannel.pullIf input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, #v[cols.op_b, 0, 0, 0], cols.op_c_imm, cols.op_a_0, 0, 1⟩ :
      ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * cols.op_a_memory.prev_value[0] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[1] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[2] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[3] === 0
  -- **W11 polarity flip:** the *read-prior* is now a `pullIf` (the chip *derives* `MemoryMsg.isU64` of the
  -- operand `prev_value`) and the *read-back* a `pushIf` (op_a/op_b are both **reads**, so every push is a
  -- read-back of the same `prev_value` — its `isU64` is discharged directly from the matching read-prior pull).
  -- op_a (rs2 read): pull prior value at prev timestamp, push the unchanged prior value at `clk_low + 4`.
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 4, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  -- op_b (rs1 read): pull prior value, push the unchanged prior value at `clk_low + 3`.
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (composed `RegisterAccessCols` checks) + `programChannel` (W11 program flip — now
  -- **pulled**) + `memoryChannel` (W11 memory flip — the read-prior `pullIf`s derive `MemoryMsg.isU64`,
  -- so it joins `channelsWithGuarantees`; its read-back `pushIf`s keep it in `channelsWithRequirements`).
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
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real`/`is_trusted` binary — the precondition for the `is_real`-gated byte receives (threaded into
the two composed `RegisterAccessCols`) + the program-pull `is_trusted` gate. Discharged by the chip's
binary gates. The decode bounds are NOT assumed — they are **derived** into the `Spec` (W11 flip). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1) ∧
    -- G1: the two read-back **push** access clocks (op_a at `clk_low + 4`, op_b at `clk_low + 3`) are
    -- 24-bit — the memory channel's `MemoryMsg.ClkBound` requirement. Not provable here: `clk_low` is a
    -- raw cross-block input, and the bound lives in the composing chip's `CPUState` block. Assumed as the
    -- named `Readers.ClkDiscipline` (uniform across the readers); soundness picks the two slots below.
    ClkDiscipline input.clk_low input.is_real

/-! ### `ProverData`-lifted forms

The reader keeps a uniform `GeneralFormalCircuit` interface, while committed-ROM membership is grounded
globally from preprocessing and balance rather than supplied to this local circuit. -/

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
  -- `h_holds`: the 2 `RegisterAccessCols` subs, the inline `is_trusted` gate `h_trust`, the **program
  -- pull's guarantee** `h_prog` (including `op_a_0` booleanity), the read-zeroing gates, then the two **memory pull
  -- guarantees** `h_mem_a`/`h_mem_b` — now PAIRS: `MemoryMsg.isU64` of op_a/op_b's `prev_value` and — G1 —
  -- `MemoryMsg.ClkBound` of each prior record's `prev_low` access clock.
  simp only [circuit_norm, AssumptionsD, SpecD, memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound,
    programChannel] at h_holds h_assumptions ⊢
  obtain ⟨h_rac_a, h_rac_b, h_trust, h_prog, z0, z1, z2, z3, h_mem_a, h_mem_b⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- bridge the four `op_a_0 * prev_value_i` read-zeroing gates from `eval` form to value form
  -- (the gates index into the nested `prev_value` vector limb-wise).
  have eva : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_op_a_memory_prev_value[i] =
        input_cols_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.1.1; simpa using this
  rw [eva 0 (by norm_num)] at z0; rw [eva 1 (by norm_num)] at z1
  rw [eva 2 (by norm_num)] at z2; rw [eva 3 (by norm_num)] at z3
  -- Spec: decode bounds (program pull) + op_a/op_b `isU64` (memory pulls — the whole-`Word` messages make
  -- the pull guarantees the Spec conjuncts verbatim). Requirements: 2 rac, program off-gate, then per
  -- operand a pull off-gate (vacuous) + a push (op_a/op_b both reads → read-back = pull).
  refine ⟨⟨⟨z0, z1, z2, z3⟩, (fun ht => ?_),
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, fun ht => ?_,
      fun ht2 => ⟨(h_mem_a (by rw [show input_is_real = 1 from ht2])).1,
        (h_mem_b (by rw [show input_is_real = 1 from ht2])).1,
        (h_mem_a (by rw [show input_is_real = 1 from ht2])).2,
        (h_mem_b (by rw [show input_is_real = 1 from ht2])).2⟩⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_⟩
  · exact (h_prog (by rw [show input_is_trusted = 1 from ht])).2.2.2.2
  · -- Decode bounds are exactly the structural Program-channel guarantee.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [show input_is_trusted = 1 from ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- push_a: read-back value = op_a prev, from the paired pull; its push clock `clk_low + 4`'s
    -- `ClkBound` is the chip-supplied assumption.
    have ht : input_is_real = 1 := h_assumptions.1.resolve_left h0
    exact ⟨(h_mem_a (by rw [ht])).1, h_assumptions.2.2.at_four ht⟩
  · -- push_b: read-back value = op_b prev, from the paired pull; push clock `clk_low + 3`.
    have ht : input_is_real = 1 := h_assumptions.1.resolve_left h0
    exact ⟨(h_mem_b (by rw [ht])).1, h_assumptions.2.2.at_three ht⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust, -⟩ := h_assumptions
  -- `h_spec` supplies the read-zeroing gates `z*`, the Program-derived conditional `op_a_0` binary
  -- `hbin`, the two `RegisterAccessCols`
  -- sub-`Spec`s, the gated decode bounds `hdec`, and (W11 memory) the op_a/op_b `isU64` `hisu` — discharging
  -- the program **pull** and the two memory **pulls** (the pushes do NOT appear in completeness goals).
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b, hdec, hisu⟩ := h_spec
  -- `hbin`/`htrust` carry `{record}.field` projections (the `ProverAssumptionsD`/Contracts `Spec`
  -- reassembly); `dsimp` iota-reduces them to the destructured atoms so the `rw`-gates below match.
  dsimp only at hbin htrust
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  have eva : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[i] =
        input_cols_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.1.1; simpa using this
  -- bridge the read-zeroing gates from value form (in `Spec`) to `eval` form (the goal asserts).
  rw [← eva 0 (by norm_num)] at z0; rw [← eva 1 (by norm_num)] at z1
  rw [← eva 2 (by norm_num)] at z2; rw [← eva 3 (by norm_num)] at z3
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ?_, ?_, z0, z1, z2, z3, ?_, ?_⟩
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · -- Prove the structural Program row from the semantic reader Spec.
    intro ht
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    exact ⟨ha, hp0, hp1, hp2, hbin (neg_inj.mp ht)⟩
  · -- mem pull a: the guarantee pair (whole-`Word` `isU64` + the message `clk_low`, which *is* the block's
    -- `prev_low`) is read straight off the `Spec`'s gated four-fact tuple.
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => ⟨(hisu (neg_inj.mp hneg)).1, (hisu (neg_inj.mp hneg)).2.2.1⟩
  · -- mem pull b
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => ⟨(hisu (neg_inj.mp hneg)).2.1, (hisu (neg_inj.mp hneg)).2.2.2⟩

/-- The native immutable I-type reader as a Clean `GeneralFormalCircuit`: composes a
`RegisterAccessCols` per operand (both reads), imposes the read-zeroing gates, and emits the
Program/Memory buses. `op_a_0` booleanity is obtained from the Program guarantee on trusted rows. -/
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
        rcases h_channel with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        all_goals exact Or.inr List.mem_cons_self
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
        rcases h_interaction with rfl | rfl | rfl | rfl | rfl
        · right
          rw [ChannelInteraction.toRaw_requirements]; intro h1 h0
          simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_trusted h1 h0
        all_goals exact Or.inl List.mem_cons_self }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [(memoryChannel (p := p)).toRaw] := rfl

end SP1Clean.Readers.ITypeReaderImmutable

/-! ## Reader-local Program-fetch interface

The named Program payload plus the exact `main`-level and compositional subcircuit projections of
this reader's one Program pull.  Chip `exposedChannels_eq` proofs and `Soundness/TypedProgram.lean`
consume these instead of re-normalizing the reader; the `SP1Clean.Soundness` namespace preserves the
established names. -/

namespace SP1Clean.Soundness

open Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Immutable I-type reader payload. -/
def iTypeImmutableProgramMessage (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c_imm, input.cols.op_a_0, 0, 1⟩

theorem iTypeReaderImmutable_programInteractions
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted
        (iTypeImmutableProgramMessage input)).toRaw] := by
  simp only [Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, iTypeImmutableProgramMessage]

theorem iTypeReaderImmutable_programInteractions_subcircuit
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) ::
          ops) =
      (programChannel.pulledIf input.is_trusted
        (iTypeImmutableProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    Readers.ITypeReaderImmutable.circuit programChannel.toRaw input offset ops _
    (iTypeReaderImmutable_programInteractions input offset)

/-- Immutable I-type reader raw Memory list: op_a (rs2) read-prior pull + read-back push at
`clk_low + 4`, then op_b (rs1) read-prior pull + read-back push at `clk_low + 3` (both operands are
**reads** — no write push). -/
def iTypeImmutableMemoryInteractions (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [(memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_a_memory.access_timestamp.prev_low, input.cols.op_a, 0, 0,
       input.cols.op_a_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf input.is_real
      ⟨input.clk_high, input.clk_low + 4, input.cols.op_a, 0, 0,
       input.cols.op_a_memory.prev_value⟩).toRaw,
   (memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_b_memory.access_timestamp.prev_low, input.cols.op_b, 0, 0,
       input.cols.op_b_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf input.is_real
      ⟨input.clk_high, input.clk_low + 3, input.cols.op_b, 0, 0,
       input.cols.op_b_memory.prev_value⟩).toRaw]

theorem iTypeReaderImmutable_memoryInteractions
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReaderImmutable.circuit (p := p).main input).operations offset).interactionsWith
        memoryChannel.toRaw =
      iTypeImmutableMemoryInteractions input := by
  simp only [Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, iTypeImmutableMemoryInteractions]

theorem iTypeReaderImmutable_memoryInteractions_subcircuit
    (input : Var Readers.ITypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
        (.subcircuit ((Readers.ITypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) ::
          ops) =
      iTypeImmutableMemoryInteractions input ++
        Operations.interactionsWith memoryChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ITypeReaderImmutable.circuit memoryChannel.toRaw input offset ops _
    (iTypeReaderImmutable_memoryInteractions input offset)

end SP1Clean.Soundness
