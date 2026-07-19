import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.ALUTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ALUTypeReaderImmutable` reader — the ALU register-adapter with op_a a **read**

Mirrors SP1's `ALUTypeReader::eval_op_a_immutable`
(`crates/core/machine/src/adapter/register/alu_type.rs:150`), used by `AluX0Chip` (ALU instructions with
`rd = x0`). op_a is a **source read**: there is no `wv*` write value, the op_a memory receive carries
`prev_value`, and the `op_a_0` gates pin the read value of `x0` to `0` (`op_a_0 * prev_value_i = 0`).
The op_b/op_c reads and the `imm_c` immediate machinery (op_c gated `is_real - imm_c`) are as in
`ALUTypeReader`.

A `FormalAssertion` (output `unit`) over the chip-owned `cols` adapter block, emitting the Program +
Memory buses (`Guarantees := True`); faithfulness to SP1's generated constraint list is the chip's
`Faithful/AluX0.lean` anchor (the reader's constraints are inlined there — `eval_op_a_immutable` is a
plain method, not an `SP1Operation`). -/

namespace SP1Clean.Readers.ALUTypeReaderImmutable

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files.
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` per operand (op_a/op_b gated `is_real`, op_c gated `is_real - imm_c`),
impose the `op_a_0` binary + the `imm_c` immediate gates, the four op_a **read**-zeroing gates
(`op_a_0 * op_a_memory.prev_value_i = 0`), and emit the Program (`is_trusted`) + Memory buses (op_a a read:
the receive carries `prev_value`, not a write value). Returns `Unit` (the adapter block `cols` is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real - cols.imm_c, input.clk_low + 2⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  (input.is_real - 1) * cols.imm_c === 0
  (input.is_real - cols.imm_c) * (input.is_real - cols.imm_c - 1) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) === 0
  cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) === 0
  -- W11 polarity flip: the Program-bus instruction fetch is now a **`pullIf`** (the ROM provider pushes &
  -- proves `ProgramMsg.RowSpec`; this reader pulls & *derives* it — the decode bounds flow into the `Spec`).
  -- Local shallow `is_trusted` boolean gate so the pull's off-gate `Requirements` are vacuous, letting
  -- `programChannel` drop from `channelsWithRequirements`. R/I-type tuple with op_c a full word + `imm_c`.
  assertZero (input.is_trusted * (input.is_trusted - 1))
  programChannel.pullIf input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, #v[cols.op_b, 0, 0, 0], cols.op_c, cols.op_a_0, 0, cols.imm_c⟩ :
      ProgramMsg (Expression (ZMod p)))
  -- `op_a_0` READ-zeroing gates (`rd = x0 ⇒ read value pinned to 0`).
  cols.op_a_0 * cols.op_a_memory.prev_value[0] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[1] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[2] === 0
  cols.op_a_0 * cols.op_a_memory.prev_value[3] === 0
  -- **W11 polarity flip:** the *read-prior* is now a `pullIf` (deriving `MemoryMsg.isU64` of the operand
  -- `prev_value`) and the *read-back* a `pushIf` (op_a/op_b/op_c are all **reads**, so every push is a
  -- read-back of the same `prev_value` — its `isU64` is discharged from the matching read-prior pull).
  -- op_a (read): pull prior value at prev timestamp, push the unchanged prior value at `clk_low + 4`.
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
  -- op_c (rs2 read), gated by `is_real - imm_c` (an immediate does no register read); index its low limb.
  memoryChannel.pullIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, input.clk_low + 2, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  -- the `localLength_eq` default (`by intros; rfl`) whnf-unfolds all of `main` (~15s on this main);
  -- the simp route proves the same goal ~100× cheaper (see compile-profile findings 2026-06-10).
  localLength_eq := by intros; simp +arith [circuit_norm, main, RegisterAccessCols.circuit]
  output _ _ := ()
  -- `byteChannel` (from the composed `RegisterAccessCols`) propagates its guarantee. `programChannel` is now
  -- **pulled** (W11 program flip), and `memoryChannel` too (W11 memory flip — the read-prior `pullIf`s derive
  -- `MemoryMsg.isU64`), so both join `channelsWithGuarantees`; memory's read-back `pushIf`s keep it in
  -- `channelsWithRequirements`.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    dsimp only [Operations.ChannelsLawful]
    refine ⟨?_, ?_, ?_⟩
    · simp only [circuit_norm, main, RegisterAccessCols.circuit]
    · intro env
      rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
      intro interaction h_interaction
      simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_interaction
      rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      all_goals exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · rw [Operations.subcircuitChannelsLawful_iff_forall]
      intro subcircuit h_subcircuit
      simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_subcircuit
      rcases h_subcircuit with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [circuit_norm]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real`/`is_trusted` binary — the precondition for the `is_real`-gated op_a/op_b byte receives and
the program-pull `is_trusted` gate. The op_c gate `is_real - imm_c` is *proven* binary in-circuit. The
decode bounds are **derived** into the `Spec` from the program pull (W11 flip), not assumed here. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1) ∧
    -- G1: the three read-back **push** access clocks (op_a at `clk_low + 4`, op_b at `+ 3`, op_c at `+ 2`)
    -- are 24-bit — the memory channel's `MemoryMsg.ClkBound` requirement. Not provable here: `clk_low` is a
    -- raw cross-block input, and the bound lives in the composing chip's `CPUState` block. The chip
    -- discharges all three with one `Readers.ClkDiscipline.of_cpuState_spec` from its `CPUState`
    -- sub-`Spec`, and soundness picks the three slots out of the named discipline below.
    -- It is gated on plain `is_real = 1`, *not* on op_c's own `is_real - imm_c = 1`
    -- multiplicity: the composing chip can only obtain the immediate gate `(is_real - 1) * imm_c = 0` from
    -- **this reader's `Spec`**, so gating that way would make the chip's discharge circular. Soundness
    -- instead derives `is_real = 1` from `is_real - imm_c = 1` in-circuit (`hreal_of_c` below).
    ClkDiscipline input.clk_low input.is_real

/-! ### `ProverData`-lifted forms

The reader keeps a uniform `GeneralFormalCircuit` interface.  Committed-ROM membership is established
globally from preprocessing and balance rather than supplied as a local prover assumption. -/

/-- The soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- The soundness spec, lifted to ignore the `unit` output and `ProverData`. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- The row-local completeness assumption. -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Assumptions input ∧ Spec input

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  simp only [circuit_norm, AssumptionsD, SpecD, Spec, memoryChannel, MemoryMsg.isU64,
    MemoryMsg.ClkBound, programChannel] at h_holds h_assumptions ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_immc, h_immbin, i0, i1, i2, i3, h_trust, h_prog,
    z0, z1, z2, z3, h_mem_a, h_mem_b, h_mem_c⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have hcbin := bool_of_mul_pred h_immbin
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- bridge the four op_a read-zeroing gates from per-limb `eval` form to value form. The memory pull
  -- guarantees / push requirements need no bridge: they are whole-`Word` `isU64`s of the message's
  -- `value` field with the eval already substituted away — `h_mem_a/b/c` feed the `Spec` and push goals.
  have eva : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env (input_var_cols_op_a_memory_prev_value[i]'hi)
        = input_cols_op_a_memory_prev_value[i]'hi := by
    intro i hi; rw [← h_input.1.2.1.1, Vector.getElem_map]
  rw [eva 0 (by norm_num)] at z0; rw [eva 1 (by norm_num)] at z1
  rw [eva 2 (by norm_num)] at z2; rw [eva 3 (by norm_num)] at z3
  -- the immediate gates bridge (op_c + op_c_memory.prev_value), as in `ALUTypeReader.soundness`.
  have hoc := h_input.1.2.2.2.2.2.1
  have hpv := h_input.1.2.2.2.2.2.2.1.1
  -- G1: the op_c **push** is gated by `is_real - imm_c`, but the chip-supplied clock bounds are gated on
  -- plain `is_real` (see `Assumptions`). The in-circuit immediate gate `h_immc` bridges the two: off a real
  -- row it forces `imm_c = 0`, so an op_c multiplicity of `1` means the row is real.
  have hreal_of_c : input_is_real - input_cols_imm_c = 1 → input_is_real = 1 := by
    intro htc
    rcases h_assumptions.1 with h | h
    · -- `h_assumptions` carries the reassembled `{record}.is_real` projection; retype it to the
      -- destructured atom (defeq by iota) so the `rw`s below match syntactically.
      have hz : input_is_real = 0 := h
      have himm : input_cols_imm_c = 0 := by rw [hz] at h_immc; simpa using h_immc
      rw [hz, himm] at htc; simp at htc
    · exact h
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, hcbin, ?_,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, h_rac_c hcbin,
      fun ht => ?_,
      fun ht2 => ⟨(h_mem_a (by rw [show input_is_real = 1 from ht2])).1,
        (h_mem_b (by rw [show input_is_real = 1 from ht2])).1,
        (h_mem_a (by rw [show input_is_real = 1 from ht2])).2,
        (h_mem_b (by rw [show input_is_real = 1 from ht2])).2⟩,
      fun ht3 => h_mem_c (by rw [show input_is_real - input_cols_imm_c = 1 from ht3])⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1, Or.inr hcbin,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous hcbin h1 h0,
    fun _ h0 => ?_⟩
  · rw [← hoc, ← hpv]; simp only [Vector.getElem_map]; exact ⟨i0, i1, i2, i3⟩
  · -- Decode bounds are exactly the structural Program-channel guarantee.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [show input_is_trusted = 1 from ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- push_a: read-back value = op_a prev, from the paired pull; push clock `clk_low + 4`.
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact ⟨(h_mem_a (by rw [ht])).1, h_assumptions.2.2.at_four ht⟩
  · -- push_b: read-back value = op_b prev, from the paired pull; push clock `clk_low + 3`.
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact ⟨(h_mem_b (by rw [ht])).1, h_assumptions.2.2.at_three ht⟩
  · -- push_c: read-back value = op_c prev, from the paired (is_real - imm_c)-gated pull; push clock
    -- `clk_low + 2`, whose `ClkBound` comes from the `is_real`-gated assumption via `hreal_of_c`.
    have htc : input_is_real - input_cols_imm_c = 1 := by
      rcases hcbin with h | h; exact absurd h h0; exact h
    exact ⟨(h_mem_c (by rw [htc])).1, h_assumptions.2.2.at_two (hreal_of_c htc)⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust, -⟩ := h_assumptions
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c,
    hdec, hisu_ab, hisu_c⟩ := h_spec
  -- `hbin`/`h_immbin_or`/`htrust` carry `{record}.field` projections (the `ProverAssumptionsD`/Contracts
  -- `Spec` reassembly); `dsimp` iota-reduces them to the destructured atoms so the `rw`-gates below match.
  dsimp only at hbin h_immbin_or htrust
  -- bridges: op_a `prev_value` limbs (the read-zeroing gates) and op_c (immediate gates); the memory
  -- pulls need none (their `isU64` obligations are whole-`Word`, eval already substituted away).
  have eva : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_a_memory_prev_value[i]'hi)
        = input_cols_op_a_memory_prev_value[i]'hi := by
    intro i hi; rw [← h_input.1.2.1.1, Vector.getElem_map]
  rw [← eva 0 (by norm_num)] at z0; rw [← eva 1 (by norm_num)] at z1
  rw [← eva 2 (by norm_num)] at z2; rw [← eva 3 (by norm_num)] at z3
  have hoc := h_input.1.2.2.2.2.2.1
  have hpv := h_input.1.2.2.2.2.2.2.1.1
  have eoc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c[i]'hi) = input_cols_op_c[i]'hi := by
    intro i hi; rw [← hoc, Vector.getElem_map]
  have epv : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c_memory_prev_value[i]'hi)
        = input_cols_op_c_memory_prev_value[i]'hi := by
    intro i hi; rw [← hpv, Vector.getElem_map]
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ⟨h_immbin_or, hrac_c⟩,
    ?_, h_immc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, z0, z1, z2, z3, ?_, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases h_immbin_or with h | h <;> rw [h] <;> simp
  · simp only [eoc, epv]; exact i0
  · simp only [eoc, epv]; exact i1
  · simp only [eoc, epv]; exact i2
  · simp only [eoc, epv]; exact i3
  · rcases htrust with h | h <;> rw [h] <;> simp     -- `is_trusted` gate
  · -- Prove the structural Program row from the semantic reader Spec.
    intro ht
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  · -- mem pull a: the guarantee pair (whole-`Word` `isU64` + the message's `clk_low`, which *is* the
    -- block's `prev_low`) is read straight off `hisu_ab`'s four-fact tuple.
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => ⟨(hisu_ab (neg_inj.mp hneg)).1, (hisu_ab (neg_inj.mp hneg)).2.2.1⟩
  · -- mem pull b
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => ⟨(hisu_ab (neg_inj.mp hneg)).2.1, (hisu_ab (neg_inj.mp hneg)).2.2.2⟩
  · -- mem pull c (gated `is_real - imm_c`): its own `Spec` conjunct is already the pair, verbatim.
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact fun hneg => hisu_c (neg_inj.mp hneg)

/-- The native immutable ALU-type reader as a Clean `GeneralFormalCircuit`: composes a `RegisterAccessCols` per
operand (op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + immediate + read-zeroing gates, and
emits the Program/Memory buses. -/
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
      refine ⟨?_, ?_, ?_⟩
      · simp only [circuit_norm, main, RegisterAccessCols.circuit]
      · intro channel h_channel
        simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_channel
        rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        all_goals exact Or.inr List.mem_cons_self
      · intro env h_constraints
        rw [constraintsHold_shallow_iff_forall_mem] at h_constraints
        have h_trusted : (ProvableStruct.eval env input_var).is_trusted = 0 ∨
            (ProvableStruct.eval env input_var).is_trusted = 1 := by
          apply bool_of_mul_pred
          have h_gate := h_constraints.1
            (input_var.is_trusted * (input_var.is_trusted - 1)) (by
              simp only [circuit_norm, main, RegisterAccessCols.circuit,
                Operations.shallowConstraints, List.mem_cons])
          simpa only [circuit_norm] using h_gate
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [circuit_norm, main, RegisterAccessCols.circuit] at h_interaction
        rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · right
          rw [ChannelInteraction.toRaw_requirements]
          intro h1 h0
          simp only [circuit_norm] at h1 h0
          exact off_gate_vacuous h_trusted h1 h0
        all_goals exact Or.inl List.mem_cons_self }

end SP1Clean.Readers.ALUTypeReaderImmutable

/-! ## Reader-local Program-fetch interface

The named Program payload plus the exact `main`-level and compositional subcircuit projections of
this reader's one Program pull.  Chip `exposedChannels_eq` proofs and `Soundness/TypedProgram.lean`
consume these instead of re-normalizing the reader; the `SP1Clean.Soundness` namespace preserves the
established names. -/

namespace SP1Clean.Soundness

open Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The immutable ALU reader emits the same fetch shape as its mutable sibling. -/
def aluTypeImmutableProgramMessage
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c, input.cols.op_a_0, 0, input.cols.imm_c⟩

theorem aluTypeReaderImmutable_programInteractions
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ALUTypeReaderImmutable.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted
        (aluTypeImmutableProgramMessage input)).toRaw] := by
  simp only [Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeImmutableProgramMessage]

theorem aluTypeReaderImmutable_programInteractions_subcircuit
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) ::
          ops) =
      (programChannel.pulledIf input.is_trusted
        (aluTypeImmutableProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    Readers.ALUTypeReaderImmutable.circuit programChannel.toRaw input offset ops _
    (aluTypeReaderImmutable_programInteractions input offset)

/-- Immutable ALU reader raw Memory list: op_a read-prior pull + read-back push at `clk_low + 4`,
op_b read-prior pull + read-back push at `clk_low + 3`, and the (`is_real - imm_c`)-gated op_c
pull/push pair at `clk_low + 2`, addressed by the low limb `op_c[0]` (an immediate does no register
read). All three operands are **reads** — no write push. -/
def aluTypeImmutableMemoryInteractions
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) :
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
       input.cols.op_b_memory.prev_value⟩).toRaw,
   (memoryChannel.pulledIf (input.is_real - input.cols.imm_c)
      ⟨input.clk_high, input.cols.op_c_memory.access_timestamp.prev_low, input.cols.op_c[0], 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf (input.is_real - input.cols.imm_c)
      ⟨input.clk_high, input.clk_low + 2, input.cols.op_c[0], 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw]

theorem aluTypeReaderImmutable_memoryInteractions
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ALUTypeReaderImmutable.circuit (p := p).main input).operations
        offset).interactionsWith memoryChannel.toRaw =
      aluTypeImmutableMemoryInteractions input := by
  simp only [Readers.ALUTypeReaderImmutable.circuit, Readers.ALUTypeReaderImmutable.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeImmutableMemoryInteractions]

theorem aluTypeReaderImmutable_memoryInteractions_subcircuit
    (input : Var Readers.ALUTypeReaderImmutable.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
        (.subcircuit
          ((Readers.ALUTypeReaderImmutable.circuit (p := p)).toSubcircuit offset input) :: ops) =
      aluTypeImmutableMemoryInteractions input ++
        Operations.interactionsWith memoryChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ALUTypeReaderImmutable.circuit memoryChannel.toRaw input offset ops _
    (aluTypeReaderImmutable_memoryInteractions input offset)

end SP1Clean.Soundness
