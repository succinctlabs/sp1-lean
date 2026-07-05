import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
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
no `wv*` write value. -/

namespace SP1Clean.Readers.ITypeReaderImmutable

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` per operand (op_a read at `clk_low + 4`, op_b read at `clk_low + 3`)
for the timestamp byte checks; impose the `op_a_0` binary + four read-zeroing gates
(`op_a_0 * prev_value_i = 0`); emit the Program bus (`imm_c = 1`) and the four Memory **read**
interactions. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
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
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

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
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

/-! ### `ProverData`-lifted forms (SC Phase 2pre)

The reader upgrades `FormalAssertion → GeneralFormalCircuit` (Output = `unit`) so its `Spec` can, in a
later phase, re-export the data-relative pull guarantees. Content UNCHANGED: `AssumptionsD`/`SpecD`
ignore the extra `ProverData`/`output`, so the soundness/completeness bodies are the old ones (modulo
the `show`/`dsimp` reductions the reassembled-record projections need). -/

/-- The soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- The soundness spec, lifted to ignore the `unit` output and `ProverData`. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- The completeness assumption (an assertion assumes both `Assumptions` and `Spec`). -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop := Assumptions input ∧ Spec input

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  -- `h_holds`: the 2 `RegisterAccessCols` subs, the `op_a_0` gate `hbin`, the inline `is_trusted` gate
  -- `h_trust`, the **program pull's guarantee** `h_prog`, the read-zeroing gates, then the two **memory pull
  -- guarantees** `h_mem_a`/`h_mem_b` (`MemoryMsg.isU64` of op_a/op_b's `prev_value`).
  simp only [circuit_norm, AssumptionsD, SpecD, memoryChannel, MemoryMsg.isU64, programChannel,
    ProgramMsg.RowSpec] at h_holds h_assumptions ⊢
  obtain ⟨h_rac_a, h_rac_b, hbin, h_trust, h_prog, z0, z1, z2, z3, h_mem_a, h_mem_b⟩ := h_holds
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
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, fun ht => ?_,
      fun ht2 => ⟨h_mem_a (by rw [show input_is_real = 1 from ht2]),
        h_mem_b (by rw [show input_is_real = 1 from ht2])⟩⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_⟩
  · -- decode bounds from the program pull guarantee
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [show input_is_trusted = 1 from ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- push_a: read-back value = op_a prev, from the paired pull
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_a (by rw [ht])
  · -- push_b: read-back value = op_b prev, from the paired pull
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_b (by rw [ht])

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust⟩ := h_assumptions
  -- `h_spec` supplies the read-zeroing gates `z*`, the `op_a_0` binary `hbin`, the two `RegisterAccessCols`
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
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ?_, ?_, ?_, z0, z1, z2, z3, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp     -- `op_a_0` gate
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · intro ht
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    simp only [programChannel, ProgramMsg.RowSpec]
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  · -- mem pull a: the whole-`Word` guarantee is the Spec's op_a `isU64` verbatim
    simp only [memoryChannel, MemoryMsg.isU64]
    exact fun hneg => (hisu (neg_inj.mp hneg)).1
  · -- mem pull b
    simp only [memoryChannel, MemoryMsg.isU64]
    exact fun hneg => (hisu (neg_inj.mp hneg)).2

/-- The native immutable I-type reader as a Clean `GeneralFormalCircuit`: composes a `RegisterAccessCols` per
operand (both reads), imposes the `op_a_0` binary + read-zeroing gates, and emits the Program/Memory buses. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit :=
  -- `byteChannel` dropped (W11 Phase 0c); `programChannel` dropped (W11 flip — now pulled, its off-gate
  -- requirement vacuous via the inline `is_trusted` gate). Only the Memory bus's requirements remain.
  { main, elaborated,
    Assumptions := AssumptionsD, Spec := SpecD,
    ProverAssumptions := ProverAssumptionsD, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, RegisterAccessCols.circuit, memoryChannel, programChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.ITypeReaderImmutable
