import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.JTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `JTypeReader` reader — the J-type register-adapter per-row checks as a Clean `FormalAssertion`

The register adapter for **J-type** instructions (JAL, AUIPC): a destination write `op_a` (= rd) plus
**two immediates** `op_b_imm`/`op_c_imm` (no register reads). SP1's `JTypeReader::eval`
(`crates/core/machine/src/adapter/register/j_type.rs`, mirrored in `Extracted/JTypeReader.lean`) emits
per row:

- the **program** send (instruction fetch), gated by `is_trusted`, carrying `op_b_imm`/`op_c_imm` with
  `imm_b = imm_c = 1`;
- for op_a (rd write), two **memory** interactions, gated by `is_real`; and
- for op_a, two **byte** timestamp checks, gated by `is_real`.

The genuine per-row constraints are the single `RegisterAccessCols` timestamp check (composed as a
`subcircuit`) and the `op_a_0` binary + the four `op_a_0 * op_a_write_value_i = 0` zeroing gates
(`rd = x0 ⇒ write 0`). The `.program`/`.memory` interactions' meaning is the trace-level multiset balance. -/

namespace SP1Clean.Readers.JTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a single `RegisterAccessCols` for op_a (write at `clk_low + 4`) for the timestamp byte checks;
impose the `op_a_0` binary + four zeroing gates; emit the Program bus (`imm_b = imm_c = 1`, op_b/op_c the
immediate words) and the two op_a Memory interactions. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  -- W11 polarity flip: the Program-bus instruction fetch is now a **`pullIf`** (the ROM provider pushes &
  -- proves `ProgramMsg.RowSpec`; this reader pulls & *derives* it — the decode bounds flow into the `Spec`).
  -- Local shallow `is_trusted` boolean gate so the pull's off-gate `Requirements` are vacuous, letting
  -- `programChannel` drop from `channelsWithRequirements`. Both operand-`b`/`c` slots carry immediate words
  -- (`op_b_imm`/`op_c_imm`) with `imm_b = imm_c = 1`. `op_a` is the rd register index.
  assertZero (input.is_trusted * (input.is_trusted - 1))
  programChannel.pullIf input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a,
      cols.op_b_imm[0], cols.op_b_imm[1], cols.op_b_imm[2], cols.op_b_imm[3],
      cols.op_c_imm[0], cols.op_c_imm[1], cols.op_c_imm[2], cols.op_c_imm[3],
      cols.op_a_0, 1, 1⟩ : ProgramMsg (Expression (ZMod p)))
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
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (composed `RegisterAccessCols` checks) + `programChannel` (W11 program flip — now
  -- **pulled**) + `memoryChannel` (W11 memory flip — the op_a read-prior `pullIf` derives `MemoryMsg.isU64`,
  -- so it joins `channelsWithGuarantees`; its write `pushIf` keeps it in `channelsWithRequirements`).
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
the composed `RegisterAccessCols`) + the program-pull `is_trusted` gate. Discharged by the chip's binary
gates. The decode bounds are NOT assumed — they are **derived** into the `Spec` (W11 flip). No `isU64 wv`
conjunct: this reader is a **pure read** (Option B) — the op_a write **push** is factored out into
`Readers/RegisterWrite.circuit`, which the composing chip discharges with `isU64 value` from its
operation; so the lone memory interaction here is the op_a read-prior pull (no write to range-check). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `h_holds`: the `RegisterAccessCols` sub, the `op_a_0` gate `hbin`, the inline `is_trusted` gate
  -- `h_trust`, the **program pull's guarantee** `h_prog` (`ProgramMsg.RowSpec`), the zeroing gates, then the
  -- **memory pull's guarantee** `h_mem_a` (`MemoryMsg.isU64` of op_a's `prev_value`).
  simp only [circuit_norm, memoryChannel, MemoryMsg.isU64, programChannel, ProgramMsg.RowSpec]
    at h_holds ⊢
  obtain ⟨h_rac_a, hbin, h_trust, h_prog, z0, z1, z2, z3, h_mem_a⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  have eva : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_op_a_memory_prev_value[i] =
        input_cols_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.1.1; simpa using this
  -- Spec: decode bounds (from program pull) + op_a `isU64` (from memory pull). Requirements: rac (Or.inr),
  -- program off-gate (vacuous), mem pull off-gate (vacuous), mem push (wv from the `isU64 wv` Assumption).
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions.1, fun ht => ?_, fun ht2 => ?_⟩,
    Or.inr h_assumptions.1,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0⟩
  · -- decode bounds from the program pull guarantee
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- op_a `isU64` from the memory pull guarantee (pure read: no write push to range-check)
    have hneg : -input_is_real = -1 := by rw [ht2]
    obtain ⟨hma0, hma1, hma2, hma3⟩ := h_mem_a hneg
    rw [eva 0 (by norm_num)] at hma0; rw [eva 1 (by norm_num)] at hma1
    rw [eva 2 (by norm_num)] at hma2; rw [eva 3 (by norm_num)] at hma3
    exact Word.isU64_of_cases hma0 hma1 hma2 hma3

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hreal, htrust⟩ := h_assumptions
  -- `h_spec` supplies the zeroing gates `z*`, the `op_a_0` binary `hbin`, the `RegisterAccessCols`
  -- sub-`Spec`, the gated decode bounds `hdec`, and (W11 memory) the op_a `isU64` `hisu` — discharging the
  -- program **pull** and the memory **pull** (the push does NOT appear in completeness goals).
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hdec, hisu⟩ := h_spec
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  have eva : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_cols_op_a_memory_prev_value[i] =
        input_cols_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.1.1; simpa using this
  refine ⟨⟨hreal, hrac_a⟩, ?_, ?_, ?_, z0, z1, z2, z3, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp     -- `op_a_0` gate
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · intro ht
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    simp only [programChannel, ProgramMsg.RowSpec]
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  · -- mem pull: derive `MemoryMsg.isU64 {eval'd prev_a}` from hisu + eval bridge
    simp only [memoryChannel, MemoryMsg.isU64]
    intro hneg
    obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 (hisu (neg_inj.mp hneg))
    rw [eva 0 (by norm_num), eva 1 (by norm_num), eva 2 (by norm_num), eva 3 (by norm_num)]
    exact ⟨ha0, ha1, ha2, ha3⟩

/-- The native J-type reader as a Clean `FormalAssertion`: composes a single `RegisterAccessCols` for op_a
(write), imposes the `op_a_0` binary + zeroing gates, and emits the Program/Memory buses. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  -- `byteChannel` dropped (W11 Phase 0c); `programChannel` dropped (W11 flip — now pulled, its off-gate
  -- requirement vacuous via the inline `is_trusted` gate). Only the Memory bus's requirements remain.
  { main, elaborated,
    channelsWithRequirements := [memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, RegisterAccessCols.circuit, memoryChannel, programChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.JTypeReader
