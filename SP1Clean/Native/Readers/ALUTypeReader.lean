import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.ALUTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ALUTypeReader` reader — the ALU register-adapter (immediate-capable op_c) as a `FormalAssertion`

The ALU-type sibling of `Readers/RTypeReader.lean`, for the ALU chips whose `op_c` may be an **immediate**
(`Addw`, `Lt`, `Bitwise`, `ShiftLeft`, `ShiftRight`). SP1's `ALUTypeReader::eval`
(mirrored in `Extracted/ALUTypeReader.lean`) is the `RTypeReader` fragment plus the immediate machinery:

- a flag `imm_c` and a **`Word`-typed** `op_c` (vs `RTypeReader`'s scalar register index);
- `imm_c` is boolean off padding (`(is_real - 1) * imm_c = 0`);
- when `imm_c = 1` the op_c "register read" is pinned to the immediate value
  (`imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0`);
- the op_c register byte/memory interactions are gated by **`is_real - imm_c`** (no register read for an
  immediate), and that multiplicity is itself asserted boolean.

Like `RTypeReader`, it is a `FormalAssertion` (output `unit`) over the **chip-owned** `cols` adapter block:
it composes a `RegisterAccessCols.circuit` per operand for the timestamp byte checks (op_a/op_b gated
`is_real`, op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + zeroing gates and the immediate
gates, and emits the Program + Memory buses (their per-row meaning is the trace-level multiset balance, so
`Guarantees := True`). The cross-block values (`clk_low`, the four `op_a_write_value` limbs `wv*`) stay
inputs; the `is_real` binary gate stays on the chip. Faithfulness to SP1's generated constraint list is the
separate `Faithful/ALUTypeReader.lean` anchor. -/

namespace SP1Clean.Readers.ALUTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files.
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Compose a `RegisterAccessCols` sub-assertion per operand (op_a/op_b gated `is_real` at clocks
`clk_low + 4/3`, op_c gated `is_real - imm_c` at `clk_low + 2`), impose the `op_a_0` binary gate, the
`imm_c` boolean/immediate gates, and emit the Program (`is_trusted`) + Memory (`±is_real`, op_c `±(is_real
- imm_c)`) buses. The op_c register index for the buses is its low limb `op_c[0]`; the four op_c word limbs
go into the Program message together with `imm_c`. Returns `Unit` (the adapter block `cols` is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- Per-operand timestamp byte checks (op_c gated by the immediate-aware `is_real - imm_c`).
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real - cols.imm_c, input.clk_low + 2⟩
  -- `op_a_0` binary (the `rd = x0` flag); `imm_c` boolean off padding; `is_real - imm_c` boolean.
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  (input.is_real - 1) * cols.imm_c === 0
  (input.is_real - cols.imm_c) * (input.is_real - cols.imm_c - 1) === 0
  -- Immediate consistency: when `imm_c = 1`, the op_c register "read" equals the immediate `op_c`.
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
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
      cols.op_a_0, 0, cols.imm_c⟩ : ProgramMsg (Expression (ZMod p)))
  -- `op_a_0` zeroing gates (`rd = x0 ⇒ write 0`).
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- Memory bus: op_a is the `rd` **read-prior** only — its write **push** is factored OUT into
  -- `Readers/RegisterWrite.circuit`, composed by the chip *after* its operation (Option B: the reader is a
  -- pure read and owes no `isU64 wv`; the op_a write's `isU64` flows operand→operation→result). op_b/op_c are
  -- the `rs1`/`rs2` reads. op_c is gated by `is_real - imm_c` (an immediate does no register read); its
  -- register index is the low limb `op_c[0]`.
  -- **W11 polarity flip:** the *read-prior* is now a `pullIf` (deriving `MemoryMsg.isU64` of the operand
  -- `prev_value`) and the *read-back* a `pushIf` (op_b/op_c from the paired read-prior pull). op_c's pull/push
  -- stay gated by `is_real - imm_c`.
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, input.clk_low + 2, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  -- the `localLength_eq` default (`by intros; rfl`) whnf-unfolds all of `main` (~15s on this main);
  -- the simp route proves the same goal ~100× cheaper (see compile-profile findings 2026-06-10).
  localLength_eq := by intros; simp +arith [circuit_norm, main, RegisterAccessCols.circuit]
  output _ _ := ()
  -- `byteChannel` (from the composed `RegisterAccessCols`) propagates its guarantee. `programChannel` is now
  -- **pulled** (W11 program flip), and `memoryChannel` too (W11 memory flip — the read-prior `pullIf`s derive
  -- `MemoryMsg.isU64`), so both join `channelsWithGuarantees`; memory's write/read-back `pushIf`s keep it in
  -- `channelsWithRequirements`.
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real`/`is_trusted` binary — the precondition for the `is_real`-gated op_a/op_b byte receives
(threaded into the two composed `RegisterAccessCols`) and the program-pull `is_trusted` gate. The op_c gate
`is_real - imm_c` is *proven* binary in-circuit. The decode bounds are **derived** into the `Spec` from the
program pull (W11 flip), not assumed here. No `isU64 wv` conjunct: this reader is a **pure read** (Option B)
— the op_a **write** push is factored out into `Readers/RegisterWrite.circuit`, which the composing chip
discharges with `isU64 value` from its operation; so all five memory interactions here are read
pulls/read-backs (no write to range-check). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `sub_eq_add_neg` on the goal aligns its `is_real - 1` / `is_real - imm_c` (HSub) with the `+ -1`
  -- form `circuit_norm` leaves in `h_holds`; the immediate-gate `Word` indexing is bridged below.
  simp only [circuit_norm, memoryChannel, MemoryMsg.isU64, programChannel, ProgramMsg.RowSpec,
    sub_eq_add_neg] at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_immc, h_immbin, i0, i1, i2, i3, h_trust, h_prog,
    z0, z1, z2, z3, h_mem_a, h_mem_b, h_mem_c⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have hcbin := bool_of_mul_pred h_immbin
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- bridge each operand `prev_value` limb from `eval` form to its value (used for the Spec `isU64` outputs).
  have eva : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_op_a_memory_prev_value[i] =
        input_cols_op_a_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.1.1; simpa using this
  have evb : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_op_b_memory_prev_value[i] =
        input_cols_op_b_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2.2.1.1; simpa using this
  have evc : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_op_c_memory_prev_value[i] =
        input_cols_op_c_memory_prev_value[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2.2.2.2.1.1; simpa using this
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, hcbin, ?_,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, h_rac_c hcbin,
      fun ht => ?_, fun ht2 => ?_, fun ht3 => ?_⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1, Or.inr hcbin,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous hcbin h1 h0,
    fun _ h0 => ?_⟩
  · -- the four immediate gates: bridge `input_cols_op_c[i]` / `…prev_value[i]` (value-level) to the
    -- `Expression.eval env …[i]` form `h_holds` carries, via the `h_input` Word equalities + `getElem_map`.
    rw [← h_input.1.2.2.2.2.2.1, ← h_input.1.2.2.2.2.2.2.1.1]
    simp only [Vector.getElem_map]; exact ⟨i0, i1, i2, i3⟩
  · -- the decode-bounds `Spec` conjunct is **derived** from the program pull `h_prog`.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- op_a/op_b `isU64` from the two `is_real`-gated memory pull guarantees.
    have hneg : -input_is_real = -1 := by rw [ht2]
    obtain ⟨hma0, hma1, hma2, hma3⟩ := h_mem_a hneg
    obtain ⟨hmb0, hmb1, hmb2, hmb3⟩ := h_mem_b hneg
    rw [eva 0 (by norm_num)] at hma0; rw [eva 1 (by norm_num)] at hma1
    rw [eva 2 (by norm_num)] at hma2; rw [eva 3 (by norm_num)] at hma3
    rw [evb 0 (by norm_num)] at hmb0; rw [evb 1 (by norm_num)] at hmb1
    rw [evb 2 (by norm_num)] at hmb2; rw [evb 3 (by norm_num)] at hmb3
    exact ⟨Word.isU64_of_cases hma0 hma1 hma2 hma3, Word.isU64_of_cases hmb0 hmb1 hmb2 hmb3⟩
  · -- op_c `isU64` from the `is_real - imm_c`-gated memory pull guarantee.
    have hnegc : -(input_is_real + -input_cols_imm_c) = -1 := by rw [ht3]
    obtain ⟨hmc0, hmc1, hmc2, hmc3⟩ := h_mem_c hnegc
    rw [evc 0 (by norm_num)] at hmc0; rw [evc 1 (by norm_num)] at hmc1
    rw [evc 2 (by norm_num)] at hmc2; rw [evc 3 (by norm_num)] at hmc3
    exact Word.isU64_of_cases hmc0 hmc1 hmc2 hmc3
  · -- push_b requirement — same eval'd prev_value as the paired pull (h_mem_b).
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_b (by rw [ht])
  · -- push_c requirement — same eval'd prev_value as the paired (is_real - imm_c)-gated pull (h_mem_c).
    have htc : input_is_real + -input_cols_imm_c = 1 := by
      rcases hcbin with h | h; exact absurd h h0; exact h
    exact h_mem_c (by rw [htc])

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hreal, htrust⟩ := h_assumptions
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c,
    hdec, hisu_ab, hisu_c⟩ := h_spec
  -- Align the `Spec`'s HSub (`-`) hyps with the goal's `circuit_norm` `+ -` form, and bridge the immediate
  -- gates' `input_cols_op_c[i]` (value) to the `Expression.eval env …[i]` form via the `h_input` Word eqs.
  have hoc := h_input.1.2.2.2.2.2.1
  have hpv := h_input.1.2.2.2.2.2.2.1.1
  have eoc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c[i]'hi) = input_cols_op_c[i]'hi := by
    intro i hi; rw [← hoc, Vector.getElem_map]
  have epv : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c_memory_prev_value[i]'hi)
        = input_cols_op_c_memory_prev_value[i]'hi := by
    intro i hi; rw [← hpv, Vector.getElem_map]
  -- bridge op_a/op_b `prev_value` limbs (for the two `is_real`-gated memory pulls).
  have eva : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_a_memory_prev_value[i]'hi)
        = input_cols_op_a_memory_prev_value[i]'hi := by
    intro i hi; rw [← h_input.1.2.1.1, Vector.getElem_map]
  have evb : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_b_memory_prev_value[i]'hi)
        = input_cols_op_b_memory_prev_value[i]'hi := by
    intro i hi; rw [← h_input.1.2.2.2.2.1.1, Vector.getElem_map]
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  simp only [sub_eq_add_neg] at h_immc h_immbin_or hrac_c i0 i1 i2 i3 hisu_c
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ⟨h_immbin_or, hrac_c⟩,
    ?_, h_immc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, z0, z1, z2, z3, ?_, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases h_immbin_or with h | h <;> rw [h] <;> simp
  · simp only [eoc, epv]; exact i0
  · simp only [eoc, epv]; exact i1
  · simp only [eoc, epv]; exact i2
  · simp only [eoc, epv]; exact i3
  · rcases htrust with h | h <;> rw [h] <;> simp     -- `is_trusted` gate
  · intro ht                                         -- program **pull** guarantee
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    simp only [programChannel, ProgramMsg.RowSpec]
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  · -- mem pull a: derive `MemoryMsg.isU64 {eval'd prev_a}` from hisu_ab.1 + eval bridge.
    simp only [memoryChannel, MemoryMsg.isU64]
    intro hneg
    obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 (hisu_ab (neg_inj.mp hneg)).1
    rw [eva 0 (by norm_num), eva 1 (by norm_num), eva 2 (by norm_num), eva 3 (by norm_num)]
    exact ⟨ha0, ha1, ha2, ha3⟩
  · -- mem pull b
    simp only [memoryChannel, MemoryMsg.isU64]
    intro hneg
    obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 (hisu_ab (neg_inj.mp hneg)).2
    rw [evb 0 (by norm_num), evb 1 (by norm_num), evb 2 (by norm_num), evb 3 (by norm_num)]
    exact ⟨hb0, hb1, hb2, hb3⟩
  · -- mem pull c (gated `is_real - imm_c`): derive from hisu_c + the op_c eval bridge `epv`.
    simp only [memoryChannel, MemoryMsg.isU64]
    intro hneg
    obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 (hisu_c (neg_inj.mp hneg))
    rw [epv 0 (by norm_num), epv 1 (by norm_num), epv 2 (by norm_num), epv 3 (by norm_num)]
    exact ⟨hc0, hc1, hc2, hc3⟩

/-- The native ALUTypeReader reader as a Clean `FormalAssertion`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` per operand (op_c gated by `is_real - imm_c`), imposes the `op_a_0` +
immediate gates, and emits the Program/Memory buses, with a semantic spec. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  -- `byteChannel` dropped (W11 Phase 0c); `programChannel` dropped (W11 flip — now pulled, its off-gate
  -- requirement vacuous via the inline `is_trusted` gate). Only the Memory bus's requirements remain.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, RegisterAccessCols.circuit, memoryChannel, programChannel]; grind }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.ALUTypeReader
