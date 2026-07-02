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
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
      cols.op_a_0, 0, cols.imm_c⟩ : ProgramMsg (Expression (ZMod p)))
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
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

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
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, MemoryMsg.isU64, programChannel, ProgramMsg.RowSpec,
    sub_eq_add_neg] at h_holds ⊢
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
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, hcbin, ?_,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, h_rac_c hcbin,
      fun ht => ?_, fun ht2 => ⟨h_mem_a (by rw [ht2]), h_mem_b (by rw [ht2])⟩,
      fun ht3 => h_mem_c (by rw [ht3])⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1, Or.inr hcbin,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous hcbin h1 h0,
    fun _ h0 => ?_⟩
  · rw [← hoc, ← hpv]; simp only [Vector.getElem_map]; exact ⟨i0, i1, i2, i3⟩
  · -- the decode-bounds `Spec` conjunct is **derived** from the program pull `h_prog`.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- push_a: read-back value = op_a prev, from the paired pull.
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_a (by rw [ht])
  · -- push_b: read-back value = op_b prev, from the paired pull.
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_b (by rw [ht])
  · -- push_c: read-back value = op_c prev, from the paired (is_real - imm_c)-gated pull.
    have htc : input_is_real + -input_cols_imm_c = 1 := by
      rcases hcbin with h | h; exact absurd h h0; exact h
    exact h_mem_c (by rw [htc])

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hreal, htrust⟩ := h_assumptions
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c,
    hdec, hisu_ab, hisu_c⟩ := h_spec
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
  · -- mem pull a: the whole-`Word` `isU64` is literally hisu_ab.1 (the eval is already substituted away).
    simp only [memoryChannel, MemoryMsg.isU64]
    exact fun hneg => (hisu_ab (neg_inj.mp hneg)).1
  · -- mem pull b
    simp only [memoryChannel, MemoryMsg.isU64]
    exact fun hneg => (hisu_ab (neg_inj.mp hneg)).2
  · -- mem pull c (gated `is_real - imm_c`): likewise literally hisu_c.
    simp only [memoryChannel, MemoryMsg.isU64]
    exact fun hneg => hisu_c (neg_inj.mp hneg)

/-- The native immutable ALU-type reader as a Clean `FormalAssertion`: composes a `RegisterAccessCols` per
operand (op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + immediate + read-zeroing gates, and
emits the Program/Memory buses. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  -- `byteChannel` dropped (W11 Phase 0c); `programChannel` dropped (W11 flip — now pulled, its off-gate
  -- requirement vacuous via the inline `is_trusted` gate). Only the Memory bus's requirements remain.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, RegisterAccessCols.circuit, memoryChannel, programChannel]; grind }

end SP1Clean.Readers.ALUTypeReaderImmutable
