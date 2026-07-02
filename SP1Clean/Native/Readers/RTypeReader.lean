import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.RTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `RTypeReader` reader — the register-adapter per-row checks as a Clean `FormalCircuit`

The second real reader (sibling of `Readers/CPUState.lean`). SP1's `RTypeReader::eval`
(`crates/core/machine/src/adapter/register/r_type.rs`, mirrored in `Extracted/RTypeReader.lean`) emits
three kinds of bus interaction per ALU row:

- the **program** send (instruction fetch), gated by `is_trusted`;
- per operand (rs1 read / rs2 read / rd write), two **memory** interactions (read prev-state, write
  new-state), gated by `is_real`; and
- per operand, two **byte** timestamp checks, gated by `is_real`.

The `.program`/`.memory` interactions are trivial- or off-chip-membership (their meaning is the
trace-level multiset balance — `Soundness/ProgramConsistency.lean`, `Soundness/MemoryConsistency.lean`),
so this reader emits no Clean lookup for them. The genuine per-row constraints it imposes are:

- per operand, the two timestamp byte checks — **factored into `Readers/RegisterAccessCols.lean`**
  and composed here as three `subcircuit`s (the idiomatic fix for the inline-22-column
  `circuit_proof_start` blow-up: each sub-circuit is a `circuit_norm` black box, à la KeccakRound); and
- the four `op_a_0 * op_a_write_value[i] = 0` gates (the `rd = x0` zeroing rule).

It is a `FormalCircuit` whose **output is the `Extracted.RTypeReader` column struct** (mirroring
`AddOperation`/`CPUState`): the reader witnesses the four scalar columns (`op_a`, `op_a_0`, `op_b`,
`op_c`) and composes a `RegisterAccessCols.circuit` per operand for the six register-access columns,
returning the assembled struct so the chip composes it as a true `subcircuit` and reads the `adapter`
block straight out of the output. The cross-block inputs: `clk_low` (the recombined low clock, from the
CPUState block) and the four `op_a_write_value` limbs (`wv0..wv3`, the ALU result, for the `op_a_0`
zeroing gates). Each operand's `RegisterAccessCols.circuit` receives its access clock
`clk_low + 4/3/2` and witnesses its timestamps from it, which is what makes completeness hold for any
`clk_low`. The `is_real` binary gate stays on the chip. -/

namespace SP1Clean.Readers.RTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- `local` so this convenience instance does not leak into importing files (see `RegisterAccessTimestamp`).
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Witness the four scalar adapter columns (`op_a`, `op_a_0`, `op_b`, `op_c`, all `0`) and compose a
`RegisterAccessCols.circuit` per operand (access clocks `clk_low + 4/3/2`) — emitting columns in the
`Extracted.RTypeReader` field order so the assembled output's offsets line up. Then impose the four
`op_a_0` zeroing gates (unconditional `assertZero`, matching SP1's bare gates). Returns the assembled
`Extracted.RTypeReader` column struct. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- The adapter block `cols` is an **input** (the composing chip witnesses it); this reader witnesses
  -- nothing. Compose a `RegisterAccessCols` sub-assertion per operand on the input's nested blocks (access
  -- clocks `clk_low + 4/3/2`) for the timestamp byte checks.
  assertion RegisterAccessCols.circuit ⟨cols.op_a_memory, input.is_real, input.clk_low + 4⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_b_memory, input.is_real, input.clk_low + 3⟩
  assertion RegisterAccessCols.circuit ⟨cols.op_c_memory, input.is_real, input.clk_low + 2⟩
  -- No local range checks on the register **indices** `op_a`/`op_b`/`op_c`: SP1's R-type adapter
  -- (`crates/core/machine/src/adapter/register/r_type.rs:100-126`) does not range-check them — the index
  -- bounds (`op_a < 32`, `op_b0`/`op_c0 < 2^16`) come from the instruction *decode* / Program ROM on the
  -- receive side, not a local send. So they are *received* facts (threaded `TraceProgramLink` until the
  -- decode/ProgramChip lands), not part of the send-proven `ProgramMsg.Spec`. The `op_a_0` binary gate stays
  -- — a genuine local `assertZero` (SP1's `op_a_0` flag), and is the one index-side fact the send can prove.
  cols.op_a_0 * (cols.op_a_0 - 1) === 0
  -- W11 polarity flip: the Program-bus instruction fetch is now a **`pullIf`** (the ROM provider pushes &
  -- proves `ProgramMsg.RowSpec`; this reader pulls & *derives* it — the decode bounds flow into the `Spec`).
  -- Local shallow `is_trusted` boolean gate (faithful — SP1's adapter `assert_bool`s the program selector,
  -- `r_type.rs:100`) so the pull's off-gate `Requirements` are vacuous, letting `programChannel` drop from
  -- `channelsWithRequirements`. Arity-16 tuple: pc, opcode, the operands as register indices (R-type ⇒ the
  -- higher limbs + `imm_b`/`imm_c` are `0`), the `op_a_0` flag. (SP1 *sends* this `+1`; our pull is `−1`,
  -- bridged up-to-sign in `Faithful/RTypeReader.lean`.)
  assertZero (input.is_trusted * (input.is_trusted - 1))
  programChannel.pullIf input.is_trusted
    (⟨input.pc[0], input.pc[1], input.pc[2], input.opcode,
      cols.op_a, cols.op_b, 0, 0, 0, cols.op_c, 0, 0, 0, cols.op_a_0, 0, 0⟩ :
      ProgramMsg (Expression (ZMod p)))
  cols.op_a_0 * input.wv0 === 0
  cols.op_a_0 * input.wv1 === 0
  cols.op_a_0 * input.wv2 === 0
  cols.op_a_0 * input.wv3 === 0
  -- The five Memory-bus interactions (SP1's per-operand `send` prior-state / `receive` new-state): op_a is the
  -- `rd` **read-prior** only — its write **push** is factored OUT into `Readers/RegisterWrite.circuit`, composed
  -- by the chip *after* its operation (so the reader is a pure read and owes no `isU64 wv`; the op_a write's
  -- `isU64` flows operand→operation→result, breaking the old circularity). op_b/op_c are the `rs1`/`rs2`
  -- **reads** (value = the read-back `prev_value`). **W11 polarity flip:** the *read-prior* is a `pullIf` (the
  -- chip *derives* `MemoryMsg.isU64` of the operand `prev_value`) and the *read-back* a `pushIf` (the chip
  -- *proves* `isU64` of the pushed value, from the paired read-prior pull — same value). SP1 *sends* the
  -- read-prior (`+is_real`); our pull is `−is_real`, bridged up-to-sign in `Faithful/RTypeReader.lean`.
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_a_memory.access_timestamp.prev_low, cols.op_a, 0, 0,
      cols.op_a_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c, 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 2, cols.op_c, 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (from the composed `RegisterAccessCols` timestamp checks) propagates its *guarantee* up
  -- here. `programChannel` is now **pulled** (W11 flip), so its *guarantee* (`ProgramMsg.RowSpec`) is assumed
  -- here too. `memoryChannel` is now **pulled** too (W11 memory flip — the read-prior `pullIf`s derive
  -- `MemoryMsg.isU64`), so it joins `channelsWithGuarantees`; its read-back/write `pushIf`s keep it in
  -- `channelsWithRequirements` (they owe `isU64`).
  channelsWithGuarantees := [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by simp [circuit_norm, main, RegisterAccessCols.circuit]

-- Expose this reader's own declared channel lists + `localLength` as `@[circuit_norm]` rfl-lemmas so the
-- composing `AddChip`'s `channelsLawful` / `circuit_proof_start` is discharged automatically.
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl


/-- `is_real`/`is_trusted` binary — the byte-receive + program-pull + `is_trusted`-gate preconditions
(threaded down to the three composed `RegisterAccessCols`). Discharged by the chip's binary gates. The
decode bounds are NOT assumed here — they are **derived** into the `Spec` from the program pull (W11 flip).
No `isU64 wv` conjunct: this reader is a **pure read** (Option B) — the `op_a` write **push** is factored out
into `Readers/RegisterWrite.circuit`, which the composing chip discharges with `isU64 value` from its
operation; so all five memory interactions here are read pulls/read-backs (no write to range-check). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- After simp: `h_holds` = 3 rac subs + hbin + h_trust + h_prog (program pull) + z0..z3 (zeroing) +
  -- h_mem_a/b/c (memory pull guarantees: `-is_real = -1 → Word.isU64 {prev_value}` — the message
  -- carries the whole `Word`, so the guarantee is the Spec's `isU64` proposition verbatim).
  simp only [circuit_norm, memoryChannel, MemoryMsg.isU64, programChannel, ProgramMsg.RowSpec] at h_holds ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_trust, h_prog, z0, z1, z2, z3, h_mem_a, h_mem_b, h_mem_c⟩ :=
    h_holds
  have htbin := bool_of_mul_pred h_trust
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- Spec: pair `(decode if trusted) ∧ (isU64 trio if real)`. Requirements: 3 rac (Or.inr), program
  -- off-gate (vacuous via binary is_trusted), 3 pull off-gates (vacuous via binary is_real), 3 push reqs.
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, h_rac_c h_assumptions.1,
      ⟨fun ht => ?_, fun ht2 => ?_⟩⟩,
    Or.inr h_assumptions.1, Or.inr h_assumptions.1, Or.inr h_assumptions.1,
    fun h1 h0 => off_gate_vacuous htbin h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ?_⟩
  · -- Goal 1: is_trusted = 1 → decode bounds (from program pull guarantee)
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- Goal 2: is_real = 1 → isU64 trio — the three memory pull guarantees, verbatim
    have hneg : -input_is_real = -1 := by rw [ht2]
    exact ⟨h_mem_a hneg, h_mem_b hneg, h_mem_c hneg⟩
  · -- Goal 3: push_b requirement — same prev_value Word as the paired pull (h_mem_b)
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_b (by rw [ht])
  · -- Goal 4: push_c requirement — same pattern as push_b
    have ht : input_is_real = 1 := by
      rcases h_assumptions.1 with h | h; exact absurd h h0; exact h
    exact h_mem_c (by rw [ht])

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hreal, htrust⟩ := h_assumptions
  -- `h_spec` supplies the zeroing gates `z*`, the `op_a_0` binary `hbin`, the three `RegisterAccessCols`
  -- sub-`Spec`s, and `hdec` — now a PAIR: `(decode if trusted) ∧ (isU64 trio if real)`.
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b, hrac_c, hdec⟩ := h_spec
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ⟨hreal, hrac_c⟩, ?_, ?_, ?_, z0, z1, z2, z3, ?_, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp     -- `op_a_0` gate
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · intro ht
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec.1 (neg_inj.mp ht)
    simp only [programChannel, ProgramMsg.RowSpec]
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  -- mem_pull_a/b/c: each pull's `MemoryMsg.isU64` is `hdec.2`'s whole-Word `isU64`, verbatim (the
  -- message carries the whole `Word`, so no per-limb eval bridging).
  · exact fun hneg => (hdec.2 (neg_inj.mp hneg)).1
  · exact fun hneg => (hdec.2 (neg_inj.mp hneg)).2.1
  · exact fun hneg => (hdec.2 (neg_inj.mp hneg)).2.2

/-- The native RTypeReader reader as a Clean `FormalAssertion`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` sub-assertion per operand for the timestamp byte checks, imposes the
`op_a_0` binary + zeroing gates, and emits the Program/Memory buses, with a semantic spec. -/
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

end SP1Clean.Readers.RTypeReader
