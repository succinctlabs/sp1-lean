import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.RTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `RTypeReader` reader — the register-adapter per-row checks as a Clean `GeneralFormalCircuit`

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

It is a **zero-witness** `GeneralFormalCircuit` (`Unit` output): the chip threads the whole
`Extracted.RTypeReader` column struct in as the `cols` input, and the reader composes a
`RegisterAccessCols.circuit` per operand over the six register-access columns — every sub-circuit a
true Clean `subcircuit` boundary. The cross-block inputs: `clk_low` (the recombined low clock, from the
CPUState block) and the four `op_a_write_value` limbs (`wv0..wv3`, the ALU result, for the `op_a_0`
zeroing gates). Each operand's `RegisterAccessCols.circuit` receives its access clock
`clk_low + 4/3/2`; the chip's witness closure computes the timestamp columns from it, which is what
makes completeness hold for any `clk_low`. The `is_real` binary gate stays on the chip. -/

namespace SP1Clean.Readers.RTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Component-wise evaluation of the canonical R-type reader row.  Kept beside the native reader so
soundness and faithfulness clients share one folded evaluator boundary. -/
@[circuit_norm] theorem eval_cols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    Eval.eval env cols =
      ({ op_a := Eval.eval env cols.op_a,
         op_a_memory := Eval.eval env cols.op_a_memory,
         op_a_0 := Eval.eval env cols.op_a_0,
         op_b := Eval.eval env cols.op_b,
         op_b_memory := Eval.eval env cols.op_b_memory,
         op_c := Eval.eval env cols.op_c,
         op_c_memory := Eval.eval env cols.op_c_memory } : Extracted.RTypeReader F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of one nested register-access block. -/
@[circuit_norm] theorem eval_registerAccessCols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RegisterAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value,
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.RegisterAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the innermost register timestamp block. -/
@[circuit_norm] theorem eval_registerAccessTimestamp {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RegisterAccessTimestamp (Expression F)) :
    Eval.eval env cols =
      ({ prev_low := Eval.eval env cols.prev_low,
         diff_low_limb := Eval.eval env cols.diff_low_limb } :
        Extracted.RegisterAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-! The six per-operand timestamp projections below all cross the same two folded boundaries
(`RegisterAccessCols` then `RegisterAccessTimestamp`); the two helpers do that crossing once over a
loose block.  Going through `simp only [circuit_norm]` instead blows the heartbeat budget — the
folded `rw` chain is what keeps the nested `Eval.eval` opaque. -/

private theorem evalPrevLow_aux {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RegisterAccessCols (Expression F)) :
    (Eval.eval env cols).access_timestamp.prev_low =
      Expression.eval env cols.access_timestamp.prev_low := by
  calc
    _ = (Eval.eval env cols.access_timestamp).prev_low := by rw [eval_registerAccessCols]
    _ = Eval.eval env cols.access_timestamp.prev_low := by rw [eval_registerAccessTimestamp]
    _ = _ := by simp only [circuit_norm]

private theorem evalDiffLow_aux {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RegisterAccessCols (Expression F)) :
    (Eval.eval env cols).access_timestamp.diff_low_limb =
      Expression.eval env cols.access_timestamp.diff_low_limb := by
  calc
    _ = (Eval.eval env cols.access_timestamp).diff_low_limb := by rw [eval_registerAccessCols]
    _ = Eval.eval env cols.access_timestamp.diff_low_limb := by rw [eval_registerAccessTimestamp]
    _ = _ := by simp only [circuit_norm]

/-- Evaluation of the canonical zero-register indicator through the folded reader row. -/
@[circuit_norm] theorem eval_opA0 {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_a_0 = Expression.eval env cols.op_a_0 := by
  simp only [circuit_norm]

@[circuit_norm] theorem eval_opAPrevLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_a_memory.access_timestamp.prev_low =
      Expression.eval env cols.op_a_memory.access_timestamp.prev_low := by
  rw [eval_cols]
  exact evalPrevLow_aux env cols.op_a_memory

@[circuit_norm] theorem eval_opADiffLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_a_memory.access_timestamp.diff_low_limb =
      Expression.eval env cols.op_a_memory.access_timestamp.diff_low_limb := by
  rw [eval_cols]
  exact evalDiffLow_aux env cols.op_a_memory

@[circuit_norm] theorem eval_opBPrevLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_b_memory.access_timestamp.prev_low =
      Expression.eval env cols.op_b_memory.access_timestamp.prev_low := by
  rw [eval_cols]
  exact evalPrevLow_aux env cols.op_b_memory

@[circuit_norm] theorem eval_opBDiffLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_b_memory.access_timestamp.diff_low_limb =
      Expression.eval env cols.op_b_memory.access_timestamp.diff_low_limb := by
  rw [eval_cols]
  exact evalDiffLow_aux env cols.op_b_memory

@[circuit_norm] theorem eval_opCPrevLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_c_memory.access_timestamp.prev_low =
      Expression.eval env cols.op_c_memory.access_timestamp.prev_low := by
  rw [eval_cols]
  exact evalPrevLow_aux env cols.op_c_memory

@[circuit_norm] theorem eval_opCDiffLow {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RTypeReader (Expression F)) :
    (Eval.eval env cols).op_c_memory.access_timestamp.diff_low_limb =
      Expression.eval env cols.op_c_memory.access_timestamp.diff_low_limb := by
  rw [eval_cols]
  exact evalDiffLow_aux env cols.op_c_memory

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
      cols.op_a, #v[cols.op_b, 0, 0, 0], #v[cols.op_c, 0, 0, 0], cols.op_a_0, 0, 0⟩ :
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
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

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
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1) ∧
    -- G1: the two read-back **push** access clocks (op_b at `clk_low + 3`, op_c at `+ 2`) are 24-bit —
    -- the memory channel's `MemoryMsg.ClkBound` requirement. Not provable here: `clk_low` is a raw
    -- cross-block input, and the bound lives in the composing chip's `CPUState` block. Assumed as the
    -- named `Readers.ClkDiscipline` (offsets `≤ 4`, uniform across the readers) rather than as this
    -- reader's two numeric offsets, so the chip supplies one `ClkDiscipline.of_cpuState_spec` and
    -- soundness picks the two slots it needs out of it below.
    ClkDiscipline input.clk_low input.is_real

/-! ### `ProverData`-lifted forms

The reader keeps the uniform `GeneralFormalCircuit` interface, while its local contract is independent
of the committed program.  ROM membership is established once, globally, from preprocessing and balance. -/

/-- The soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- The soundness spec, lifted to ignore the `unit` output and `ProverData`. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- The completeness assumption for the row-local reader. -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Assumptions input ∧ Spec input

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  -- After simp: `h_holds` = 3 rac subs + hbin + h_trust + h_prog (program pull) + z0..z3 (zeroing) +
  -- h_mem_a/b/c (memory pull guarantees: `-is_real = -1 → Word.isU64 {prev_value}` — the message
  -- carries the whole `Word`, so the guarantee is the Spec's `isU64` proposition verbatim).
  -- `AssumptionsD`/`SpecD` unfold to the data-free content in the same `circuit_norm` pass.
  simp only [circuit_norm, AssumptionsD, SpecD, memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound,
    programChannel] at h_holds h_assumptions ⊢
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
  · -- Decode bounds are exactly the structural Program-channel guarantee.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [show input_is_trusted = 1 from ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- Goal 2: is_real = 1 → isU64 trio + the three pulled records' 24-bit clock bounds — the three
    -- memory pull guarantees (`isU64 ∧ ClkBound`), verbatim.
    have hneg : - input_is_real = -1 := by rw [show input_is_real = 1 from ht2]
    exact ⟨(h_mem_a hneg).1, (h_mem_b hneg).1, (h_mem_c hneg).1,
      (h_mem_a hneg).2, (h_mem_b hneg).2, (h_mem_c hneg).2⟩
  · -- Goal 3: push_b requirement — the same prev_value Word as the paired pull (h_mem_b), pushed at
    -- `clk_low + 3`, whose `ClkBound` is the chip-supplied assumption.
    have ht : input_is_real = 1 := h_assumptions.1.resolve_left h0
    exact ⟨(h_mem_b (by rw [ht])).1, h_assumptions.2.2.at_three ht⟩
  · -- Goal 4: push_c requirement — same pattern as push_b, at `clk_low + 2`.
    have ht : input_is_real = 1 := h_assumptions.1.resolve_left h0
    exact ⟨(h_mem_c (by rw [ht])).1, h_assumptions.2.2.at_two ht⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust, -⟩ := h_assumptions
  -- `h_spec` supplies the zeroing gates `z*`, the `op_a_0` binary `hbin`, the three `RegisterAccessCols`
  -- sub-`Spec`s, and `hdec` — now a PAIR: `(decode if trusted) ∧ (isU64 trio if real)`.
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, hrac_a, hrac_b, hrac_c, hdec, hisu⟩ := h_spec
  -- `hbin`/`htrust` carry `{record}.field` projections (the `ProverAssumptionsD`/Contracts `Spec`
  -- reassembly); `dsimp` iota-reduces them to the destructured atoms so the `rw`-gates below match.
  dsimp only at hbin htrust
  have e : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  refine ⟨⟨hreal, hrac_a⟩, ⟨hreal, hrac_b⟩, ⟨hreal, hrac_c⟩, ?_, ?_, ?_, z0, z1, z2, z3, ?_, ?_, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp     -- `op_a_0` gate
  · rcases htrust with h | h <;> rw [h] <;> simp   -- `is_trusted` gate
  · -- Completeness proves the structural Program row from the reader's semantic Spec.
    intro ht
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    obtain ⟨ha, hp0, hp1, hp2⟩ := hdec (neg_inj.mp ht)
    exact ⟨ha, hp0, hp1, hp2, hbin⟩
  -- mem_pull_a/b/c: each pull's `MemoryMsg.isU64 ∧ MemoryMsg.ClkBound` is read straight off the
  -- `Spec`'s gated six-fact tuple (the message carries the whole `Word`, so no per-limb eval bridging,
  -- and its `clk_low` *is* the block's `prev_low`).
  · exact fun hneg => ⟨(hisu (neg_inj.mp hneg)).1, (hisu (neg_inj.mp hneg)).2.2.2.1⟩
  · exact fun hneg => ⟨(hisu (neg_inj.mp hneg)).2.1, (hisu (neg_inj.mp hneg)).2.2.2.2.1⟩
  · exact fun hneg => ⟨(hisu (neg_inj.mp hneg)).2.2.1, (hisu (neg_inj.mp hneg)).2.2.2.2.2⟩

/-- The native RTypeReader reader as a Clean `GeneralFormalCircuit`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` sub-assertion per operand for the timestamp byte checks, imposes the
`op_a_0` binary + zeroing gates, and emits the Program/Memory buses, with a semantic spec. -/
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
        rcases h_channel with rfl | rfl | rfl | rfl | rfl | rfl
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
        rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl
        · right
          rw [ChannelInteraction.toRaw_requirements]; intro h1 h0
          simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_trusted h1 h0
        all_goals exact Or.inl List.mem_cons_self }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.RTypeReader

/-! ## Reader-local Program-fetch interface

The named Program payload plus the exact `main`-level and compositional subcircuit projections of
this reader's one Program pull.  Chip `exposedChannels_eq` proofs and `Soundness/TypedProgram.lean`
consume these instead of re-normalizing the reader; the `SP1Clean.Soundness` namespace preserves the
established names. -/

namespace SP1Clean.Soundness

open Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The R-type reader's Program payload, named once for compositional chip proofs. -/
def rTypeProgramMessage (input : Var Readers.RTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], #v[input.cols.op_c, 0, 0, 0], input.cols.op_a_0, 0, 0⟩

/-- Exact Program interaction of the R-type reader, before it is composed by a chip. -/
theorem rTypeReader_programInteractions (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.RTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw] := by
  simp only [Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append,
    rTypeProgramMessage]

/-- Compositional R-type form: retain the reader's fetch and append the surrounding operations. -/
theorem rTypeReader_programInteractions_subcircuit
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.RTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (rTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    Readers.RTypeReader.circuit programChannel.toRaw input offset ops _
    (rTypeReader_programInteractions input offset)

/-- R-type reader raw Memory list: the destination read-prior pull, followed by the two source
register read-prior/read-back pairs.  The destination write push is deliberately outside the reader
and is supplied by `Readers.RegisterWrite.circuit` after the chip has computed its result. -/
def rTypeMemoryInteractions (input : Var Readers.RTypeReader.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [(memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_a_memory.access_timestamp.prev_low, input.cols.op_a, 0, 0,
       input.cols.op_a_memory.prev_value⟩).toRaw,
   (memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_b_memory.access_timestamp.prev_low, input.cols.op_b, 0, 0,
       input.cols.op_b_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf input.is_real
      ⟨input.clk_high, input.clk_low + 3, input.cols.op_b, 0, 0,
       input.cols.op_b_memory.prev_value⟩).toRaw,
   (memoryChannel.pulledIf input.is_real
      ⟨input.clk_high, input.cols.op_c_memory.access_timestamp.prev_low, input.cols.op_c, 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf input.is_real
      ⟨input.clk_high, input.clk_low + 2, input.cols.op_c, 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw]

theorem rTypeReader_memoryInteractions (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.RTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        memoryChannel.toRaw =
      rTypeMemoryInteractions input := by
  simp only [Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, rTypeMemoryInteractions]

theorem rTypeReader_memoryInteractions_subcircuit
    (input : Var Readers.RTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
        (.subcircuit ((Readers.RTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      rTypeMemoryInteractions input ++ Operations.interactionsWith memoryChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.RTypeReader.circuit memoryChannel.toRaw input offset ops _
    (rTypeReader_memoryInteractions input offset)

end SP1Clean.Soundness
