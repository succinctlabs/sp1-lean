import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Extracted.ALUTypeReader
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `ALUTypeReader` reader — the ALU register-adapter (immediate-capable op_c) as a `GeneralFormalCircuit`

The ALU-type sibling of `Readers/RTypeReader.lean`, for the ALU chips whose `op_c` may be an **immediate**
(`Addw`, `Lt`, `Bitwise`, `ShiftLeft`, `ShiftRight`). SP1's `ALUTypeReader::eval`
(mirrored in `Extracted/ALUTypeReader.lean`) is the `RTypeReader` fragment plus the immediate machinery:

- a flag `imm_c` and a **`Word`-typed** `op_c` (vs `RTypeReader`'s scalar register index);
- `imm_c` is boolean off padding (`(is_real - 1) * imm_c = 0`);
- when `imm_c = 1` the op_c "register read" is pinned to the immediate value
  (`imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0`);
- the op_c register byte/memory interactions are gated by **`is_real - imm_c`** (no register read for an
  immediate), and that multiplicity is itself asserted boolean.

Like `RTypeReader`, it is a `GeneralFormalCircuit` (output `unit`) over the **chip-owned** `cols` adapter block:
it composes a `RegisterAccessCols.circuit` per operand for the timestamp byte checks (op_a/op_b gated
`is_real`, op_c gated `is_real - imm_c`), imposes the `op_a_0` binary + zeroing gates and the immediate
gates, and pulls/pushes the Program + Memory buses (deriving the structural `RowSpec` and
`isU64 ∧ ClkBound` guarantees from its pulls — the W11 polarity flips). The cross-block values
(`clk_low`, the four `op_a_write_value` limbs `wv*`) stay
inputs; the `is_real` binary gate stays on the chip. Faithfulness to SP1's generated constraint list is the
separate `Faithful/ALUTypeReader.lean` anchor. -/

namespace SP1Clean.Readers.ALUTypeReader

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Component-wise evaluation of the ALU reader input bundle.  Keeping this folded projection next
to the reader avoids repeatedly normalizing the derived `ProvableStruct` instance in whole-chip
faithfulness proofs. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ cols := Eval.eval env input.cols, is_real := Eval.eval env input.is_real,
         is_trusted := Eval.eval env input.is_trusted,
         clk_high := Eval.eval env input.clk_high, clk_low := Eval.eval env input.clk_low,
         pc := Eval.eval env input.pc, opcode := Eval.eval env input.opcode,
         wv0 := Eval.eval env input.wv0, wv1 := Eval.eval env input.wv1,
         wv2 := Eval.eval env input.wv2, wv3 := Eval.eval env input.wv3 } :
        Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the nested register-access block. -/
@[circuit_norm] theorem eval_accessCols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.RegisterAccessCols (Expression F)) :
    Eval.eval env cols =
      ({ prev_value := Eval.eval env cols.prev_value,
         access_timestamp := Eval.eval env cols.access_timestamp } :
        Extracted.RegisterAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Component-wise evaluation of the canonical immediate-capable ALU reader row.  Chip-level
grounding proofs use this folded boundary instead of normalizing a completed reader circuit. -/
@[circuit_norm] theorem eval_cols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.ALUTypeReader (Expression F)) :
    Eval.eval env cols =
      ({ op_a := Eval.eval env cols.op_a,
         op_a_memory := Eval.eval env cols.op_a_memory,
         op_a_0 := Eval.eval env cols.op_a_0,
         op_b := Eval.eval env cols.op_b,
         op_b_memory := Eval.eval env cols.op_b_memory,
         op_c := Eval.eval env cols.op_c,
         op_c_memory := Eval.eval env cols.op_c_memory,
         imm_c := Eval.eval env cols.imm_c } : Extracted.ALUTypeReader F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-- Evaluation of the destination-zero routing flag through the folded ALU reader row. -/
@[circuit_norm] theorem eval_opA0 {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.ALUTypeReader (Expression F)) :
    (Eval.eval env cols).op_a_0 = Expression.eval env cols.op_a_0 := by
  simp only [circuit_norm]

/-- Scalar immediate-selector projection through the folded ALU reader row. -/
@[circuit_norm] theorem eval_immC {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.ALUTypeReader (Expression F)) :
    (Eval.eval env cols).imm_c = Expression.eval env cols.imm_c := by
  simp only [circuit_norm]

/-- Source-C word projection through the folded ALU reader row. -/
@[circuit_norm] theorem eval_opC {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.ALUTypeReader (Expression F)) :
    (Eval.eval env cols).op_c = Eval.eval env cols.op_c := by
  rw [eval_cols]

/-- Source-C prior-value projection through the folded nested register-access row. -/
@[circuit_norm] theorem eval_opCPrev {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.ALUTypeReader (Expression F)) :
    (Eval.eval env cols).op_c_memory.prev_value =
      Eval.eval env cols.op_c_memory.prev_value := by
  rw [eval_cols]
  change (Eval.eval env cols.op_c_memory).prev_value =
    Eval.eval env cols.op_c_memory.prev_value
  rw [eval_accessCols]

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
      cols.op_a, #v[cols.op_b, 0, 0, 0], cols.op_c, cols.op_a_0, 0, cols.imm_c⟩ :
      ProgramMsg (Expression (ZMod p)))
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
      cols.op_a_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf input.is_real
    (⟨input.clk_high, cols.op_b_memory.access_timestamp.prev_low, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 3, cols.op_b, 0, 0,
      cols.op_b_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pullIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, cols.op_c_memory.access_timestamp.prev_low, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf (input.is_real - cols.imm_c)
    (⟨input.clk_high, input.clk_low + 2, cols.op_c[0], 0, 0,
      cols.op_c_memory.prev_value⟩ : MemoryMsg (Expression (ZMod p)))

set_option linter.unusedSectionVars false in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ FlatOperation.constraints
      (((Gadgets.Equality.main (M := field) (x, y)).operations offset).toFlat) := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  exact List.mem_singleton_self _

/-- The reader's four immediate-consistency assertions bind the retained source-C value whenever
`imm_c = 1`.  This is a physical AIR fact, exposed without invoking the reader's semantic `Spec` or
any Memory guarantee, so `advanceReady` proofs can consume it before timed Memory grounding. -/
theorem eval_opCPrev_eq_opC_of_mainConstraints
    (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env ((main input).operations offset))
    (immediate : Expression.eval env input.cols.imm_c = 1) :
    Eval.eval env input.cols.op_c_memory.prev_value = Eval.eval env input.cols.op_c := by
  have limb (i : Fin 4) :
      Expression.eval env input.cols.op_c_memory.prev_value[i] =
        Expression.eval env input.cols.op_c[i] := by
    have constrained :
        Expression.eval env
          (input.cols.imm_c *
            (input.cols.op_c_memory.prev_value[i] - input.cols.op_c[i]) - 0) = 0 := by
      apply constraints.1
      simp only [main, circuit_norm]
      fin_cases i
      · right; right; right; right; right; right; left
        simpa only [Gadgets.Equality.circuit, FormalAssertion.toSubcircuit,
          Operations.toNested_toFlat] using equalityConstraint_mem _ 0 _
      · right; right; right; right; right; right; right; left
        simpa only [Gadgets.Equality.circuit, FormalAssertion.toSubcircuit,
          Operations.toNested_toFlat] using equalityConstraint_mem _ 0 _
      · right; right; right; right; right; right; right; right; left
        simpa only [Gadgets.Equality.circuit, FormalAssertion.toSubcircuit,
          Operations.toNested_toFlat] using equalityConstraint_mem _ 0 _
      · right; right; right; right; right; right; right; right; right; left
        simpa only [Gadgets.Equality.circuit, FormalAssertion.toSubcircuit,
          Operations.toNested_toFlat] using equalityConstraint_mem _ 0 _
    simp only [eval_sub, Expression.eval, immediate, one_mul, sub_zero] at constrained
    exact sub_eq_zero.mp constrained
  apply Vector.ext
  intro i hi
  have left := ProvableType.getElem_eval_fields env input.cols.op_c_memory.prev_value i hi
  have right := ProvableType.getElem_eval_fields env input.cols.op_c i hi
  exact left.symm.trans ((limb ⟨i, hi⟩).trans right)

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
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_trusted = 0 ∨ input.is_trusted = 1) ∧
    -- G1: the two read-back **push** access clocks (op_b at `clk_low + 3`, op_c at `clk_low + 2`) are
    -- 24-bit — the memory channel's `MemoryMsg.ClkBound` requirement. Not provable here: `clk_low` is a
    -- raw cross-block input, and the bound lives in the composing chip's `CPUState` block. The chip
    -- discharges both with one `Readers.ClkDiscipline.of_cpuState_spec` from its `CPUState` sub-`Spec`,
    -- and soundness picks the two slots out of the named discipline below.
    -- It is gated on plain `is_real = 1`, *not* on op_c's own `is_real - imm_c = 1` multiplicity: the
    -- composing chip can only obtain the immediate gate `(is_real - 1) * imm_c = 0` from **this reader's
    -- `Spec`**, so gating the assumption that way would make the chip's discharge circular. Soundness
    -- instead derives `is_real = 1` from `is_real - imm_c = 1` in-circuit (`hreal_of_c` below).
    ClkDiscipline input.clk_low input.is_real

/-! ### `ProverData`-lifted forms

The reader keeps a uniform `GeneralFormalCircuit` interface.  Committed-ROM membership is grounded
globally from preprocessing and balance rather than supplied as a local prover assumption. -/

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
  -- `sub_eq_add_neg` on the goal aligns its `is_real - 1` / `is_real - imm_c` (HSub) with the `+ -1`
  -- form `circuit_norm` leaves in `h_holds`; the immediate-gate `Word` indexing is bridged below.
  -- `AssumptionsD`/`SpecD` unfold to the data-free content in the same `circuit_norm` pass. Unlike
  -- `RTypeReader`, the `SpecD`-folded goal keeps `Spec` opaque over a reassembled record, so `sub_eq_add_neg`
  -- can't reach its `is_real - imm_c` HSub subtractions to align them with the `+ -` form `circuit_norm`
  -- leaves in `h_holds` — unfold `Spec` here too so the projections reduce and `sub_eq_add_neg` fires.
  simp only [circuit_norm, AssumptionsD, SpecD, Spec, memoryChannel, MemoryMsg.isU64,
    MemoryMsg.ClkBound, programChannel] at h_holds h_assumptions ⊢
  obtain ⟨h_rac_a, h_rac_b, h_rac_c, hbin, h_immc, h_immbin, i0, i1, i2, i3, h_trust, h_prog,
    z0, z1, z2, z3, h_mem_a, h_mem_b, h_mem_c⟩ := h_holds
  have htbin := bool_of_mul_pred h_trust
  have hcbin := bool_of_mul_pred h_immbin
  have e : ∀ i (hi : i < 3), Expression.eval env input_var_pc[i] = input_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.2.2.2.2.2.1; simpa using this
  -- G1: the op_c **push** is gated by `is_real - imm_c`, but the chip-supplied clock bounds are gated on
  -- plain `is_real` (see `Assumptions`). The immediate gate `(is_real - 1) * imm_c = 0` — available here as
  -- the in-circuit `h_immc` — bridges the two: off a real row it forces `imm_c = 0`, so the op_c
  -- multiplicity is `0`, and a multiplicity of `1` therefore means the row is real.
  have hreal_of_c : input_is_real - input_cols_imm_c = 1 → input_is_real = 1 := by
    intro htc
    refine h_assumptions.1.resolve_left fun h => ?_
    -- `h_assumptions` carries the reassembled `{record}.is_real` projection; retype it to the
    -- destructured atom (defeq by iota) so the `rw`s below match syntactically.
    have hz : input_is_real = 0 := h
    have himm : input_cols_imm_c = 0 := by rw [hz] at h_immc; simpa using h_immc
    rw [hz, himm] at htc; simp at htc
  -- The pull guarantees / push requirements are pairs: the whole-`Word` `isU64` of the message's `value`
  -- field (the eval already substituted away) and the `ClkBound` of its `clk_low` field — which for a
  -- read-prior pull *is* the block's `prev_low`, and for a read-back push is `clk_low + 3` / `+ 2`.
  refine ⟨⟨⟨z0, z1, z2, z3⟩, bool_of_mul_pred hbin, h_immc, hcbin, ?_,
      h_rac_a h_assumptions.1, h_rac_b h_assumptions.1, h_rac_c hcbin,
      fun ht => ?_,
      fun ht2 => ⟨(h_mem_a (by rw [ht2])).1, (h_mem_b (by rw [ht2])).1,
        (h_mem_a (by rw [ht2])).2, (h_mem_b (by rw [ht2])).2⟩,
      fun ht3 => h_mem_c (by rw [ht3])⟩,
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
  · -- Decode bounds are exactly the structural Program-channel guarantee.
    obtain ⟨ha, hp0, hp1, hp2, _⟩ := h_prog (by rw [ht])
    rw [e 0 (by norm_num)] at hp0; rw [e 1 (by norm_num)] at hp1; rw [e 2 (by norm_num)] at hp2
    exact ⟨ha, hp0, hp1, hp2⟩
  · -- push_b requirement — same whole-`Word` prev_value as the paired pull (h_mem_b), pushed at
    -- `clk_low + 3`, whose `ClkBound` is the chip-supplied assumption.
    have ht : input_is_real = 1 := h_assumptions.1.resolve_left h0
    exact ⟨(h_mem_b (by rw [ht])).1, h_assumptions.2.2.at_three ht⟩
  · -- push_c requirement — same whole-`Word` prev_value as the paired (is_real - imm_c)-gated pull
    -- (h_mem_c), pushed at `clk_low + 2`; its `ClkBound` comes from the `is_real`-gated assumption via
    -- `hreal_of_c`.
    have htc : input_is_real - input_cols_imm_c = 1 := hcbin.resolve_left h0
    exact ⟨(h_mem_c (by rw [htc])).1, h_assumptions.2.2.at_two (hreal_of_c htc)⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  obtain ⟨hreal, htrust, -⟩ := h_assumptions
  obtain ⟨⟨z0, z1, z2, z3⟩, hbin, h_immc, h_immbin_or, ⟨i0, i1, i2, i3⟩, hrac_a, hrac_b, hrac_c,
    hdec, hisu_ab, hisu_c⟩ := h_spec
  -- `hbin`/`htrust` carry `{record}.field` projections (the `ProverAssumptionsD`/Contracts `Spec`
  -- reassembly); `dsimp` iota-reduces them to the destructured atoms so the `rw`-gates below match.
  dsimp only at hbin htrust
  -- Align the `Spec`'s HSub (`-`) hyps with the goal's `circuit_norm` `+ -` form, and bridge the immediate
  -- gates' `input_cols_op_c[i]` (value) to the `Expression.eval env …[i]` form via the `h_input` Word eqs.
  have eoc : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c[i]'hi) = input_cols_op_c[i]'hi := by
    intro i hi; rw [← h_input.1.2.2.2.2.2.1, Vector.getElem_map]
  have epv : ∀ (i : ℕ) (hi : i < 4),
      Expression.eval env.toEnvironment (input_var_cols_op_c_memory_prev_value[i]'hi)
        = input_cols_op_c_memory_prev_value[i]'hi := by
    intro i hi; rw [← h_input.1.2.2.2.2.2.2.1.1, Vector.getElem_map]
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

/-- The native ALUTypeReader reader as a Clean `GeneralFormalCircuit`: takes the chip-owned `cols` adapter block,
composes a `RegisterAccessCols` per operand (op_c gated by `is_real - imm_c`), imposes the `op_a_0` +
immediate gates, and emits the Program/Memory buses, with a semantic spec. -/
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

end SP1Clean.Readers.ALUTypeReader

/-! ## Reader-local Program-fetch interface

The named Program payload plus the exact `main`-level and compositional subcircuit projections of
this reader's one Program pull.  Chip `exposedChannels_eq` proofs and `Soundness/TypedProgram.lean`
consume these instead of re-normalizing the reader; the `SP1Clean.Soundness` namespace preserves the
established names. -/

namespace SP1Clean.Soundness

open Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The immediate-capable ALU reader's Program payload. -/
def aluTypeProgramMessage (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) :
    ProgramMsg (Expression (ZMod p)) :=
  ⟨input.pc[0], input.pc[1], input.pc[2], input.opcode, input.cols.op_a,
    #v[input.cols.op_b, 0, 0, 0], input.cols.op_c, input.cols.op_a_0, 0, input.cols.imm_c⟩

theorem aluTypeReader_programInteractions (input : Var Readers.ALUTypeReader.Inputs (ZMod p))
    (offset : ℕ) :
    ((Readers.ALUTypeReader.circuit (p := p).main input).operations offset).interactionsWith
        programChannel.toRaw =
      [(programChannel.pulledIf input.is_trusted (aluTypeProgramMessage input)).toRaw] := by
  simp only [Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeProgramMessage]

theorem aluTypeReader_programInteractions_subcircuit
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith programChannel.toRaw
        (.subcircuit ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      (programChannel.pulledIf input.is_trusted (aluTypeProgramMessage input)).toRaw ::
        Operations.interactionsWith programChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact
    Readers.ALUTypeReader.circuit programChannel.toRaw input offset ops _
    (aluTypeReader_programInteractions input offset)

/-- ALU reader raw Memory list: op_a read-prior pull, op_b read-prior pull + read-back push at
`clk_low + 3`, and the (`is_real - imm_c`)-gated op_c pull/push pair at `clk_low + 2`, addressed by
the low limb `op_c[0]` (an immediate does no register read).  The op_a **write** push is factored out
into `Readers/RegisterWrite.circuit` (Option B), so this list carries five read-side entries. -/
def aluTypeMemoryInteractions
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) :
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
   (memoryChannel.pulledIf (input.is_real - input.cols.imm_c)
      ⟨input.clk_high, input.cols.op_c_memory.access_timestamp.prev_low, input.cols.op_c[0], 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw,
   (memoryChannel.pushedIf (input.is_real - input.cols.imm_c)
      ⟨input.clk_high, input.clk_low + 2, input.cols.op_c[0], 0, 0,
       input.cols.op_c_memory.prev_value⟩).toRaw]

theorem aluTypeReader_memoryInteractions
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ALUTypeReader.circuit (p := p).main input).operations
        offset).interactionsWith memoryChannel.toRaw =
      aluTypeMemoryInteractions input := by
  simp only [Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]
  simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    decide_false, Bool.false_eq_true, List.nil_append, aluTypeMemoryInteractions]

theorem aluTypeReader_memoryInteractions_subcircuit
    (input : Var Readers.ALUTypeReader.Inputs (ZMod p)) (offset : ℕ)
    (ops : Operations (ZMod p)) :
    Operations.interactionsWith memoryChannel.toRaw
        (.subcircuit
          ((Readers.ALUTypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      aluTypeMemoryInteractions input ++
        Operations.interactionsWith memoryChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ALUTypeReader.circuit memoryChannel.toRaw input offset ops _
    (aluTypeReader_memoryInteractions input offset)

end SP1Clean.Soundness
