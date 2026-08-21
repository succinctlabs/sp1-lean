import SP1Clean.FormalModel.TraceGen.Arith
import SP1Clean.Proofs.Chips.JalChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.JalChip` — from trace events to a valid AIR table

`JAL` through the trace-generation chain (see `AddChip/Complete.lean` for the programme note). It
reads the very `Extracted.JTypeReader` block `UType` reads — one register access, the `op_a` write —
so the adapter half is `UTypeChip/Complete.lean` verbatim. What is new is the **jump**.

`Jal` is the first chip of the rollout whose `next_pc` is *computed data* rather than `pc + 4`: the
row witnesses two `AddOperation` results, the jump target `pc + op_b` and the link address
`pc + 4`, and its contract asks three things about them that no reader lemma supplies —

* both results' high limbs are zero (they are program counters, committed as three u16 limbs), and
* the jump target is 4-byte aligned (the `Range(add_operation.value[0] / 4, 14)` byte pull).

Those are facts about **where the executor jumped**, so they are stated in plain `ℕ` on the event —
`JTypeEvent.JalTargets` — for exactly the reason `JTypeEvent.UTypeImm` is stated separately: they
are false for the adapter's other user. `UType`'s `op_b` is a shifted U-immediate and its `next_pc`
is `pc + 4`; nothing about `pc + op_b` is an address there. So the `JalTargets` hypothesis is
explicit and named, not smuggled into `JTypeEvent.WellFormed`.

The bridge from those `ℕ` facts to the witnessed words is `TraceGen.populate_pcWord`: SP1's
limb-wise addition at two built words is the built word of the plain sum, so each of the three
obligations becomes one `wordOfNat` lemma. -/

namespace SP1Clean.JalChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The two witnessed target words

Both are `AddOperation.populate` at the built program-counter word, so both are built words of the
executor's own wrapping sums. -/

/-- The witnessed jump target of a built row is the built word of `pc + op_b`. -/
lemma jumpTargetWord_toJalInputs {e : JTypeEvent} (h : e.pc < 2 ^ 48) :
    jumpTargetWord (e.toJalInputs (p := p)) = wordOfNat e.jalTarget := by
  rw [jumpTargetWord]
  simp only [JTypeEvent.toJalInputs_state, JTypeEvent.toJalInputs_adapter,
    jTypeReaderCols_op_b_imm]
  rw [populate_pcWord h, JTypeEvent.jalTarget]

/-- The witnessed link address of a built row is the built word of `pc + 4`. -/
lemma linkTargetWord_toJalInputs {e : JTypeEvent} (h : e.pc < 2 ^ 48) :
    linkTargetWord (e.toJalInputs (p := p)) = wordOfNat ((e.pc + 4) % 2 ^ 64) := by
  rw [linkTargetWord]
  simp only [JTypeEvent.toJalInputs_state]
  rw [wordOfNat_four, populate_pcWord h]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed `JAL` event with a legal target builds a row the honest prover can complete.**
Every conjunct of `JalChip.ProverAssumptions` at the built input row follows from
`JTypeEvent.WellFormed` together with `htgt : e.JalTargets`, with no residual side condition.

`htgt` is the one thing the J-type record cannot supply — see the module docstring.

The `data` and `hint` are arbitrary: `Jal`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : JTypeEvent} (h : e.WellFormed) (htgt : e.JalTargets)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toJalInputs (p := p)) data hint := by
  obtain ⟨htgt48, htgt4, hlink⟩ := htgt
  have hpc : e.pc < 2 ^ 48 := h.pc_lt
  refine ⟨wordOfNat_isU64 _, cpuStateCols_pcWord_isU64 e.clk e.pc, fun _ => wordOfNat_isU64 _,
    Or.inr rfl, jTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt, ?_, ?_, ?_,
    fun _ => ⟨jTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => registerAccessCols_prevLow_val_lt _ _ _⟩
  -- the jump target is a program counter: 48 bits, so the committed high limb is zero
  · rw [jumpTargetWord_toJalInputs hpc]
    exact wordOfNat_three_eq_zero htgt48
  -- so is the link address `pc + 4`
  · rw [linkTargetWord_toJalInputs hpc]
    exact wordOfNat_three_eq_zero (by omega)
  -- and the jump target is 4-byte aligned — the `Range(value[0] / 4, 14)` byte pull
  · intro _
    rw [jumpTargetWord_toJalInputs hpc]
    simpa using wordOfNat_div_four_val_lt (p := p) (n := e.jalTarget) (sub := 0) (by omega)
      (by omega)

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct vacuous;
what survives is the two operand `isU64`s, the `op_a_0` zero flag, and — because they are stated
**ungated** — the two `value[3] = 0` gates, which the zero row's two sums `0 + 0` and `0 + 4`
satisfy. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (jalPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, rfl, fun hr => absurd hr hne,
    fun hr => absurd hr hne, ?_, ?_, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne⟩ <;>
    simp [jumpTargetWord, linkTargetWord, jalPaddingInputs, zeroCPUStateCols,
      zeroJTypeReaderCols, AddOperation.populate]

/-! ## The built table -/

/-- The Jal chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List JTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map JTypeEvent.toJalInputs ++ List.replicate padding jalPaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List JTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.JalTargets) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Jal table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.JalTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.JalTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List JTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.JalChip
