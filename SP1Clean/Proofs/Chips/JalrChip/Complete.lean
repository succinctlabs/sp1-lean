import SP1Clean.FormalModel.TraceGen.Arith
import SP1Clean.Proofs.Chips.JalrChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.JalrChip` — from trace events to a valid AIR table

`JALR` through the trace-generation chain (see `AddChip/Complete.lean` for the programme note, and
`JalChip/Complete.lean` for the jump half). It reads the ordinary `Extracted.ITypeReader` block —
the same one `Addi` and the nine memory chips read — so the adapter half is `Addi`'s verbatim, at
both register-access offsets.

The jump differs from `JAL`'s in exactly one way, and it is the interesting one: the base is a
**register**, and RISC-V clears the target's low bit before jumping (`next_pc = (rs1 + imm) & !1`).
So the row witnesses a third cell, `lsb`, reading back the low bit of its own `add_operation`
result, and the alignment pull is on the *cleared* target `(value[0] - lsb) / 4`. That is why the
event predicate is `ITypeEvent.JalrTargets` rather than `JTypeEvent.JalTargets`: its alignment
conjunct is taken after the clearing, which is exactly RISC-V's rule for `JALR`.

As for `Jal`, the three target obligations are facts about *where the executor jumped*, false for
every other user of the shared `ITypeReader` record (an `Addi` sum is an arbitrary 64-bit value, a
load's is an address but not an aligned instruction address), so they are an explicit named
hypothesis rather than a `WellFormed` conjunct. -/

namespace SP1Clean.JalrChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The witnessed words of a built row -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The jump base of a built row is the built word of the `rs1` read. -/
lemma rs1WordI_toJalrInputs (e : ITypeEvent) :
    rs1WordI (e.toJalrInputs (p := p)) = wordOfNat e.b := by
  rw [rs1WordI]
  simp only [ITypeEvent.toJalrInputs_adapter, iTypeReaderCols_op_b_memory,
    registerAccessCols_prev_value]
  exact word_eta _

/-- The witnessed jump target of a built row is the built word of `rs1 + imm` — the **uncleared**
sum the chip's `AddOperation` computes. -/
lemma jumpTargetWord_toJalrInputs (e : ITypeEvent) :
    jumpTargetWord (e.toJalrInputs (p := p)) = wordOfNat e.jalrTarget := by
  rw [jumpTargetWord, rs1WordI_toJalrInputs]
  simp only [ITypeEvent.toJalrInputs_adapter, iTypeReaderCols_op_c_imm]
  rw [populate_wordOfNat, ITypeEvent.jalrTarget]

/-- The witnessed link address of a built row is the built word of `pc + 4`. -/
lemma linkTargetWord_toJalrInputs {e : ITypeEvent} (h : e.pc < 2 ^ 48) :
    linkTargetWord (e.toJalrInputs (p := p)) = wordOfNat ((e.pc + 4) % 2 ^ 64) := by
  rw [linkTargetWord]
  simp only [ITypeEvent.toJalrInputs_state]
  rw [wordOfNat_four, populate_pcWord h]

/-- The committed `lsb` witness of a built row is the target's own low bit. -/
lemma lsbBit_toJalrInputs (e : ITypeEvent) :
    lsbBit (e.toJalrInputs (p := p)) = ((e.jalrTarget % 2 : ℕ) : ZMod p) := by
  rw [lsbBit, jumpTargetWord_toJalrInputs, wordOfNat_zero_val,
    Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ∣ 2 ^ 16)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed `JALR` event with a legal target builds a row the honest prover can complete.**
Every conjunct of `JalrChip.ProverAssumptions` at the built input row follows from
`ITypeEvent.WellFormedJalr` together with `htgt : e.JalrTargets`, including the
`jalr x0, rs1, imm` form, with no residual side condition.

The `data` and `hint` are arbitrary: `Jalr`'s prover contract reads neither.
-/
theorem proverAssumptions_of_event {e : ITypeEvent} (h : e.WellFormedJalr) (htgt : e.JalrTargets)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toJalrInputs (p := p)) data hint := by
  obtain ⟨htgt48, htgt4, hlink⟩ := htgt
  have hpc : e.pc < 2 ^ 48 := h.pc_lt
  refine ⟨wordOfNat_isU64 _, ?_, cpuStateCols_pcWord_isU64 e.clk e.pc,
    fun _ => wordOfNat_isU64 _, Or.inr rfl, ?_,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt,
    registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt, ?_, ?_, ?_,
    fun _ => ⟨iTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩,
    fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _, registerAccessCols_prevLow_val_lt _ _ _⟩⟩
  -- the `rs1` operand word, spelled limb by limb in the contract
  · show Word.isU64 (rs1WordI (e.toJalrInputs (p := p)))
    rw [rs1WordI_toJalrInputs]
    exact wordOfNat_isU64 _
  -- real JALR rows may either write an ordinary destination or discard the link at x0
  · by_cases hzero : e.opA = 0
    · exact Or.inr ⟨rfl, iTypeReaderCols_op_a_0_eq_one hzero⟩
    · exact Or.inl (iTypeReaderCols_op_a_0_eq_zero hzero)
  -- the uncleared jump target is a program counter: 48 bits, so its committed high limb is zero
  · rw [jumpTargetWord_toJalrInputs]
    exact wordOfNat_three_eq_zero htgt48
  -- so is the link address `pc + 4`
  · rw [linkTargetWord_toJalrInputs hpc]
    exact wordOfNat_three_eq_zero (by omega)
  -- and the **cleared** target is 4-byte aligned — the `Range((value[0] - lsb) / 4, 14)` byte pull
  · intro _
    rw [jumpTargetWord_toJalrInputs, lsbBit_toJalrInputs]
    exact wordOfNat_div_four_val_lt (p := p) (n := e.jalrTarget) (sub := e.jalrTarget % 2)
      (by omega) htgt4

/-- **A padding row satisfies the same contract.** `is_real = 0` makes every gated conjunct vacuous;
what survives is the three operand `isU64`s, the `op_a_0` zero flag, and — because they are stated
**ungated** — the two `value[3] = 0` gates, which the zero row's two sums `0 + 0` and `0 + 4`
satisfy. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (jalrPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  refine ⟨hzero, hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, Or.inl rfl,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne⟩ <;>
    simp [jumpTargetWord, linkTargetWord, rs1WordI, jalrPaddingInputs, zeroCPUStateCols,
      zeroITypeReaderCols, zeroAccessCols, AddOperation.populate]

/-! ## The built table -/

/-- The Jalr chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row per event, then `padding` zero rows. -/
def traceInputs (events : List ITypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ITypeEvent.toJalrInputs ++ List.replicate padding jalrPaddingInputs

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ITypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormedJalr ∧ e.JalrTargets) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Jalr table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedJalr ∧ e.JalrTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Constraints :=
  Air.Flat.Table.build_constraints _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedJalr ∧ e.JalrTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      hint).Guarantees :=
  Air.Flat.Table.build_guarantees _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data hint)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
        hint).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ channel

end SP1Clean.JalrChip
