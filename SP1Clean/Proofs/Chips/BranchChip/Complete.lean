import SP1Clean.FormalModel.TraceGen.Arith
import SP1Clean.Proofs.Chips.BranchChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.BranchChip` — from trace events to a valid AIR table

The six conditional branches (`BEQ`/`BNE`/`BLT`/`BGE`/`BLTU`/`BGEU`) through the trace-generation
chain (see `AddChip/Complete.lean` for the programme note, and `BitwiseChip/Complete.lean` for why
a hint-flag chip's hint has to be built per row).

Branch is the chip that needs the per-row hint for **two** reasons, not one. The six variant
selectors are the familiar case: `is_real = Σ is_b*`, so a table-level hint could not carry a
padding row and a real row at once. The second is `is_branching` — the row's taken/not-taken
decision, which is per-row *data*, not a per-table constant, and which the chip's
`ProverAssumptions` pins against the operand comparison the row's own opcode names:

    f[2] = 1 → (br = 1 ↔ (rs1).slt (rs2) = true)          -- and five siblings

`ITypeEvent.branchTaken` is that bridge on the event side: the RV64 comparison of the event's two
operand values, selected by its opcode discriminant. `ITypeEvent.toBranchHint` puts it in the
`"branch_branching"` key beside the flags, so the row the builder produces decides the way the
executor decided.

## Two new event predicates, and why each

* `ITypeEvent.WellFormedBranch` — **not** `ITypeEvent.WellFormed`. That record's `opA_ne_zero` is
  the write families' routing condition; a branch's `op_a` is the `rs1` **source read**, and
  `beq x0, x1, L` is legal and common, so reusing it would silently exclude every branch comparing
  against zero — the `MemoryEvent.WellFormedStore` finding, repeated. What it states instead is
  that `x0` reads as zero, which is what the immutable adapter's four `op_a_0 · prev_value_i = 0`
  gates need. (Details in `TraceGen/Events.lean`.)
* `ITypeEvent.BranchTargets` — the two candidate addresses. Both carry chains run on every real
  row, so both owe `< 2 ^ 48`; only the **selected** one is alignment-range-checked, so that
  conjunct is gated on the decision rather than demanded of both.

Everything else is cited: the `CPUState` block, the whole immutable I-type adapter contract
(`iTypeReaderImmutable_spec`, the store family's lemma, unchanged), and the `AddOperation` witness
identity `populate_pcWord`. Padding is satisfiable: the empty hint reads six zero flags and
`is_branching = 0`, and the two ungated `value[3] = 0` conjuncts hold on a zero row because its two
sums are `0 + 0` and `0 + 4`. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The six variant selectors of a `Branch` row, in the chip's own column order (`is_beq`, `is_bne`,
`is_blt`, `is_bge`, `is_bltu`, `is_bgeu`), read off the executor's opcode discriminant
(`Opcode::{BEQ … BGEU} = 40 … 45` — the same numbers the chip's `branchOpcode` sends to the Program
bus). -/
def branchFlags (opcode : ℕ) : Vector (ZMod p) 6 :=
  #v[if opcode = 40 then 1 else 0, if opcode = 41 then 1 else 0, if opcode = 42 then 1 else 0,
     if opcode = 43 then 1 else 0, if opcode = 44 then 1 else 0, if opcode = 45 then 1 else 0]

/-- The `Branch` chip's committed input row for one event — a **real** row (`is_real = 1`). The six
flags, the decision, the compare block and the three `next_pc` limbs are all *witnessed* columns,
not inputs; only the state and adapter blocks are built here. -/
def ITypeEvent.toBranchInputs (e : ITypeEvent) : BranchChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e

lemma ITypeEvent.toBranchInputs_state (e : ITypeEvent) :
    (e.toBranchInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma ITypeEvent.toBranchInputs_adapter (e : ITypeEvent) :
    (e.toBranchInputs (p := p)).adapter = iTypeReaderCols e := rfl

/-- **The row's prover hint.** Two keys: `"branch_flags"` carries the variant selectors of *this
event's* opcode, and `"branch_branching"` carries *this event's* taken/not-taken decision. Both are
per-row data in SP1's Rust trace, and both are pinned by the chip's `ProverAssumptions` against the
row's own columns — the flags against `is_real`, the decision against the operand comparison. -/
def ITypeEvent.toBranchHint (e : ITypeEvent) : ProverHint (ZMod p) :=
  hintAdd "branch_branching" #v[if e.branchTaken then (1 : ZMod p) else 0]
    (flagHint "branch_flags" (branchFlags e.opcode))

/-- The `Branch` chip's padding row: every column zero, `is_real = 0`. Its hint is the empty one,
so all six flags and the decision read back as `0`. -/
def branchPaddingInputs : BranchChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroITypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the flags the builder put in (the `"branch_branching"` key of the
hint falls through to the flag table). -/
lemma hintFlags_toBranchHint (e : ITypeEvent) :
    BranchChip.hintFlags (e.toBranchHint (p := p)) = branchFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 6) = #v[0, 0, 0, 0, 0, 0] := rfl
  rw [BranchChip.hintFlags, ← hdefault, ITypeEvent.toBranchHint, hintAdd, if_neg (by decide)]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the decision the builder put in. -/
lemma hintBranching_toBranchHint (e : ITypeEvent) :
    BranchChip.hintBranching (e.toBranchHint (p := p))
      = if e.branchTaken then (1 : ZMod p) else 0 := by
  have hdefault : (default : Vector (ZMod p) 1) = #v[0] := rfl
  rw [BranchChip.hintBranching, ← hdefault, ITypeEvent.toBranchHint,
    hintAdd_apply "branch_branching" _ _]
  rfl

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as all-zero flags. -/
lemma branchHintFlags_empty :
    BranchChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 0, 0, 0, 0, 0] := rfl

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as a `0` decision — a padding row branches nowhere. -/
lemma branchHintBranching_empty :
    BranchChip.hintBranching (ProverHint.empty (ZMod p)) = 0 := rfl

/-- **The flags of a real `Branch` row are one-hot, and their sum is `1`.** -/
lemma branchFlags_spec {e : ITypeEvent} (hop : e.IsBranch) :
    (∀ i (hi : i < 6), (branchFlags (p := p) e.opcode)[i] = 0
        ∨ (branchFlags (p := p) e.opcode)[i] = 1) ∧
      (branchFlags (p := p) e.opcode)[0] + (branchFlags (p := p) e.opcode)[1]
        + (branchFlags (p := p) e.opcode)[2] + (branchFlags (p := p) e.opcode)[3]
        + (branchFlags (p := p) e.opcode)[4] + (branchFlags (p := p) e.opcode)[5] = 1 := by
  obtain h | h | h | h | h | h := hop <;>
    exact ⟨fun i hi => by interval_cases i <;> simp [branchFlags, h], by simp [branchFlags, h]⟩

omit [Fact (2 ^ 24 < p)] in
/-- The `is_branching` cell a built row carries is `1` exactly when the row's decision is taken. -/
lemma branchBit_eq_one_iff (b : Bool) : ((if b then (1 : ZMod p) else 0) = 1) ↔ b = true := by
  cases b
  · simp
  · simp

/-! ## The witnessed words of a built row -/

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The `rs1` operand of a built row is the built word of the `op_a` source read. -/
lemma rs1WordInput_toBranchInputs (e : ITypeEvent) :
    BranchChip.rs1WordInput (e.toBranchInputs (p := p)) = wordOfNat e.prevA := by
  rw [BranchChip.rs1WordInput]
  simp only [ITypeEvent.toBranchInputs_adapter, iTypeReaderCols_op_a_memory,
    registerAccessCols_prev_value]
  exact word_eta _

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The `rs2` operand of a built row is the built word of the `op_b` source read. -/
lemma rs2WordInput_toBranchInputs (e : ITypeEvent) :
    BranchChip.rs2WordInput (e.toBranchInputs (p := p)) = wordOfNat e.b := by
  rw [BranchChip.rs2WordInput]
  simp only [ITypeEvent.toBranchInputs_adapter, iTypeReaderCols_op_b_memory,
    registerAccessCols_prev_value]
  exact word_eta _

/-- The two operand words of a built row mean the event's two register values. -/
lemma rs1BV_toBranchInputs (e : ITypeEvent) :
    Word.toBitVec64 (BranchChip.rs1WordInput (e.toBranchInputs (p := p))) = e.rs1BV := by
  rw [rs1WordInput_toBranchInputs, toBitVec64_wordOfNat, ITypeEvent.rs1BV]

lemma rs2BV_toBranchInputs (e : ITypeEvent) :
    Word.toBitVec64 (BranchChip.rs2WordInput (e.toBranchInputs (p := p))) = e.rs2BV := by
  rw [rs2WordInput_toBranchInputs, toBitVec64_wordOfNat, ITypeEvent.rs2BV]

/-- The taken-side carry chain of a built row computes the built word of the executor's own
wrapping `pc + imm`. -/
lemma branchTargetWord_toBranchInputs {e : ITypeEvent} (h : e.pc < 2 ^ 48) :
    BranchChip.branchTargetWord (e.toBranchInputs (p := p)) = wordOfNat e.branchTarget := by
  rw [BranchChip.branchTargetWord]
  simp only [ITypeEvent.toBranchInputs_state, ITypeEvent.toBranchInputs_adapter,
    iTypeReaderCols_op_c_imm]
  rw [populate_pcWord h, ITypeEvent.branchTarget]

/-- The fall-through carry chain of a built row computes the built word of `pc + 4`. -/
lemma fallThroughWord_toBranchInputs {e : ITypeEvent} (h : e.pc < 2 ^ 48) :
    BranchChip.fallThroughWord (e.toBranchInputs (p := p)) = wordOfNat ((e.pc + 4) % 2 ^ 64) := by
  rw [BranchChip.fallThroughWord]
  simp only [ITypeEvent.toBranchInputs_state]
  rw [wordOfNat_four, populate_pcWord h]

/-- **The committed `next_pc` of a built row is the built word of the address the row continues
at** — the decision the hint carries selects the same candidate the executor did. -/
lemma committedNextPc_toBranchInputs {e : ITypeEvent} (h : e.pc < 2 ^ 48) :
    BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0)
      = #v[(wordOfNat (p := p) e.branchNextPc)[0], (wordOfNat (p := p) e.branchNextPc)[1],
           (wordOfNat (p := p) e.branchNextPc)[2]] := by
  rw [BranchChip.committedNextPc, branchTargetWord_toBranchInputs h,
    fallThroughWord_toBranchInputs h, ITypeEvent.branchNextPc]
  cases hb : e.branchTaken <;>
    · refine Vector.ext (fun i hi => ?_)
      interval_cases i <;> simp [ITypeEvent.toBranchInputs]

/-- **The committed `next_pc` is a legal program counter**: its low limb passes the chip's
`Range(next_pc[0] / 4, 14)` alignment pull and its two upper limbs are u16s. The alignment is the
event's own — the address the executor continued at is 4-byte aligned — and the limb bounds are
properties of the builder. -/
lemma committedNextPc_bounds {e : ITypeEvent} (hpc : e.pc < 2 ^ 48)
    (halign : e.branchNextPc % 4 = 0) :
    ((BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
      (BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[1].val < 2 ^ 16 ∧
      (BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[2].val < 2 ^ 16 := by
  simp only [committedNextPc_toBranchInputs hpc, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  obtain ⟨-, hl1, hl2, -⟩ := Word.lt_cases_of_isU64 (wordOfNat_isU64 (p := p) e.branchNextPc)
  refine ⟨?_, hl1, hl2⟩
  have hb := wordOfNat_div_four_val_lt (p := p) (n := e.branchNextPc) (sub := 0)
    (Nat.zero_le _) (by simpa using halign)
  simpa using hb

end SP1Clean.TraceGen

namespace SP1Clean.BranchChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed branch trace event with legal targets builds a row the honest prover can complete,
at the hint the same event builds.** Every conjunct of `BranchChip.ProverAssumptions` follows from
`ITypeEvent.WellFormedBranch`, the routing condition `hop : e.IsBranch`, and `htgt : e.BranchTargets`.

The `data` is arbitrary; the **hint is not** — it is `e.toBranchHint`, carrying this event's own
opcode selectors and its own taken/not-taken decision.
-/
theorem proverAssumptions_of_event {e : ITypeEvent} (h : e.WellFormedBranch) (hop : e.IsBranch)
    (htgt : e.BranchTargets) (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toBranchInputs (p := p)) data e.toBranchHint := by
  obtain ⟨htgt48, hlink, halign⟩ := htgt
  obtain ⟨hbin, hsum⟩ := branchFlags_spec (p := p) hop
  have hne : ((0 : ZMod p)) ≠ 1 := zero_ne_one
  have hpc : e.pc < 2 ^ 48 := h.pc_lt
  simp only [ProverAssumptions, hintFlags_toBranchHint, hintBranching_toBranchHint]
  refine ⟨wordOfNat_isU64 _, ?_, ?_, cpuStateCols_pcWord_isU64 e.clk e.pc, Or.inr rfl,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    ?_, ?_, hbin 0 (by omega), hbin 1 (by omega), hbin 2 (by omega), hbin 3 (by omega),
    hbin 4 (by omega), hbin 5 (by omega), hsum.symm, ?_, fun hr => absurd hr.symm hne, ?_, ?_⟩
  -- the two operand words are the two register reads
  · rw [rs1WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  · rw [rs2WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  -- both candidate addresses are program counters: 48 bits, so their committed high limbs vanish
  · rw [branchTargetWord_toBranchInputs hpc]
    exact wordOfNat_three_eq_zero htgt48
  · rw [fallThroughWord_toBranchInputs hpc]
    exact wordOfNat_three_eq_zero (by omega)
  -- the decision cell is binary
  · cases hb : e.branchTaken
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- **the decision bridge**: the cell is `1` exactly when the comparison the row's opcode names
  -- holds of the row's two operands
  · intro _
    rw [rs1BV_toBranchInputs, rs2BV_toBranchInputs]
    obtain hq | hq | hq | hq | hq | hq := hop <;>
      refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_,
        fun hf => ?_⟩ <;>
      simp only [branchFlags, hq, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, if_true] at hf ⊢ <;>
      first
        | exact absurd hf hne
        | · rw [branchBit_eq_one_iff, ITypeEvent.branchTaken]
            simp [hq]
  -- the alignment and limb ranges of the committed `next_pc`, on whichever candidate was selected
  · exact fun _ => committedNextPc_bounds hpc halign

/-- **A padding row satisfies the same contract**, at the empty hint: six zero flags, a `0`
decision, and every `is_real`-gated conjunct vacuous. The two `value[3] = 0` conjuncts are stated
**ungated** and hold because a zero row's two carry chains compute `0 + 0` and `0 + 4`. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (branchPaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  refine ⟨hzero, ?_, ?_, hzero, Or.inl rfl, fun hr => absurd hr hne, ?_, ?_, ?_,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_,
    Or.inl rfl, fun _ => rfl, fun hr => absurd hr hne, fun hr => absurd hr hne⟩
  -- the two operand words of a zero row
  · exact hzero
  · exact hzero
  -- the immutable adapter's contract: the four zeroing gates are `0 * 0`, everything else is gated
  · exact ⟨⟨zero_mul _, zero_mul _, zero_mul _, zero_mul _⟩, fun hr => absurd hr hne,
      fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
      fun hr => absurd hr hne⟩
  -- the two ungated `value[3] = 0` gates: the zero row's two sums are `0 + 0` and `0 + 4`
  · simp [branchTargetWord, branchPaddingInputs, zeroCPUStateCols, zeroITypeReaderCols,
      AddOperation.populate]
  · simp [fallThroughWord, branchPaddingInputs, zeroCPUStateCols, AddOperation.populate]
  -- the selector sum of a padding row is `0`
  · simp [branchPaddingInputs, branchHintFlags_empty]

/-! ## The built table -/

/-- The Branch chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
zero rows at the empty hint. -/
def traceInputs (events : List ITypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toBranchInputs, e.toBranchHint))
    ++ List.replicate padding (branchPaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ITypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets)
    (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2.1 (h e he).2.2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid Branch table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Guarantees :=
  Air.Flat.Table.buildHinted_guarantees _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
        data).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input.1 data input.2) data) :=
  Air.Flat.Table.buildHinted_interactions _ _ _ channel

end SP1Clean.BranchChip
