import SP1Clean.FormalModel.TraceGen.Arith
import SP1Clean.Proofs.Chips.BranchChip.Witgen
import ToClean.Air.TableBuild

/-! # Branch event and table construction

Event opcodes supply the six committed selectors. Clean generates the comparison, branch
bit and next PC without per-row hints. `WellFormedBranch` permits reading `x0`; `BranchTargets`
bounds both candidate PCs and aligns the selected target.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The six variant selectors of a `Branch` row, in the chip's own column order (`is_beq`, `is_bne`,
`is_blt`, `is_bge`, `is_bltu`, `is_bgeu`), read off the executor's opcode discriminant
(`Opcode::{BEQ … BGEU} = 40 … 45` — the same numbers the chip's `branchOpcode` sends to the Program
bus). -/
def branchFlags (opcode : ℕ) : Vector (ZMod p) 6 :=
  #v[if opcode = 40 then 1 else 0, if opcode = 41 then 1 else 0, if opcode = 42 then 1 else 0,
     if opcode = 43 then 1 else 0, if opcode = 44 then 1 else 0, if opcode = 45 then 1 else 0]

/-- CPU state, immutable reads and selectors for one branch event. -/
def ITypeEvent.toBranchInputs (e : ITypeEvent) : BranchChip.Inputs (ZMod p) where
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e
  isBeq := (branchFlags e.opcode)[0]
  isBne := (branchFlags e.opcode)[1]
  isBlt := (branchFlags e.opcode)[2]
  isBge := (branchFlags e.opcode)[3]
  isBltu := (branchFlags e.opcode)[4]
  isBgeu := (branchFlags e.opcode)[5]

lemma ITypeEvent.toBranchInputs_state (e : ITypeEvent) :
    (e.toBranchInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma ITypeEvent.toBranchInputs_adapter (e : ITypeEvent) :
    (e.toBranchInputs (p := p)).adapter = iTypeReaderCols e := rfl

/-- Zero state, operands and selectors for padding. -/
def branchPaddingInputs : BranchChip.Inputs (ZMod p) where
  state := zeroCPUStateCols
  adapter := zeroITypeReaderCols
  isBeq := 0
  isBne := 0
  isBlt := 0
  isBge := 0
  isBltu := 0
  isBgeu := 0

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
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
/-- A branch event activates exactly one instruction selector. -/
lemma ITypeEvent.toBranchInputs_is_real {e : ITypeEvent} (hop : e.IsBranch) :
    (e.toBranchInputs (p := p)).is_real = 1 := (branchFlags_spec hop).2

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

/-- The comparison witness computes the executor's branch decision. -/
lemma populateBranching_toBranchInputs {e : ITypeEvent} (hop : e.IsBranch) :
    BranchChip.populateBranching (e.toBranchInputs (p := p)) =
      if e.branchTaken then (1 : ZMod p) else 0 := by
  have hrs1 : Word.isU64 (BranchChip.rs1WordInput (e.toBranchInputs (p := p))) := by
    rw [rs1WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  have hrs2 : Word.isU64 (BranchChip.rs2WordInput (e.toBranchInputs (p := p))) := by
    rw [rs2WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  have hf : ∀ i : Fin 6, (e.toBranchInputs (p := p)).flags[i] = 0 ∨
      (e.toBranchInputs (p := p)).flags[i] = 1 := by
    intro i
    exact (branchFlags_spec (p := p) hop).1 i i.isLt
  have hreal := e.toBranchInputs_is_real (p := p) hop
  have hbinary := BranchChip.populateBranching_binary e.toBranchInputs hrs1 hrs2 hf (Or.inr hreal)
  have hconditions := BranchChip.populateBranching_conditions e.toBranchInputs hrs1 hrs2 hf hreal
  rw [rs1BV_toBranchInputs, rs2BV_toBranchInputs] at hconditions
  have hdecision : BranchChip.populateBranching (e.toBranchInputs (p := p)) = 1 ↔
      e.branchTaken = true := by
    obtain hq | hq | hq | hq | hq | hq := hop
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.1 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.2.1 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.2.2.1 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.2.2.2.1 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.2.2.2.2.1 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
    · simpa [ITypeEvent.branchTaken, hq] using hconditions.2.2.2.2.2 (by simp [ITypeEvent.toBranchInputs, branchFlags, hq])
  cases hb : e.branchTaken with
  | false =>
    rcases hbinary with h0 | h1
    · exact h0
    · have hf := hdecision.mp h1
      simp [hb] at hf
  | true => exact hdecision.mpr hb

/-- Selecting the event's branch bit yields the executor's next PC. -/
lemma committedNextPc_toBranchInputs {e : ITypeEvent} (hop : e.IsBranch)
    (h : e.pc < 2 ^ 48) :
    BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0)
      = #v[(wordOfNat (p := p) e.branchNextPc)[0], (wordOfNat (p := p) e.branchNextPc)[1],
           (wordOfNat (p := p) e.branchNextPc)[2]] := by
  rw [BranchChip.committedNextPc, e.toBranchInputs_is_real hop, branchTargetWord_toBranchInputs h,
    fallThroughWord_toBranchInputs h, ITypeEvent.branchNextPc]
  cases hb : e.branchTaken <;>
    · refine Vector.ext (fun i hi => ?_)
      interval_cases i <;> simp

/-- **The committed `next_pc` is a legal program counter**: its low limb passes the chip's
`Range(next_pc[0] / 4, 14)` alignment pull and its two upper limbs are u16s. The alignment is the
event's own — the address the executor continued at is 4-byte aligned — and the limb bounds are
properties of the builder. -/
lemma committedNextPc_bounds {e : ITypeEvent} (hop : e.IsBranch) (hpc : e.pc < 2 ^ 48)
    (halign : e.branchNextPc % 4 = 0) :
    ((BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
      (BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[1].val < 2 ^ 16 ∧
      (BranchChip.committedNextPc (e.toBranchInputs (p := p))
        (if e.branchTaken then (1 : ZMod p) else 0))[2].val < 2 ^ 16 := by
  simp only [committedNextPc_toBranchInputs hop hpc, Vector.getElem_mk, List.getElem_toArray,
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

/-- A well-formed branch event satisfies the prover contract for arbitrary hints. -/
theorem proverAssumptions_of_event {e : ITypeEvent} (h : e.WellFormedBranch) (hop : e.IsBranch)
    (htgt : e.BranchTargets) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toBranchInputs (p := p)) data hint := by
  obtain ⟨htgt48, _hlink, halign⟩ := htgt
  obtain ⟨hbin, _hsum⟩ := branchFlags_spec (p := p) hop
  have hpc : e.pc < 2 ^ 48 := h.pc_lt
  simp only [ProverAssumptions, e.toBranchInputs_is_real hop]
  refine ⟨wordOfNat_isU64 _, ?_, ?_, cpuStateCols_pcWord_isU64 e.clk e.pc, Or.inr trivial,
    cpuState_spec e.clk e.pc h.clk_mod _ _ _,
    iTypeReaderImmutable_spec h.clk_mod h.opA_lt h.prevA_x0 h.prevTsA_lt h.prevTsB_lt _ _ _ _,
    ?_, ?_, ?_, ?_⟩
  · rw [rs1WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  · rw [rs2WordInput_toBranchInputs]
    exact wordOfNat_isU64 _
  · rw [branchTargetWord_toBranchInputs hpc]
    exact wordOfNat_three_eq_zero htgt48
  · rw [fallThroughWord_toBranchInputs hpc]
    exact wordOfNat_three_eq_zero (by omega)
  · intro i
    exact hbin i i.isLt
  · intro _
    rw [populateBranching_toBranchInputs hop]
    exact committedNextPc_bounds hop hpc halign

/-- Zero selectors make every activity-gated padding obligation vacuous.
The two ungated high limbs vanish for `0 + 0` and `0 + 4`. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (branchPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hreal : (branchPaddingInputs (p := p)).is_real = 0 := by simp [branchPaddingInputs]
  simp only [ProverAssumptions, hreal]
  refine ⟨hzero, hzero, hzero, hzero, Or.inl trivial, fun hr => absurd hr hne, ?_, ?_, ?_,
    ?_, fun hr => absurd hr hne⟩
  · exact ⟨⟨zero_mul _, zero_mul _, zero_mul _, zero_mul _⟩, fun hr => absurd hr hne,
      fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
      fun hr => absurd hr hne⟩
  · simp [branchTargetWord, branchPaddingInputs, zeroCPUStateCols, zeroITypeReaderCols,
      AddOperation.populate]
  · simp [fallThroughWord, branchPaddingInputs, zeroCPUStateCols, AddOperation.populate]
  · intro i
    left
    fin_cases i <;> rfl

/-! ## The built table -/

/-- The Branch chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Real event inputs followed by zero padding inputs. -/
def traceInputs (events : List ITypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map ITypeEvent.toBranchInputs ++ List.replicate padding branchPaddingInputs

/-- Each event or padding row satisfies the prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ITypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2.1 (h e he).2.2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- Clean's ordinary table builder satisfies every constraint. -/
theorem traceTable_constraints (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      (ProverHint.empty _)).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The built table satisfies its channel guarantees. -/
theorem traceTable_guarantees (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormedBranch ∧ e.IsBranch ∧ e.BranchTargets) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding) data
      (ProverHint.empty _)).Guarantees data :=
  Air.Flat.Table.build_guarantees _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The table interaction list, preserving row order and multiplicities. -/
theorem traceTable_interactionsWith (events : List ITypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
        data (ProverHint.empty _)).interactionsWith data channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data (ProverHint.empty _)) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ _ data channel

end SP1Clean.BranchChip
