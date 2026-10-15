import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.MulChip.Witgen
import ToClean.Air.TableBuild

/-! # Mul trace construction

Each event supplies its five opcode selectors as circuit inputs. Their sum is the row's
activity, matching SP1's physical layout. `mulFlags_opcode_eq` identifies the instruction,
and `mulFlags_spec` proves the selector contract for all five multiply variants.

Padding supplies zero operands and selectors. Both real and padding rows use the ordinary
table builder; witness generation needs no external hints. Events writing `x0` route to AluX0.
-/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The five variant selectors of a `Mul` row, in the chip's own column order (`isMul`,
`isMulh`, `isMulhu`, `isMulhsu`, `isMulw`), read off the executor's opcode discriminant
(`Opcode::{MUL, MULH, MULHU, MULHSU, MULW} = 11, 12, 13, 14, 24`). The same numbers appear in the
chip's `cpu_opcode` expression `isMul·11 + isMulh·12 + isMulhu·13 + isMulhsu·14 + isMulw·24`,
which is what the Program-bus fetch checks them against. -/
def mulFlags (opcode : ℕ) : Vector (ZMod p) 5 :=
  #v[if opcode = 11 then 1 else 0, if opcode = 12 then 1 else 0, if opcode = 13 then 1 else 0,
     if opcode = 14 then 1 else 0, if opcode = 24 then 1 else 0]

/-- A real Mul row, with selectors determined by the event's opcode. -/
def RTypeEvent.toMulInputs (e : RTypeEvent) : MulChip.Inputs (ZMod p) where
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e
  isMul := (mulFlags e.opcode)[0]
  isMulh := (mulFlags e.opcode)[1]
  isMulhu := (mulFlags e.opcode)[2]
  isMulhsu := (mulFlags e.opcode)[3]
  isMulw := (mulFlags e.opcode)[4]

/-- SP1's all-zero inactive Mul input. -/
def mulPaddingInputs : MulChip.Inputs (ZMod p) where
  state := zeroCPUStateCols
  adapter := zeroRTypeReaderCols
  isMul := 0
  isMulh := 0
  isMulhu := 0
  isMulhsu := 0
  isMulw := 0

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Weighting the supplied selectors by the reader's opcode coefficients recovers the event's
opcode, so the Program-bus fetch authenticates the chosen multiply variant. -/
lemma mulFlags_opcode_eq {e : RTypeEvent} (hop : e.IsMul) :
    (mulFlags (p := p) e.opcode)[0] * 11 + (mulFlags (p := p) e.opcode)[1] * 12
        + (mulFlags (p := p) e.opcode)[2] * 13 + (mulFlags (p := p) e.opcode)[3] * 14
        + (mulFlags (p := p) e.opcode)[4] * 24 = ((e.opcode : ℕ) : ZMod p) := by
  obtain h | h | h | h | h := hop <;> rw [h] <;> norm_num [mulFlags]

omit [Fact (2 ^ 24 < p)] in
/-- A routed Mul event selects exactly one of the five variants. -/
lemma mulFlags_spec {e : RTypeEvent} (hop : e.IsMul) :
    ((mulFlags (p := p) e.opcode)[0] = 0 ∨ (mulFlags (p := p) e.opcode)[0] = 1) ∧
    ((mulFlags (p := p) e.opcode)[1] = 0 ∨ (mulFlags (p := p) e.opcode)[1] = 1) ∧
    ((mulFlags (p := p) e.opcode)[2] = 0 ∨ (mulFlags (p := p) e.opcode)[2] = 1) ∧
    ((mulFlags (p := p) e.opcode)[3] = 0 ∨ (mulFlags (p := p) e.opcode)[3] = 1) ∧
    ((mulFlags (p := p) e.opcode)[4] = 0 ∨ (mulFlags (p := p) e.opcode)[4] = 1) ∧
    (mulFlags (p := p) e.opcode)[0] + (mulFlags (p := p) e.opcode)[1]
      + (mulFlags (p := p) e.opcode)[2] + (mulFlags (p := p) e.opcode)[3]
      + (mulFlags (p := p) e.opcode)[4] = 1 := by
  obtain h | h | h | h | h := hop <;> simp [mulFlags, h]

end SP1Clean.TraceGen

namespace SP1Clean.MulChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- A routed, well-formed event satisfies the prover contract for arbitrary data and hints. -/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed) (hop : e.IsMul)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (e.toMulInputs (p := p)) data hint := by
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hsum⟩ := mulFlags_spec (p := p) hop
  have hreal : (e.toMulInputs (p := p)).is_real = 1 := hsum
  simp only [ProverAssumptions, hreal]
  refine ⟨?_, ?_, ?_, Or.inr trivial, hf0, hf1, hf2, hf3, hf4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wordOfNat_isU64 _
  · exact wordOfNat_isU64 _
  · exact fun _ => wordOfNat_isU64 _
  · exact rTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  · exact registerAccessCols_spec_opC h.clk_mod h.prevTsC_lt
  · exact fun _ => ⟨rTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, registerAccessCols_prevLow_val_lt _ _ _⟩

/-- The zero input satisfies the contract, including its ungated operand bounds. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ProverAssumptions (mulPaddingInputs (p := p)) data hint := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  have hreal : (mulPaddingInputs (p := p)).is_real = 0 := by simp [mulPaddingInputs]
  simp only [ProverAssumptions, hreal]
  exact ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl trivial, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    Or.inl rfl, Or.inl rfl, rfl, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne⟩

/-! ## The built table -/

/-- The Mul chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := { circuit := circuit }

/-- Real event inputs followed by all-zero padding inputs. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) : List (Inputs (ZMod p)) :=
  events.map RTypeEvent.toMulInputs ++ List.replicate padding mulPaddingInputs

/-- Every event or padding input satisfies the chip's prover contract. -/
theorem proverAssumptions_of_mem_traceInputs {events : List RTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input data hint := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data hint
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data hint

/-- **A real trace builds a valid Mul table.** Every `assertZero` of the whole flattened chip
circuit — the 45-cell schoolbook multiplication block, the flag gates, the result-placement
selector, the reader glue — evaluates to zero on every built row, and no static lookup is left
unchecked. -/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
      data (ProverHint.empty _)).Constraints data :=
  Air.Flat.Table.build_constraints _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
      data (ProverHint.empty _)).Guarantees data :=
  Air.Flat.Table.build_guarantees _ _ _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data (ProverHint.empty _))

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.build (component (p := p)) (traceInputs events padding)
        data (ProverHint.empty _)).interactionsWith data channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data (ProverHint.empty _)) data) :=
  Air.Flat.Table.build_interactions _ _ _ _ _ data channel

end SP1Clean.MulChip
