import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.LtChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.LtChip` — from trace events to a valid AIR table

`SLT`/`SLTU` through the trace-generation chain. Structurally the `Bitwise` file with two variant
flags instead of three: SP1's `Lt` chip has no `is_real` column either — its real-row selector is
`is_slt + is_sltu` — the flags are witnessed from the `"lt_flags"` hint key, and the row's hint is
therefore built per row from **this event's own opcode discriminant**
(`Opcode::{SLT, SLTU} = 9, 10`, the same numbers the chip threads into its reader as
`is_slt·9 + is_sltu·10`). See `BitwiseChip/Complete.lean` for why the hint must be per row, and
`AddwChip/Complete.lean` for the ALU-type adapter half, which this chip reuses verbatim.

`ALUTypeEvent.IsLt` is the chip's **routing** condition, and — as for `Bitwise` — padding is
satisfiable: the empty hint reads both flags as `0`, matching `is_real = 0`.

One conjunct is `Lt`'s own and has no `Bitwise` counterpart: `f[0] = 1 → is_real = 1`, which the
soundness proof uses to force `is_slt = 0` on the `SLTU` branch. On a built real row it is
`fun _ => rfl`, and on a padding row it is vacuous. Everything else is `Addw`'s, cited unchanged. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The two variant selectors of an `Lt` row, in the chip's own column order (`is_slt`, `is_sltu`),
read off the executor's opcode discriminant (`Opcode::{SLT, SLTU} = 9, 10`). -/
def ltFlags (opcode : ℕ) : Vector (ZMod p) 2 :=
  #v[if opcode = 9 then 1 else 0, if opcode = 10 then 1 else 0]

/-- The `Lt` chip's committed input row for one event — a **real** row (`is_real = 1`). The two
variant flags are witnessed from the hint, not committed here. -/
def ALUTypeEvent.toLtInputs (e : ALUTypeEvent) : LtChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e

lemma ALUTypeEvent.toLtInputs_adapter (e : ALUTypeEvent) :
    (e.toLtInputs (p := p)).adapter = aluTypeReaderCols e := rfl

/-- **The row's prover hint**: the `"lt_flags"` key carries the variant selectors of *this event's*
opcode, so the row the builder produces is the row the executor's instruction produces. -/
def ALUTypeEvent.toLtHint (e : ALUTypeEvent) : ProverHint (ZMod p) :=
  flagHint "lt_flags" (ltFlags e.opcode)

/-- The `Lt` chip's padding row: every column zero, `is_real = 0` (and `imm_c = 0`, the register-row
form the chip's `ProverAssumptions` asks for). Its hint is the empty one, so both flags read back as
`0`. -/
def ltPaddingInputs : LtChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the flags the builder put in. -/
lemma hintFlags_toLtHint (e : ALUTypeEvent) :
    LtChip.hintFlags (e.toLtHint (p := p)) = ltFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 2) = #v[0, 0] := rfl
  rw [LtChip.hintFlags, ← hdefault, ALUTypeEvent.toLtHint]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as all-zero flags — SP1's own padding convention. -/
lemma ltHintFlags_empty : LtChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 0] := rfl

/-- **The flags of a real `Lt` row are one-hot, and their sum is `1`** — everything the chip's
`ProverAssumptions` says about the hint, from the routing condition alone. -/
lemma ltFlags_spec {e : ALUTypeEvent} (hop : e.IsLt) :
    ((ltFlags (p := p) e.opcode)[0] = 0 ∨ (ltFlags (p := p) e.opcode)[0] = 1) ∧
    ((ltFlags (p := p) e.opcode)[1] = 0 ∨ (ltFlags (p := p) e.opcode)[1] = 1) ∧
    (ltFlags (p := p) e.opcode)[0] + (ltFlags (p := p) e.opcode)[1] = 1 := by
  obtain h | h := hop <;> simp [ltFlags, h]

end SP1Clean.TraceGen

namespace SP1Clean.LtChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed register-row `Lt` trace event builds a row the honest prover can complete, at the
hint the same event builds.** Every conjunct of `LtChip.ProverAssumptions` follows from
`ALUTypeEvent.WellFormed`, the routing condition `hop : e.IsLt`, and `himm : e.immC = 0`.

The `data` is arbitrary; the **hint is not** — it is `e.toLtHint`, the flags of this event's own
opcode.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed) (hop : e.IsLt)
    (himm : e.immC = 0) (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toLtInputs (p := p)) data e.toLtHint := by
  obtain ⟨hf0, hf1, hsum⟩ := ltFlags_spec (p := p) hop
  simp only [ProverAssumptions, hintFlags_toLtHint]
  refine ⟨?_, ?_, ?_, ?_, ?_, hf0, hf1, hsum.symm, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces, and the `op_c` read at the reader's own gate
  · exact fun _ => wordOfNat_isU64 _
  · exact fun _ => aluTypeOpCCols_prev_value_isU64 e
  -- the row is real
  · exact Or.inr rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the register-register form: the committed `imm_c` flag is the event's, hence `0`
  · rw [ALUTypeEvent.toLtInputs_adapter, aluTypeReaderCols_imm_c, himm, Nat.cast_zero]
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: on a register row the block is the ordinary `rs2` read block
  · rw [ALUTypeEvent.toLtInputs_adapter, aluTypeReaderCols_op_c_memory, aluTypeOpCCols_of_reg himm]
    exact registerAccessCols_spec_opC h.clk_mod (h.prevTsC_reg himm)
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, aluTypeOpCCols_prevLow_val_lt e⟩

/-- **A padding row satisfies the same contract**, at the empty hint: both flags read back as `0`,
so the selector-sum conjunct is `0 = 0 + 0`, and every `is_real`-gated conjunct is vacuous. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (ltPaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  simp only [ProverAssumptions, ltHintFlags_empty]
  refine ⟨hzero, hzero, fun hr => absurd hr hne, ?_, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    by simp [ltPaddingInputs], fun hr => absurd hr hne, rfl, rfl, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, ?_, fun hr => absurd hr hne,
    fun hr => absurd hr hne⟩ <;>
    · intro hr
      have h0 : (0 : ZMod p) = 1 := by rw [← sub_zero (0 : ZMod p)]; exact hr
      exact absurd h0 hne

/-! ## The built table -/

/-- The Lt chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
zero rows at the empty hint. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toLtInputs, e.toLtHint))
    ++ List.replicate padding (ltPaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint, provided every event is a register-register set-less-than. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsLt ∧ e.immC = 0) (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2.1 (h e he).2.2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid Lt table.** Every `assertZero` of the whole flattened chip circuit
evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsLt ∧ e.immC = 0) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsLt ∧ e.immC = 0) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Guarantees :=
  Air.Flat.Table.buildHinted_guarantees _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
        data).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input.1 data input.2) data) :=
  Air.Flat.Table.buildHinted_interactions _ _ _ channel

end SP1Clean.LtChip
