import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.BitwiseChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.BitwiseChip` — from trace events to a valid AIR table (the hint-flag template)

`XOR`/`OR`/`AND` through the trace-generation chain (see `AddChip/Complete.lean` for the programme
note, and `AddwChip/Complete.lean` for the ALU-type adapter half, which this chip reuses verbatim).

**The first chip whose row carries a `ProverHint`.** SP1's `Bitwise` chip has no `is_real` column:
its real-row selector *is* the sum of the three variant flags (`alu/bitwise/mod.rs`), and the native
circuit witnesses those flags from the `"bitwise_flags"` hint key rather than committing them as
`Inputs` columns. The chip's `ProverAssumptions` therefore pins the hint against the row's own
selector — `is_real = f[0] + f[1] + f[2]` — which a *table-level* hint cannot satisfy: one hint for
the whole table would need `0 = 1` on every padding row, and would force every real row to be the
same variant. `Air.Flat.Table.buildHinted` takes the hint **per row**, and this file is its first
user: `ALUTypeEvent.toBitwiseHint` reads the flags off *this event's own opcode discriminant*, so
the row the builder produces is the row the executor's instruction produces, not an arbitrary
one-hot triple.

That is also where the new event predicate comes from. `is_real = 1` and "exactly one flag is set"
are the same fact, so a real `Bitwise` row exists only for an event whose opcode is one of the
three the chip serves: `ALUTypeEvent.IsBitwise` (`Opcode::{XOR, OR, AND} = 3, 4, 5`) is that
**routing** condition, the ALU-side sibling of `MemoryEvent.IsLoad`.

**Padding is satisfiable.** Unlike the table-level-hint form, a zero row paired with the empty hint
reads all three flags as `0`, and `0 = 0 + 0 + 0` holds — so this chip gets a genuine
`proverAssumptions_padding`, exactly like the single-variant chips.

**The register-row hypothesis.** As for `Addw`, the chip's `ProverAssumptions` asks for `imm_c = 0`:
this theorem is the completeness witness for the register-register forms. Honest `ANDI`/`ORI`/`XORI`
rows carry `imm_c = 1` and are covered by soundness and by the bridge, not here.

Beyond the seven flag conjuncts — all discharged by the one `bitwiseFlags_spec` case split — every
bullet is `Addw`'s, cited unchanged. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The three variant selectors of a `Bitwise` row, in the chip's own column order (`is_xor`,
`is_or`, `is_and`), read off the executor's opcode discriminant (`Opcode::{XOR, OR, AND} = 3, 4,
5`). The same numbers appear in the chip's `cpu_opcode` expression `is_xor·3 + is_or·4 + is_and·5`,
which is what the Program-bus fetch checks them against. -/
def bitwiseFlags (opcode : ℕ) : Vector (ZMod p) 3 :=
  #v[if opcode = 3 then 1 else 0, if opcode = 4 then 1 else 0, if opcode = 5 then 1 else 0]

/-- The `Bitwise` chip's committed input row for one event — a **real** row (`is_real = 1`). The
three variant flags are *not* here: SP1 does not commit them as input columns, the circuit
witnesses them from the hint (`ALUTypeEvent.toBitwiseHint`). -/
def ALUTypeEvent.toBitwiseInputs (e : ALUTypeEvent) : BitwiseChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e

lemma ALUTypeEvent.toBitwiseInputs_adapter (e : ALUTypeEvent) :
    (e.toBitwiseInputs (p := p)).adapter = aluTypeReaderCols e := rfl

/-- **The row's prover hint.** The `"bitwise_flags"` key carries this row's own variant selectors,
computed from **this event's opcode**. This is what makes the built row mean the event: the chip's
`Spec` says the result word is the RV64 operation the *flags* name, so flags unrelated to the
opcode would prove a true statement about the wrong instruction. -/
def ALUTypeEvent.toBitwiseHint (e : ALUTypeEvent) : ProverHint (ZMod p) :=
  flagHint "bitwise_flags" (bitwiseFlags e.opcode)

/-- The `Bitwise` chip's padding row: every column zero, `is_real = 0` (and `imm_c = 0`, the
register-row form the chip's `ProverAssumptions` asks for). Its hint is the empty one, so all three
flags read back as `0` and the selector sum matches `is_real = 0`. -/
def bitwisePaddingInputs : BitwiseChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the flags the builder put in. -/
lemma hintFlags_toBitwiseHint (e : ALUTypeEvent) :
    BitwiseChip.hintFlags (e.toBitwiseHint (p := p)) = bitwiseFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 3) = #v[0, 0, 0] := rfl
  rw [BitwiseChip.hintFlags, ← hdefault, ALUTypeEvent.toBitwiseHint]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as all-zero flags — SP1's own padding convention. -/
lemma hintFlags_empty : BitwiseChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 0, 0] := rfl

/-- **The flags of a real `Bitwise` row are one-hot, and their sum is `1`.** Everything the chip's
`ProverAssumptions` says about the hint, from the routing condition alone: whichever of the three
opcodes the event carries sets exactly that selector. -/
lemma bitwiseFlags_spec {e : ALUTypeEvent} (hop : e.IsBitwise) :
    ((bitwiseFlags (p := p) e.opcode)[0] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[0] = 1) ∧
    ((bitwiseFlags (p := p) e.opcode)[1] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[1] = 1) ∧
    ((bitwiseFlags (p := p) e.opcode)[2] = 0 ∨ (bitwiseFlags (p := p) e.opcode)[2] = 1) ∧
    (bitwiseFlags (p := p) e.opcode)[0] + (bitwiseFlags (p := p) e.opcode)[1]
      + (bitwiseFlags (p := p) e.opcode)[2] = 1 ∧
    ((bitwiseFlags (p := p) e.opcode)[0] = 1 →
      (bitwiseFlags (p := p) e.opcode)[1] = 0 ∧ (bitwiseFlags (p := p) e.opcode)[2] = 0) ∧
    ((bitwiseFlags (p := p) e.opcode)[1] = 1 →
      (bitwiseFlags (p := p) e.opcode)[0] = 0 ∧ (bitwiseFlags (p := p) e.opcode)[2] = 0) ∧
    ((bitwiseFlags (p := p) e.opcode)[2] = 1 →
      (bitwiseFlags (p := p) e.opcode)[0] = 0 ∧ (bitwiseFlags (p := p) e.opcode)[1] = 0) := by
  obtain h | h | h := hop <;> simp [bitwiseFlags, h]

end SP1Clean.TraceGen

namespace SP1Clean.BitwiseChip

open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed register-row `Bitwise` trace event builds a row the honest prover can complete, at
the hint the same event builds.** Every conjunct of `BitwiseChip.ProverAssumptions` follows from
`ALUTypeEvent.WellFormed`, the routing condition `hop : e.IsBitwise`, and `himm : e.immC = 0`.

The `data` is arbitrary — the chip's prover contract does not read it — but the **hint is not**: it
is `e.toBitwiseHint`, the flags of this event's own opcode.
-/
theorem proverAssumptions_of_event {e : ALUTypeEvent} (h : e.WellFormed) (hop : e.IsBitwise)
    (himm : e.immC = 0) (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toBitwiseInputs (p := p)) data e.toBitwiseHint := by
  obtain ⟨hf0, hf1, hf2, hsum, hone0, hone1, hone2⟩ := bitwiseFlags_spec (p := p) hop
  simp only [ProverAssumptions, hintFlags_toBitwiseHint]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, hf2, hsum.symm, hone0, hone1, hone2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  -- the `rs1` read, then the `op_c` block's committed value — a u64 in *either* row form
  · exact wordOfNat_isU64 _
  · exact aluTypeOpCCols_prev_value_isU64 e
  -- the value the `op_a` write displaces
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact aluTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the register-register form: the committed `imm_c` flag is the event's, hence `0`
  · rw [ALUTypeEvent.toBitwiseInputs_adapter, aluTypeReaderCols_imm_c, himm, Nat.cast_zero]
  -- the shared reader contracts: the state block, then the two unconditional register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  -- the `op_c` access: on a register row the block is the ordinary `rs2` read block
  · rw [ALUTypeEvent.toBitwiseInputs_adapter, aluTypeReaderCols_op_c_memory,
      aluTypeOpCCols_of_reg himm]
    exact registerAccessCols_spec_opC h.clk_mod (h.prevTsC_reg himm)
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨aluTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, aluTypeOpCCols_prevLow_val_lt e⟩

/-- **A padding row satisfies the same contract**, at the empty hint. `is_real = 0` makes every
gated conjunct vacuous, and the three flags read back as `0`, so the selector-sum conjunct is
`0 = 0 + 0 + 0`. What survives besides is the two operand `isU64`s and the two zero flags. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (bitwisePaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  simp only [ProverAssumptions, hintFlags_empty]
  refine ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    by simp [bitwisePaddingInputs], fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    rfl, rfl, fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne, ?_,
    fun hr => absurd hr hne, fun hr => absurd hr hne⟩
  intro hr
  have h0 : (0 : ZMod p) = 1 := by rw [← sub_zero (0 : ZMod p)]; exact hr
  exact absurd h0 hne

/-! ## The built table -/

/-- The Bitwise chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
zero rows at the empty hint. -/
def traceInputs (events : List ALUTypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toBitwiseInputs, e.toBitwiseHint))
    ++ List.replicate padding (bitwisePaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint, provided every event is a register-register bitwise instruction. -/
theorem proverAssumptions_of_mem_traceInputs {events : List ALUTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise ∧ e.immC = 0) (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2.1 (h e he).2.2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid Bitwise table.** Every `assertZero` of the whole flattened chip
circuit evaluates to zero on every built row, and no static lookup is left unchecked. -/
theorem traceTable_constraints (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise ∧ e.immC = 0) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding) data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List ALUTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p))
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsBitwise ∧ e.immC = 0) :
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

end SP1Clean.BitwiseChip
