import SP1Clean.FormalModel.TraceGen.Readers
import SP1Clean.Proofs.Chips.MulChip.Witgen
import ToClean.Air.TableBuild

/-! # `SP1Clean.MulChip` — from trace events to a valid AIR table

`MUL`/`MULH`/`MULHU`/`MULHSU`/`MULW` through the trace-generation chain (see
`AddChip/Complete.lean` for the programme note — this chip shares the whole R-type register block
with it — and `BitwiseChip/Complete.lean` for why a multi-opcode chip's hint has to be per row).

**Add's contract plus a five-flag block.** Every reader-side conjunct of
`MulChip.ProverAssumptions` is `AddChip`'s, cited unchanged: the two operand `isU64`s and the
gated `op_a` read-prior `isU64` (the builder commits limbs, so no event conjunct is spent on
them), `is_real` binary, `op_a_0 = 0` from `rd ≠ x0`, the `CPUState` block's contract, the three
`RegisterAccessCols` contracts at the `MemoryAccessPosition` offsets `A = 4` / `B = 3` / `C = 2`,
the gated decode bounds, and the three gated 24-bit prior-access clocks. What is new is the flag
block: five binary selectors, the row gate `is_real = Σ flags` (SP1's `alu/mul/mod.rs:234` — the
chip has no independent real-row column, `is_real` *is* the selector sum), and
`is_mulw = 1 → is_real = 1`.

Those flags are witnessed from the `"mul_flags"` hint key, so — as for `Bitwise` — the builder
produces the hint alongside the input row, and reads the selectors off **this event's own opcode
discriminant** (`RTypeEvent.toMulHint`). `RTypeEvent.IsMul` is the chip's **routing** condition,
and `mulFlags_opcode_eq` is the check that the two really are the same fact: the flags the builder
supplies, weighted by the chip's own `cpu_opcode` expression, recombine to the event's opcode.

**The register-row hypothesis is Add's.** `RTypeEvent.WellFormed.opA_ne_zero` is the ALU family's
routing condition — SP1 sends an `rd = x0` multiply to the `AluX0` chip (whose own routing
condition `opcode < 29` covers all five multiply discriminants) — so it is the right record here,
unchanged.

**Padding is satisfiable.** A zero row at the empty hint reads all five flags as `0`, and
`0 = 0 + 0 + 0 + 0 + 0` holds; `is_mulw = 1` is then false, so the last flag conjunct is vacuous
too. -/

namespace SP1Clean.TraceGen

variable {p : ℕ}

/-- The five variant selectors of a `Mul` row, in the chip's own column order (`is_mul`,
`is_mulh`, `is_mulhu`, `is_mulhsu`, `is_mulw`), read off the executor's opcode discriminant
(`Opcode::{MUL, MULH, MULHU, MULHSU, MULW} = 11, 12, 13, 14, 24`). The same numbers appear in the
chip's `cpu_opcode` expression `is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24`,
which is what the Program-bus fetch checks them against. -/
def mulFlags (opcode : ℕ) : Vector (ZMod p) 5 :=
  #v[if opcode = 11 then 1 else 0, if opcode = 12 then 1 else 0, if opcode = 13 then 1 else 0,
     if opcode = 14 then 1 else 0, if opcode = 24 then 1 else 0]

/-- The `Mul` chip's committed input row for one event — a **real** row (`is_real = 1`). The five
variant flags are *not* here: SP1 does not commit them as input columns, the circuit witnesses
them from the hint (`RTypeEvent.toMulHint`). -/
def RTypeEvent.toMulInputs (e : RTypeEvent) : MulChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e

/-- **The row's prover hint.** The `"mul_flags"` key carries this row's own variant selectors,
computed from **this event's opcode**. This is what makes the built row mean the event: the chip's
`Spec` says the result word is the RV64 multiply the *flags* name, so flags unrelated to the
opcode would prove a true statement about the wrong instruction. -/
def RTypeEvent.toMulHint (e : RTypeEvent) : ProverHint (ZMod p) :=
  flagHint "mul_flags" (mulFlags e.opcode)

/-- The `Mul` chip's padding row: every column zero, `is_real = 0`. Its hint is the empty one, so
all five flags read back as `0` and the selector sum matches `is_real = 0`. -/
def mulPaddingInputs : MulChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroRTypeReaderCols

variable [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- The chip reads back exactly the flags the builder put in. -/
lemma hintFlags_toMulHint (e : RTypeEvent) :
    MulChip.hintFlags (e.toMulHint (p := p)) = mulFlags e.opcode := by
  have hdefault : (default : Vector (ZMod p) 5) = #v[0, 0, 0, 0, 0] := rfl
  rw [MulChip.hintFlags, ← hdefault, RTypeEvent.toMulHint]
  exact flagHint_apply _ _

omit [Fact (2 ^ 24 < p)] in
/-- A padding row's empty hint reads back as all-zero flags — SP1's own padding convention. -/
lemma mulHintFlags_empty : MulChip.hintFlags (ProverHint.empty (ZMod p)) = #v[0, 0, 0, 0, 0] := rfl

omit [Fact (2 ^ 24 < p)] in
/-- **The built flags name the event's instruction.** Weighted by the chip's own `cpu_opcode`
expression — the one `MulChip.main` threads into `RTypeReader` and the Program-bus fetch checks —
the selectors this builder supplies recombine to the event's opcode discriminant. This is the
statement that the hint is *this* row's, not an arbitrary one-hot vector: `ProverAssumptions` pins
the flags only against `is_real`, so without this the built table would be a true theorem about an
unspecified multiply. -/
lemma mulFlags_opcode_eq {e : RTypeEvent} (hop : e.IsMul) :
    (mulFlags (p := p) e.opcode)[0] * 11 + (mulFlags (p := p) e.opcode)[1] * 12
        + (mulFlags (p := p) e.opcode)[2] * 13 + (mulFlags (p := p) e.opcode)[3] * 14
        + (mulFlags (p := p) e.opcode)[4] * 24 = ((e.opcode : ℕ) : ZMod p) := by
  obtain h | h | h | h | h := hop <;> rw [h] <;> norm_num [mulFlags]

omit [Fact (2 ^ 24 < p)] in
/-- **The flags of a real `Mul` row are binary and sum to `1`.** Everything the chip's
`ProverAssumptions` says about the hint, from the routing condition alone: whichever of the five
opcodes the event carries sets exactly that selector. -/
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

/-! ## The chip's honest-prover contract on a built row -/

/--
**A well-formed R-type trace event builds a row the honest prover can complete, at the hint the
same event builds.** Every conjunct of `MulChip.ProverAssumptions` follows from
`RTypeEvent.WellFormed` and the routing condition `hop : e.IsMul`, with no residual side
condition.

The `data` is arbitrary — the chip's prover contract does not read it — but the **hint is not**:
it is `e.toMulHint`, the flags of this event's own opcode (`mulFlags_opcode_eq`).
-/
theorem proverAssumptions_of_event {e : RTypeEvent} (h : e.WellFormed) (hop : e.IsMul)
    (data : ProverData (ZMod p)) :
    ProverAssumptions (e.toMulInputs (p := p)) data e.toMulHint := by
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hsum⟩ := mulFlags_spec (p := p) hop
  simp only [ProverAssumptions, hintFlags_toMulHint]
  refine ⟨?_, ?_, ?_, ?_, hf0, hf1, hf2, hf3, hf4, hsum.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the two source operands, and the value the `op_a` write displaces: committed limb-wise, so
  -- `isU64` regardless of the event
  · exact wordOfNat_isU64 _
  · exact wordOfNat_isU64 _
  · exact fun _ => wordOfNat_isU64 _
  -- the row is real
  · exact Or.inr rfl
  -- `is_mulw = 1 → is_real = 1`: the row is real outright
  · exact fun _ => rfl
  -- `rd ≠ x0`, so the `op_a_0` zeroing flag is off
  · exact rTypeReaderCols_op_a_0_eq_zero h.opA_ne_zero
  -- the shared reader contracts: the state block, then the three register accesses
  · exact cpuState_spec e.clk e.pc h.clk_mod _ _ _
  · exact registerAccessCols_spec_opA h.clk_mod h.prevTsA_lt
  · exact registerAccessCols_spec_opB h.clk_mod h.prevTsB_lt
  · exact registerAccessCols_spec_opC h.clk_mod h.prevTsC_lt
  -- the decode bounds the Program-bus fetch carries
  · exact fun _ => ⟨rTypeReaderCols_op_a_val_lt h.opA_lt, (cpuStateCols_pc_val_lt e.clk e.pc).1,
      (cpuStateCols_pc_val_lt e.clk e.pc).2.1, (cpuStateCols_pc_val_lt e.clk e.pc).2.2⟩
  -- G1: the three pulled prior records' 24-bit access clocks
  · exact fun _ => ⟨registerAccessCols_prevLow_val_lt _ _ _,
      registerAccessCols_prevLow_val_lt _ _ _, registerAccessCols_prevLow_val_lt _ _ _⟩

/-- **A padding row satisfies the same contract**, at the empty hint. `is_real = 0` makes every
gated conjunct vacuous, and the five flags read back as `0`, so the selector-sum conjunct is
`0 = 0 + 0 + 0 + 0 + 0` and `is_mulw = 1` is false. What survives besides is the two operand
`isU64`s and the `op_a_0` flag. -/
theorem proverAssumptions_padding (data : ProverData (ZMod p)) :
    ProverAssumptions (mulPaddingInputs (p := p)) data (ProverHint.empty (ZMod p)) := by
  have hzero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_of_cases (by simp) (by simp) (by simp) (by simp)
  have hne : ¬((0 : ZMod p) = 1) := zero_ne_one
  simp only [ProverAssumptions, mulHintFlags_empty]
  exact ⟨hzero, hzero, fun hr => absurd hr hne, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    Or.inl rfl, Or.inl rfl, by simp [mulPaddingInputs], fun hr => absurd hr hne, rfl,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne,
    fun hr => absurd hr hne, fun hr => absurd hr hne, fun hr => absurd hr hne⟩

/-! ## The built table -/

/-- The Mul chip as a flat-AIR component: one circuit, checked independently on each row.

A plain `def`, deliberately not an `abbrev` (see `AddChip.component` for the measurement). -/
def component : Air.Flat.Component (ZMod p) := ⟨circuit⟩

/-- The rows a trace builds: one input row **paired with its own hint** per event, then `padding`
zero rows at the empty hint. -/
def traceInputs (events : List RTypeEvent) (padding : ℕ) :
    List (Inputs (ZMod p) × ProverHint (ZMod p)) :=
  events.map (fun e => (e.toMulInputs, e.toMulHint))
    ++ List.replicate padding (mulPaddingInputs, ProverHint.empty (ZMod p))

/-- Every row of a built trace — event row or padding row — satisfies the chip's honest-prover
contract at its own hint, provided every event is a multiply instruction. -/
theorem proverAssumptions_of_mem_traceInputs {events : List RTypeEvent} {padding : ℕ}
    (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) (data : ProverData (ZMod p)) :
    ∀ input ∈ traceInputs (p := p) events padding, ProverAssumptions input.1 data input.2 := by
  intro input hin
  rcases List.mem_append.mp hin with hin | hin
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hin
    exact proverAssumptions_of_event (h e he).1 (h e he).2 data
  · rw [List.eq_of_mem_replicate hin]
    exact proverAssumptions_padding data

/-- **A real trace builds a valid Mul table.** Every `assertZero` of the whole flattened chip
circuit — the 45-cell schoolbook multiplication block, the flag gates, the result-placement
selector, the reader glue — evaluates to zero on every built row, and no static lookup is left
unchecked. -/
theorem traceTable_constraints (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
      data).Constraints :=
  Air.Flat.Table.buildHinted_constraints _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The same table satisfies its **channel guarantees** — every message it pushes onto the State,
Memory, Program and Byte channels carries the payload its channel promises. -/
theorem traceTable_guarantees (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (h : ∀ e ∈ events, e.WellFormed ∧ e.IsMul) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
      data).Guarantees :=
  Air.Flat.Table.buildHinted_guarantees _ _ _ computableWitnesses
    (proverAssumptions_of_mem_traceInputs h data)

/-- The table's interaction list on a channel, in closed form: the per-row evaluated interactions,
concatenated in row order. -/
theorem traceTable_interactionsWith (events : List RTypeEvent) (padding : ℕ)
    (data : ProverData (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Air.Flat.Table.buildHinted (component (p := p)) (traceInputs events padding)
        data).interactionsWith channel =
      (traceInputs (p := p) events padding).flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input.1 data input.2) data) :=
  Air.Flat.Table.buildHinted_interactions _ _ _ channel

end SP1Clean.MulChip
