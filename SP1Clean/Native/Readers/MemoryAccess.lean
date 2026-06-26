import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels
import SP1Clean.Extracted.LoadByteChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `MemoryAccess` primitive — one true-address memory read/write as a Clean `FormalAssertion`

SP1's `eval_memory_access_read` / `eval_memory_access_write` + `eval_memory_access_timestamp`
(`crates/core/machine/src/air/memory.rs`), mirrored in the `memory_access` fragment of every
`Extracted/{Load,Store}*Chip.lean`. The Memory bus operates at a *real* 48-bit address (`addr0/1/2 ≠
register-index shape`); the read/write distinction is carried by the `new_value` parameter
(read: `new = prev_value`; write: `new = store_value`).

Per real row it imposes the **48-bit timestamp monotonicity** machinery — `compare_low` selects whether the
high clock limbs match (then compare the low limbs) or differ (compare the high limbs); the gap
`selected_cur − selected_prev − 1` is a 24-bit value `diff_low + diff_high·2^16` (range-checked 16 + 8 on the
Byte bus) — and emits the two Memory interactions: a **send** of the prior value at the previous timestamp
(`+is_real`) and a **receive** of `new_value` at the current timestamp `(clk_high, clk_low + 1)` (`−is_real`).
The bus's cross-row meaning (offline-memory, last-write-wins) is the trace level
(`Soundness/MemoryConsistency.lean`); this primitive supplies the per-row monotonicity + emission. -/

namespace SP1Clean.Readers.MemoryAccess

open Circuit
open SP1Clean.Channels (byteChannel memoryChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `16 < p`, so the `Range` width column `16` round-trips through `byteRowSpec_range`. -/
lemma h16p : (16 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega

/-- The cross-block inputs. `mem` is the chip-owned `MemoryAccessCols` (`prev_value` + the 5 timestamp
columns); `clk_high`/`clk_low` are the current clock limbs; `addr0/1/2` the 3-limb memory address (from
`AddressOperation`); `new_value` the value placed at the current timestamp (`= prev_value` for a read,
`= store_value` for a write); `is_real` the row selector. -/
structure Inputs (F : Type) where
  mem : Extracted.MemoryAccessCols F
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  new_value : (Word F)
  is_real : F
deriving ProvableStruct

/-- The previous-timestamp representative `compare_low · prev_low + (1 − compare_low) · prev_high`. -/
@[reducible] def selPrev (ts : Extracted.MemoryAccessTimestamp (ZMod p)) : ZMod p :=
  ts.compare_low * ts.prev_low + (1 - ts.compare_low) * ts.prev_high

/-- The current-timestamp representative `compare_low · (clk_low + 1) + (1 − compare_low) · clk_high`. -/
@[reducible] def selCur (ts : Extracted.MemoryAccessTimestamp (ZMod p)) (clk_high clk_low : ZMod p) : ZMod p :=
  ts.compare_low * (clk_low + 1) + (1 - ts.compare_low) * clk_high

/-- Semantic contract (`is_real`-gated): on a real row the timestamp columns are well-formed — `compare_low`
boolean, the high clock limbs equal when comparing the low parts, and the gap
`selected_cur − selected_prev − 1` is the 24-bit value `diff_low + diff_high·2^16` (with the two limbs
genuinely 16/8-bit). Together these witness `(prev_high, prev_low) < (clk_high, clk_low + 1)` (timestamp
monotonicity), which the offline-memory trace argument consumes. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (input.mem.access_timestamp.compare_low = 0 ∨ input.mem.access_timestamp.compare_low = 1) ∧
    input.mem.access_timestamp.compare_low * (input.clk_high - input.mem.access_timestamp.prev_high) = 0 ∧
    selCur input.mem.access_timestamp input.clk_high input.clk_low - selPrev input.mem.access_timestamp - 1
      = input.mem.access_timestamp.diff_low_limb + input.mem.access_timestamp.diff_high_limb * 65536 ∧
    input.mem.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
    input.mem.access_timestamp.diff_high_limb.val < 2 ^ 8

/-- Impose the three `is_real`-gated timestamp asserts (`compare_low` boolean, the high-limb-equality gate,
the diff decomposition), the two `is_real`-gated byte range checks (`diff_low < 2^16`, `diff_high < 2^8`),
and emit the two Memory interactions (send prior value at prev timestamp `+is_real`, receive `new_value` at
`(clk_high, clk_low + 1)` `−is_real`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ts := input.mem.access_timestamp
  input.is_real * (ts.compare_low * (ts.compare_low - 1)) === 0
  input.is_real * (ts.compare_low * (input.clk_high - ts.prev_high)) === 0
  input.is_real * ((ts.compare_low * (input.clk_low + 1) + (1 - ts.compare_low) * input.clk_high
      - (ts.compare_low * ts.prev_low + (1 - ts.compare_low) * ts.prev_high) - 1)
    - (ts.diff_low_limb + ts.diff_high_limb * 65536)) === 0
  byteChannel.pullIf input.is_real
    (⟨6, ts.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨3, 0, ts.diff_high_limb, 0⟩ : ByteRow (Expression (ZMod p)))
  memoryChannel.emit input.is_real
    (⟨ts.prev_high, ts.prev_low, input.addr0, input.addr1, input.addr2,
      input.mem.prev_value[0], input.mem.prev_value[1], input.mem.prev_value[2],
      input.mem.prev_value[3]⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.emit (-input.is_real)
    (⟨input.clk_high, input.clk_low + 1, input.addr0, input.addr1, input.addr2,
      input.new_value[0], input.new_value[1], input.new_value[2], input.new_value[3]⟩ :
      MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the `is_real`-gated byte receives + asserts. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel, memoryChannel] at h_holds ⊢
  obtain ⟨a1, a2, a3, b4, b5⟩ := h_holds
  -- The two trailing conjuncts are the byte pulls' own `Requirements` (diff_low/diff_high range
  -- checks) — vacuous off-gate; the two Memory emits add no soundness obligation.
  refine ⟨fun hr1 => ?_, fun h1 h0 => off_gate_vacuous h_assumptions h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions h1 h0⟩
  rw [hr1, one_mul] at a1 a2 a3
  have hb4 := b4 (by rw [hr1]); rw [← c16] at hb4
  have hb5 := b5 (by rw [hr1])
  -- strip the `id (ZMod p)` `ProvableType` carrier off the `Spec` body so `ring`/`sub_eq_add_neg`
  -- resolve (the `id` carrier, à la `LtOperationUnsigned`; `docs/agents/mul-operation-learnings.md` §1).
  simp only [id] at *
  refine ⟨bool_of_mul_pred a1, ?_, ?_, (byteRowSpec_range _ h16p).mp hb4, ?_⟩
  · rw [sub_eq_add_neg]; exact a2
  · simp only [selCur, selPrev]; linear_combination a3
  · exact ((byteRowSpec_u8range_pair _ _).mp hb5).1

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
  simp only [circuit_norm, byteChannel]
  rcases h_assumptions with h0 | h1
  · -- padding row (`is_real = 0`): every gated assert is `0 · _`, the byte pulls fire only off-padding.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [h0, zero_mul]
    · simp only [h0, zero_mul]
    · simp only [h0, zero_mul]
    · intro h; have h1 := neg_inj.mp h; rw [h0] at h1; exact absurd h1 zero_ne_one
    · intro h; have h1 := neg_inj.mp h; rw [h0] at h1; exact absurd h1 zero_ne_one
  · -- real row (`is_real = 1`): the asserts come from the `Spec` facts, the byte pulls from its ranges.
    obtain ⟨hcl, ha2, ha3, hd_low, hd_high⟩ := h_spec h1
    simp only [id] at *
    simp only [selCur, selPrev] at ha3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, one_mul]; rcases hcl with h | h <;> rw [h] <;> ring
    · rw [h1, one_mul]; linear_combination ha2
    · rw [h1, one_mul]; linear_combination ha3
    · intro _; rw [← c16]; exact (byteRowSpec_range _ h16p).mpr hd_low
    · intro _; exact (byteRowSpec_u8range_pair _ _).mpr ⟨hd_high, by rw [ZMod.val_zero]; norm_num⟩

/-- The native memory-access primitive as a Clean `FormalAssertion`: timestamp monotonicity columns +
the two Memory-bus interactions at a real 48-bit address, parameterised by the written `new_value`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [byteChannel.toRaw, memoryChannel.toRaw] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.MemoryAccess
