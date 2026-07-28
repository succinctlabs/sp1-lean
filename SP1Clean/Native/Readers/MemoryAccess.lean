import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels
import SP1Clean.Extracted.MemoryAccess
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `MemoryAccess` primitive — one true-address memory read/write as a Clean `GeneralFormalCircuit`

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
    input.mem.access_timestamp.diff_high_limb.val < 2 ^ 8 ∧
    -- (W11 memory flip) the read prior `prev_value` is `isU64`, derived from the memory read-prior pull,
    -- and — G1 — that prior record's low access clock is 24-bit (`Channels.MemoryMsg.ClkBound`, the clock
    -- half of the memory channel's `Guarantees`). Unlike the register readers the pulled key here is the
    -- *previous* timestamp pair `(prev_high, prev_low)`, so the bound lands on `prev_low` directly. It is
    -- what upgrades the field-level gap decomposition above to a genuine ℕ-level timestamp ordering
    -- (`Soundness/TimeExtraction.lean`).
    Word.isU64 input.mem.prev_value ∧
    input.mem.access_timestamp.prev_low.val < 2 ^ 24

/-- Impose the three `is_real`-gated timestamp asserts (`compare_low` boolean, the high-limb-equality gate,
the diff decomposition), the two `is_real`-gated byte range checks (`diff_low < 2^16`, `diff_high < 2^8`),
and emit the two Memory interactions (send prior value at prev timestamp `+is_real`, receive `new_value` at
`(clk_high, clk_low + 1)` `−is_real`). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ts := input.mem.access_timestamp
  -- Local, shallow `is_real` boolean gate (faithful — SP1's memory-access `assert_bool`); kept inline
  -- (`assertZero`, not `=== 0`) so it is visible to `ConstraintsHold.Shallow`, discharging the off-gate
  -- byte-pull `Requirements` without keeping `byteChannel` in `channelsWithRequirements`.
  assertZero (input.is_real * (input.is_real - 1))
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
  -- **W11 polarity flip:** the *send* of the prior value is now a `pullIf` (the chip *derives*
  -- `MemoryMsg.isU64` of `prev_value`) and the *receive* of `new_value` a `pushIf` (the chip *proves*
  -- `isU64` of the pushed `new_value` — from the `isU64 new_value` `Assumptions` conjunct: a read pins
  -- `new = prev_value` (from the pull), a write supplies the store value's range-check).
  memoryChannel.pullIf input.is_real
    (⟨ts.prev_high, ts.prev_low, input.addr0, input.addr1, input.addr2,
      input.mem.prev_value⟩ : MemoryMsg (Expression (ZMod p)))
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low + 1, input.addr0, input.addr1, input.addr2,
      input.new_value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- `byteChannel` (the two timestamp range pulls) + `memoryChannel` (W11 memory flip — the prior `pullIf`
  -- derives `MemoryMsg.isU64`, so it joins `channelsWithGuarantees`; its `new_value` `pushIf` keeps it in
  -- `channelsWithRequirements`).
  channelsWithGuarantees := [byteChannel.toRaw, memoryChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    change Operations.ChannelsLawful
      ([.assert _, .subcircuit _, .subcircuit _, .subcircuit _, .interact _, .interact _,
        .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, memoryChannel.toRaw]
    refine ⟨by simp only [circuit_norm], ?_, by simp only [circuit_norm]⟩
    intro env
    rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
    intro interaction h_interaction
    simp only [circuit_norm] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl
    · exact Or.inl List.mem_cons_self
    · exact Or.inl List.mem_cons_self
    · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the `is_real`-gated byte receives + asserts. The `isU64
new_value` conjunct (W11 memory flip): the value placed at the current timestamp is `U64` (a read pins it to
the just-pulled `prev_value`; a write supplies its store value's range-check) — needed to prove the
`new_value` **push**'s `MemoryMsg.isU64`. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_real = 1 → Word.isU64 input.new_value) ∧
    -- G1: the **push** places `new_value` at the current timestamp `(clk_high, clk_low + 1)`, so the memory
    -- channel's `MemoryMsg.ClkBound` requirement lands on `clk_low + 1` — the RAM `+1` effect slot, vs the
    -- register readers' `+4/+3/+2` operand slots. `clk_low` is a raw cross-block input here (**unshifted**:
    -- the `+ 1` is applied inside this circuit), so the assumption is the same named `Readers.ClkDiscipline`
    -- every register reader takes, and soundness picks the `+ 1` slot out of it with `ClkDiscipline.at_one`.
    ClkDiscipline input.clk_low input.is_real

/-! ### `ProverData`-lifted forms (SC Phase 2pre)

The reader upgrades `FormalAssertion → GeneralFormalCircuit` (Output = `unit`) so its `Spec` can, in a
later phase, re-export the data-relative pull guarantees. Content UNCHANGED: `AssumptionsD`/`SpecD` ignore
the extra `ProverData`/`output`, so the soundness/completeness bodies are the old ones (modulo the
`AssumptionsD`/`SpecD` folds and any `dsimp`/`show` reductions the record reassembly needs). -/

/-- The soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- The soundness spec, lifted to ignore the `unit` output and `ProverData`. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- The completeness assumption (an assertion assumes both `Assumptions` and `Spec`). -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop := Assumptions input ∧ Spec input

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  simp only [circuit_norm, AssumptionsD, SpecD, byteChannel, memoryChannel, MemoryMsg.isU64,
    MemoryMsg.ClkBound] at h_holds h_assumptions ⊢
  -- the leading `_` is the inline `is_real` boolean gate (unused in soundness — `Assumptions` already gives
  -- `is_real ∈ {0,1}`); `a1 a2 a3` the three timestamp asserts, `b4 b5` the two byte-pull guarantees, and
  -- `h_mem` the memory read-prior pull's guarantee — now a PAIR: `Word.isU64` of the whole `prev_value`
  -- word and — G1 — the pulled record's `prev_low` 24-bit clock bound.
  obtain ⟨_, a1, a2, a3, b4, b5, h_mem⟩ := h_holds
  -- The byte-pull off-gate `Requirements` + the memory pull off-gate are vacuous; the memory **push** owes
  -- `Word.isU64` of `new_value` and the `ClkBound` of its `clk_low + 1` push clock — exactly the two gated
  -- `Assumptions` conjuncts (real row via ¬is_real = 0).
  refine ⟨fun hr1 => ?_, fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions.1 h1 h0,
    fun _ h0 => ⟨h_assumptions.2.1 (h_assumptions.1.resolve_left h0),
      h_assumptions.2.2.at_one (h_assumptions.1.resolve_left h0)⟩⟩
  -- Spec consequent (real row); the `isU64 prev_value` conjunct is the memory pull `h_mem` verbatim.
  -- `hr1`/the goal carry the reassembled `{record}.field` projections (the `SpecD` wrapper); `dsimp only`
  -- iota-reduces them to the destructured atoms (`selCur`/`selPrev` stay folded) so the `rw`s below match.
  dsimp only at hr1 ⊢
  rw [hr1, one_mul] at a1 a2 a3
  refine ⟨bool_of_mul_pred a1, a2, ?_,
    (byteRowSpec_range _ sixteen_lt).mp (by rw [Nat.cast_ofNat]; exact b4 (by rw [hr1])),
    ((byteRowSpec_u8range_pair _ _).mp (b5 (by rw [hr1]))).1, h_mem (by rw [hr1])⟩
  simp only [selCur, selPrev]; linear_combination a3

theorem completeness :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [ProverAssumptionsD] at h_assumptions
  obtain ⟨h_assumptions, h_spec⟩ := h_assumptions
  simp only [circuit_norm, byteChannel, memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
  obtain ⟨hbin, hnew, -⟩ := h_assumptions
  -- `hbin` carries the reassembled `{record}.is_real` projection (the `ProverAssumptionsD` reassembly);
  -- `dsimp only` iota-reduces it to the destructured atom so the `simp`/`rw`-gates below match.
  dsimp only at hbin
  rcases hbin with h0 | h1
  · -- padding row (`is_real = 0`): the leading gate + every gated assert is `0 · _`, the byte/memory pulls
    -- fire only off-padding.
    have hne : ∀ {P : Prop}, - input_is_real = -1 → P :=
      fun h => absurd (neg_inj.mp h) (by rw [h0]; exact zero_ne_one)
    refine ⟨?_, ?_, ?_, ?_, hne, hne, hne⟩ <;> simp only [h0, zero_mul]
  · -- real row (`is_real = 1`): the asserts come from the `Spec` facts, the byte pulls from its ranges, the
    -- memory pull from its `isU64 prev_value` + G1 `prev_low` clock-bound conjuncts.
    obtain ⟨hcl, ha2, ha3, hd_low, hd_high, hisu, hclk⟩ := h_spec h1
    -- the `Spec`-derived facts carry the reassembled `{record}.field` projections; `dsimp only` reduces
    -- them to atoms (`selCur`/`selPrev` stay folded) so the `rw`/`linear_combination`s below match.
    dsimp only at *
    simp only [selCur, selPrev] at ha3
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [h1, sub_self, mul_zero]
    · rw [h1, one_mul]; rcases hcl with h | h <;> rw [h] <;> ring
    · rw [h1, one_mul]; linear_combination ha2
    · rw [h1, one_mul]; linear_combination ha3
    · intro _; simpa only [Nat.cast_ofNat] using (byteRowSpec_range _ sixteen_lt).mpr hd_low
    · intro _; exact (byteRowSpec_u8range_pair _ _).mpr ⟨hd_high, by rw [ZMod.val_zero]; norm_num⟩
    · intro _; exact ⟨hisu, hclk⟩

/-- The native memory-access primitive as a Clean `GeneralFormalCircuit`: timestamp monotonicity columns +
the two Memory-bus interactions at a real 48-bit address, parameterised by the written `new_value`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit :=
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate byte-pull `Requirements` are now discharged by the
  -- inline `is_real` boolean gate in `main`, so only the Memory bus stays in `channelsWithRequirements`
  -- (it carries the real send/receive emits); `byteChannel` moves to a Clean `SoundEnsemble` provider later.
  { main, elaborated,
    Assumptions := AssumptionsD, Spec := SpecD,
    ProverAssumptions := ProverAssumptionsD, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      change Operations.RequirementsChannelsLawful
        ([.assert _, .subcircuit _, .subcircuit _, .subcircuit _, .interact _, .interact _,
          .interact _, .interact _] : Operations (ZMod p))
          [byteChannel.toRaw, memoryChannel.toRaw] [memoryChannel.toRaw]
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨by simp only [circuit_norm], ?_, ?_⟩
      · intro channel h_channel
        -- `circuit_norm`'s `or_self` collapses the trailing duplicate: a 3- not 4-way split.
        simp only [circuit_norm] at h_channel
        rcases h_channel with rfl | rfl | rfl
        · exact Or.inl List.mem_cons_self
        · exact Or.inl List.mem_cons_self
        · exact Or.inr List.mem_cons_self
      · intro env h_constraints
        have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
            (ProvableStruct.eval env input_var).is_real = 1 := by
          apply bool_of_mul_pred
          simpa only [circuit_norm] using h_constraints.1
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [circuit_norm] at h_interaction
        -- The two byte pulls and the memory read-prior pull are `is_real`-gated, so their
        -- requirement is off-gate vacuous; only the memory **push** (unnegated multiplicity
        -- `is_real`) has to be delegated to `channelsWithRequirements`.
        rcases h_interaction with rfl | rfl | rfl | rfl <;>
          first
            | (right; rw [ChannelInteraction.toRaw_requirements]; intro h1 h0;
               simp only [circuit_norm] at h1 h0; exact off_gate_vacuous h_bool h1 h0)
            | exact Or.inl List.mem_cons_self }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.MemoryAccess
