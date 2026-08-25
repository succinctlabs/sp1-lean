import SP1Clean.FormalModel.Contracts.SystemChips
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The MemoryBump system table as a Clean circuit (W3, external report Finding 2)

SP1's `MemoryBumpChip::eval` (`../sp1 crates/core/machine/src/memory/bump.rs`), constraint-for-
constraint in the same order: range-check the four refreshed-timestamp limbs and the register-index
address on the Byte bus, then perform the standard `eval_memory_access_read` fragment at the
refreshed clock — pull the register record at its previous timestamp, push the **same value** at the
strictly later canonical timestamp, with the `compare_low`-selected difference range-checked to 24
bits.

The access fragment is written as flat own-asserts rather than composing `Readers.MemoryAccess`:
that reader's contract carries the instruction-row clock discipline (`Readers.ClkDiscipline` — every
`+δ ≤ 4` effect slot stays 24-bit) and bakes the RAM `+1` effect slot into its push, neither of
which a bump row satisfies (its refreshed timestamp is not an intra-instruction slot; its recombined
low clock can sit at `2^24 - 1`). The columns still reuse the shared `MemoryAccessCols` carrier, so
the shape matches the load/store chips cell-for-cell. All fifteen cells are inputs
(`localLength = 0`); the row struct and semantic `Spec` live in
`FormalModel/Contracts/SystemChips.lean`, the proofs in `Proofs/Chips/MemoryBumpChip/Formal.lean`. -/

namespace SP1Clean.MemoryBumpChip

open Circuit
open SP1Clean.Channels (memoryChannel byteChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The pulled register record (previous timestamp). Shared by `main` and the trace layer. -/
@[circuit_norm] def pulledMsg (r : Var Inputs (ZMod p)) : MemoryMsg (Expression (ZMod p)) :=
  ⟨r.access.access_timestamp.prev_high, r.access.access_timestamp.prev_low,
    r.addr, 0, 0, r.access.prev_value⟩

/-- The pushed refreshed record — same address and value, the canonically-limbed later timestamp.
Shared by `main` and the trace layer. -/
@[circuit_norm] def pushedMsg (r : Var Inputs (ZMod p)) : MemoryMsg (Expression (ZMod p)) :=
  ⟨r.clk_24_32 + r.clk_32_48 * 256, r.clk_0_16 + r.clk_16_24 * 65536,
    r.addr, 0, 0, r.access.prev_value⟩

/-- SP1's `MemoryBumpChip::eval`, in its constraint order: the `is_real` boolean gate, the two
16-bit and paired 8-bit refreshed-clock limb checks, the register-index `LTU` check, and the
`eval_memory_access_read` fragment at the refreshed clock (the three `is_real`-gated timestamp
asserts, the two difference-limb byte checks, the record pull and the refreshed push). -/
def main (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ts := r.access.access_timestamp
  -- Inline shallow boolean gate (`assertZero`, visible to `ConstraintsHold.Shallow`) — it discharges
  -- every gated pull's off-gate `Requirements` without keeping `byteChannel` in
  -- `channelsWithRequirements`.
  assertZero (r.is_real * (r.is_real - 1))
  byteChannel.pullIf r.is_real
    (⟨6, r.clk_0_16, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨6, r.clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨3, 0, r.clk_16_24, r.clk_24_32⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨4, 1, r.addr, Expression.const ((32 : ℕ) : ZMod p)⟩ : ByteRow (Expression (ZMod p)))
  assertZero (r.is_real * (ts.compare_low * (ts.compare_low - 1)))
  assertZero (r.is_real *
    (ts.compare_low * (r.clk_24_32 + r.clk_32_48 * 256 - ts.prev_high)))
  assertZero (r.is_real *
    ((ts.compare_low * (r.clk_0_16 + r.clk_16_24 * 65536)
        + (1 - ts.compare_low) * (r.clk_24_32 + r.clk_32_48 * 256)
      - (ts.compare_low * ts.prev_low + (1 - ts.compare_low) * ts.prev_high) - 1)
    - (ts.diff_low_limb + ts.diff_high_limb * 65536)))
  byteChannel.pullIf r.is_real
    (⟨6, ts.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨3, 0, ts.diff_high_limb, 0⟩ : ByteRow (Expression (ZMod p)))
  memoryChannel.pullIf r.is_real (pulledMsg r)
  memoryChannel.pushIf r.is_real (pushedMsg r)

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw, memoryChannel.toRaw]
  -- The `change`-to-op-list shape (the `Readers.MemoryAccess` pattern): the nested
  -- `MemoryAccessCols` carrier makes a `main`-unfolding `simp` prohibitively expensive, so state the
  -- op list directly and split the interaction membership by hand.
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    change Operations.ChannelsLawful
      ([.assert _, .interact _, .interact _, .interact _, .interact _, .assert _, .assert _,
        .assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, memoryChannel.toRaw]
    refine ⟨by simp only [circuit_norm], ?_, by simp only [circuit_norm]⟩
    intro env
    rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
    intro interaction h_interaction
    simp only [circuit_norm] at h_interaction
    rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl List.mem_cons_self
    · exact Or.inl List.mem_cons_self
    · exact Or.inl List.mem_cons_self
    · exact Or.inl List.mem_cons_self
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

end SP1Clean.MemoryBumpChip
