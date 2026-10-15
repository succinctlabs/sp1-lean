import SP1Clean.Native.Chips.LoadByteStaticChip.Defs
import ToClean.Air.FiniteLookup

/-! # Authentication of the upstream fixed byte table

These lemmas realize the existing `Gadgets.ByteTable`; no new table predicate is introduced.
Its finite contents and membership are independent of prover-supplied table data.
-/

namespace SP1Clean.LoadByteStaticChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Membership means exactly an 8-bit canonical field value. -/
theorem fixedByte_contains_iff (data : Array (ZMod p)) (value : ZMod p) :
    (Gadgets.ByteTable (p := p)).Contains data value ↔ value.val < 256 :=
  ⟨Gadgets.ByteTable.imply_soundness data value,
    Gadgets.ByteTable.implied_by_completeness data value⟩

/-- The fixed lookup is authenticated by its complete, existing 256-element enumeration. -/
def fixedByteLookup : Air.Flat.FiniteLookup (ZMod p) where
  table := (Gadgets.ByteTable (p := p)).toRaw
  rows := List.ofFn (fun i : Fin 256 => #v[Gadgets.fromByte (p := p) i])
  realizes := by
    intro data row
    exact Air.Flat.staticTable_realizes _ data row

/-- Fixed-table size is independent of the workload, including empty and padded workloads. -/
theorem fixedByteLookup_length : (fixedByteLookup (p := p)).rows.length = 256 := by
  dsimp only [fixedByteLookup]
  exact List.length_ofFn

/-- Gating the lookup input is exactly the original active-row byte condition. -/
theorem gated_fixedByte_iff (data : Array (ZMod p)) (gate value : ZMod p)
    (binary : gate = 0 ∨ gate = 1) :
    Gadgets.ByteTable.Contains data (gate * value) ↔ (gate = 1 → value.val < 256) := by
  rw [fixedByte_contains_iff]
  rcases binary with rfl | rfl <;> simp

end SP1Clean.LoadByteStaticChip
