import SP1Clean.Native.Readers.RegisterRead

/-! # Register reads from an ordered prior record

Compute the timestamp gap's low limb from semantic clocks. A later access in the same high-clock
block, a bounded target clock, and a bounded old word suffice for the reader's completeness.
-/

namespace SP1Clean.Readers.RegisterRead

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (value : Word (ZMod p)) (previous high target index gate : ZMod p) : Inputs (ZMod p) :=
  ⟨⟨value, ⟨previous, ((target.val - previous.val - 1) % 65536 : ℕ)⟩⟩,
    high, target, index, gate⟩

def Domain (value : Word (ZMod p)) (previous target gate : ZMod p) : Prop :=
  (gate = 0 ∨ gate = 1) ∧
    (gate = 1 → Word.isU64 value ∧ previous.val < target.val ∧ target.val < 2 ^ 24)

theorem populate_assumptions (value : Word (ZMod p)) (previous high target index gate : ZMod p)
    (valid : Domain value previous target gate) :
    ProverAssumptions (populate value previous high target index gate) := by
  refine ⟨⟨valid.1, fun active => (valid.2 active).2.2⟩, ?_, ?_⟩
  · intro active
    obtain ⟨gap, low, highBound⟩ := MemoryClock.gap_encoding target previous
      (valid.2 active).2.1 (valid.2 active).2.2
    refine ⟨low, ?_⟩
    change ((target - previous - 1 -
      (((target.val - previous.val - 1) % 65536 : ℕ) : ZMod p)) * (65536 : ZMod p)⁻¹).val < 2 ^ 8
    rw [gap, add_sub_cancel_left, mul_inv_cancel_right₀ val_65536_ne_zero]
    exact highBound
  · intro active
    refine ⟨(valid.2 active).1, ?_⟩
    change previous.val < 2 ^ 24
    exact lt_trans (valid.2 active).2.1 (valid.2 active).2.2

end SP1Clean.Readers.RegisterRead
