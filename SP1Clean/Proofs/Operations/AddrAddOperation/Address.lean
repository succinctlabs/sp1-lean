import SP1Clean.Proofs.Operations.AddrAddOperation.Formal
import SP1Clean.Math.Address

/-! # Exact natural sums from the existing bounded address adder

The adder's final carry excludes 48-bit overflow. Once the semantic operands rule out 64-bit
wrap, its result is the ordinary sum. The converse constructs the adder contract directly from
a canonical sum, keeping host consumers independent of its limb-level constraint decomposition.
-/

namespace SP1Clean.AddrAddOperation

variable {p : ℕ} [Fact p.Prime]

theorem exact_sum (a b : Word (ZMod p)) (result : fields 3 (ZMod p))
    (checked : Spec ⟨a, b, ⟨result⟩, 1⟩) (noWrap : Word.toNat a + Word.toNat b < 2 ^ 64) :
    Address.Bounded result ∧ Address.toNat result = Word.toNat a + Word.toNat b ∧
      Word.toNat a + Word.toNat b < 2 ^ 48 := by
  obtain ⟨sum, low, middle, high, fits⟩ := checked rfl
  rw [Nat.mod_eq_of_lt noWrap] at fits
  rw [Nat.mod_eq_of_lt fits] at sum
  refine ⟨?_, ?_, fits⟩
  · intro index
    fin_cases index <;> assumption
  · simpa only [Address.toNat, Nat.mul_comm, Nat.reducePow] using sum

theorem spec_of_sum (a b : Word (ZMod p)) (result : fields 3 (ZMod p))
    (bounded : Address.Bounded result) (sum : Address.toNat result = Word.toNat a + Word.toNat b) :
    Spec ⟨a, b, ⟨result⟩, 1⟩ := by
  have fits : Word.toNat a + Word.toNat b < 2 ^ 48 := by
    rw [← sum]
    exact Address.toNat_lt bounded
  intro _
  refine ⟨?_, bounded 0, bounded 1, bounded 2, ?_⟩
  · rw [Nat.mod_eq_of_lt fits]
    simpa only [Address.toNat, Nat.mul_comm, Nat.reducePow] using sum
  · rwa [Nat.mod_eq_of_lt (show Word.toNat a + Word.toNat b < 2 ^ 64 by omega)]

end SP1Clean.AddrAddOperation
