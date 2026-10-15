import SP1Clean.Proofs.Operations.HintReadSpan
import SP1Clean.Model.Core.HintQueueWords

/-! # Semantic construction of complete padded span endpoints

The constructor preserves its input address and length words. An aligned permitted HINT_READ
supplies its entire completeness domain; the final padding word is counted for every length.
These endpoints still need a balance-derived consumer walk to authenticate actual row coverage.
-/

namespace SP1Clean.HintReadSpan

open Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem Domain.bounds {address length : ℕ} (domain : Domain address length) :
    address < 2 ^ 48 ∧ length < 2 ^ 48 ∧
      address + length / 8 * 8 < 2 ^ 48 ∧ length / 8 + 1 < 2 ^ 48 := by
  obtain ⟨lower, aligned, upper⟩ := domain
  omega

def populate (address : fields 3 (ZMod p)) (length : Word (ZMod p)) : Inputs (ZMod p) :=
  ⟨address, (AddressDiv8.populate (Address.asWord address)).quotients, AddressDiv8.populate length,
    Address.ofNat (Address.toNat address + Word.toNat length / 8 * 8),
    Address.ofNat (Word.toNat length / 8 + 1)⟩

theorem populate_spec (address : fields 3 (ZMod p)) (length : Word (ZMod p))
    (bounded : Address.Bounded address) (word : Word.isU64 length)
    (domain : Domain (Address.toNat address) (Word.toNat length)) : Spec (populate address length) := by
  refine ⟨bounded, word, domain, Address.bounded_ofNat _, ?_, Address.bounded_ofNat _, ?_⟩
  · exact Address.toNat_ofNat _ domain.bounds.2.2.1
  · exact Address.toNat_ofNat _ domain.bounds.2.2.2

theorem populate_assumptions (address : fields 3 (ZMod p)) (length : Word (ZMod p))
    (bounded : Address.Bounded address) (word : Word.isU64 length)
    (domain : Domain (Address.toNat address) (Word.toNat length)) :
    ProverAssumptions (populate address length) := by
  refine ⟨AddressDiv8.populate_assumptions _ (Address.isU64_asWord bounded) ?_,
    AddressDiv8.populate_assumptions _ word domain.bounds.2.1,
    populate_spec address length bounded word domain⟩
  rw [Address.toNat_asWord]
  exact domain.bounds.1

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Actual padded-write permission and alignment imply the span constructor's native domain. -/
theorem domain_of_permitted (bytes : Bytes) (policy : HostMemoryPolicy) (address : ℕ)
    (lower : 2 ^ 16 ≤ policy.lower) (upper : policy.upper ≤ 2 ^ 48) (aligned : address % 8 = 0)
    (permitted : policy.permits address (hintWriteBytes bytes).length = true) :
    Domain address bytes.length := by
  obtain ⟨start, finish, _⟩ := (policy.permits_iff _ _).mp permitted
  rw [hintWriteBytes_length] at finish
  exact ⟨by omega, aligned, by omega⟩

omit [Fact (2 ^ 17 < p)] in
/-- The bounded count is exactly the immutable node's complete padded word inventory. -/
theorem Spec.word_count {input : Inputs (ZMod p)} (valid : Spec input) (bytes : Bytes)
    (length : Word.toNat input.length.value = bytes.length) :
    Address.toNat input.count = HintQueue.wordCount bytes := by
  rw [valid.2.2.2.2.2.2, length]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- Every required word is aligned and in-window, including the last word at the address ceiling. -/
theorem Spec.word_window {input : Inputs (ZMod p)} (valid : Spec input)
    (index : ℕ) (position : index < Address.toNat input.count) :
    2 ^ 16 ≤ Address.toNat input.start + index * 8 ∧
      (Address.toNat input.start + index * 8) % 8 = 0 ∧
      Address.toNat input.start + index * 8 + 8 ≤ 2 ^ 48 := by
  have lower := valid.2.2.1.1
  have aligned := valid.2.2.1.2.1
  have upper := valid.2.2.1.2.2
  rw [valid.2.2.2.2.2.2] at position
  exact ⟨by omega, by omega, by omega⟩

omit [Fact (2 ^ 17 < p)] in
/-- The last-index computation is positive and exactly reaches the declared final RAM cell. -/
theorem Spec.last_word {input : Inputs (ZMod p)} (valid : Spec input) :
    0 < Address.toNat input.count ∧
      Address.toNat input.start + (Address.toNat input.count - 1) * 8 = Address.toNat input.last := by
  rw [valid.2.2.2.2.2.2, valid.2.2.2.2.1]
  omega

end SP1Clean.HintReadSpan
