import SP1Clean.Proofs.Operations.HintReadStep

/-! # Constructing successive hint word rows

The constructor preserves the authenticated word and current address. It computes exact
successors under explicit nonwrapping bounds; permitted padded spans derive these bounds later.
-/

namespace SP1Clean.HintReadStep

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def populate (last : Bool) (word : Model.Core.HintQueue.WordRecord (ZMod p))
    (address : fields 3 (ZMod p)) : Inputs (ZMod p) :=
  ⟨word, address, Address.ofNat (Address.toNat word.index + 1),
    if last then address else Address.ofNat (Address.toNat address + 8)⟩

theorem populate_spec (last : Bool) (word : Model.Core.HintQueue.WordRecord (ZMod p))
    (address : fields 3 (ZMod p)) (valid : word.Valid)
    (marker : word.isLast = if last then 1 else 0) (bounded : Address.Bounded address)
    (indexFits : Address.toNat word.index + 1 < 2 ^ 48)
    (addressFits : last = false → Address.toNat address + 8 < 2 ^ 48) :
    Spec last (populate last word address) := by
  refine ⟨valid, marker, bounded, Address.bounded_ofNat _, Address.toNat_ofNat _ indexFits, ?_⟩
  cases last with
  | false => exact ⟨Address.bounded_ofNat _, Address.toNat_ofNat _ (addressFits rfl)⟩
  | true => exact ⟨bounded, by simp [populate]⟩

end SP1Clean.HintReadStep
