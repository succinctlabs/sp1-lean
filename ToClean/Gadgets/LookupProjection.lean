module

public import Clean.Gadgets.Bits
public import ToClean.Circuit.SubcircuitProjection

/-! # Lookup metadata for Clean's bit decomposition

Clean's bit decomposition uses witnesses and assertions only. This projection lemma is an
upstream addition: consumers can establish their lookup inventory without unfolding its
proof-bearing circuit or each iteration of the bit loop.
-/

@[expose] public section

namespace Gadgets.ToBits

variable {p : ℕ} [Fact p.Prime]

/-- Bit decomposition contributes no lookup operations, at any width or row offset. -/
@[circuit_norm] theorem main_lookups (n offset : ℕ) (input : Expression (F p)) :
    ((main n input).operations offset).lookups = [] := by
  simp [main, circuit_norm, Gadgets.Equality.main, Operations.lookups]

end Gadgets.ToBits
