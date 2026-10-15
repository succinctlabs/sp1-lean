import SP1Clean.Proofs.Chips.OrderedInitialProvider
import SP1Clean.Soundness.RankedGrounding

/-! # Ordered initial records cannot duplicate a memory location

The row circuit authenticates the value and binds the control key to the decoded location.
The only global input here is endpoint balance on those control keys. Strict ordering excludes
both duplicate keys and disconnected cycles, even when rows have different payloads or values.
The machine ensemble must still derive this balance from its actual interaction ledger.
-/

namespace SP1Clean.Soundness.InitialMemoryBoundary

open SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels RankedGrounding

variable {p : ℕ} [Fact p.Prime]
variable {Row : Type} [DecidableEq Row]

/-- Provider uniqueness is derived from ordered control balance, not assumed of the trace. -/
theorem locations_nodup (image : ProgramImage) (rows : Multiset Row)
    (link : Row → OrderedBoundary.Inputs (ZMod p))
    (record : Row → MemoryMsg (ZMod p)) (initial final : Word (ZMod p))
    (valid : ∀ row ∈ rows, OrderedInitialProvider.Spec image (link row) (record row))
    (balanced : EndpointBalanced rows (fun row => ((link row).previous, (link row).current))
      initial final) :
    (rows.map fun row => MemoryMsg.locOf (record row)).Nodup := by
  exact keys_nodup_of_endpointBalanced rows _ Word.toNat
    (fun row => MemoryMsg.locOf (record row)) (fun loc => loc.busAddress + 1) initial final balanced
    (fun row member => (valid row member).2.1.2.2)
    (fun row member => (valid row member).2.2)

end SP1Clean.Soundness.InitialMemoryBoundary
