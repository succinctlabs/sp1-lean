import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.Model.Core.NativeLayout

/-! # RAM-specific finalization

The RAM finalizer checks the native guest window. Its contract retains this distinction
through the ordering and receipt wrappers, so an authenticated target byte read denotes a
RAM observation in the existing complete snapshot. Values and clocks remain global facts.
-/

namespace SP1Clean.MemoryBoundary

open Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime]

/-- A canonical final RAM record lies outside the native reserved low region. -/
def RamFinalSpec (message : MemoryMsg (ZMod p)) : Prop :=
  FinalSpec message ∧ NativeLayout.guestMemory.lower ≤ (MemoryMsg.locOf message).busAddress

/-- RAM-specific finalization also preserves the caller's semantic query address. -/
def RamFinalAtSpec (query : ℕ) (message : MemoryMsg (ZMod p)) : Prop :=
  RamFinalSpec message ∧ Word.toNat (address message) = query

/-- The RAM contract retains the original shared finalization interface. -/
theorem RamFinalAtSpec.finalAt {query : ℕ} {message : MemoryMsg (ZMod p)}
    (spec : RamFinalAtSpec query message) : FinalAtSpec query message :=
  ⟨spec.1.1, spec.2⟩

end SP1Clean.MemoryBoundary
