import SP1Clean.Model.Channels

/-! # Final-record handoff to target snapshot checks

Ordered finalizers publish their complete records here. Register and RAM receipts use distinct
channels, so a RAM value cannot be authenticated through the register table at an overlapping
numeric address. These are accounting channels; they assert no value or historical truth.
-/

namespace SP1Clean.FinalMemoryValue

open Circuit Channels

def channel {p : ℕ} [Fact p.Prime] (ram : Bool) : Channel (ZMod p) MemoryMsg where
  name := if ram then "SP1FinalRamValue" else "SP1FinalRegisterValue"
  Guarantees _ _ := True

@[circuit_norm ↓] theorem guarantees {p : ℕ} [Fact p.Prime] (ram : Bool)
    (record : MemoryMsg (ZMod p)) (data : ProverData (ZMod p)) :
    (channel ram).Guarantees record data := trivial

end SP1Clean.FinalMemoryValue
