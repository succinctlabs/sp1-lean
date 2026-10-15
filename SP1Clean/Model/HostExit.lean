import SP1Clean.Model.Channels

/-! # Complete native terminal receipts

This channel distinguishes a real HALT from legacy zero-valued Exit padding. Its payload is
the complete exit word; the local boundary decides whether a receipt is required.
-/

namespace SP1Clean.HostExitBoundary

open Circuit

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Word where
  name := "SP1HostExit"
  Guarantees _ _ := True

end SP1Clean.HostExitBoundary
