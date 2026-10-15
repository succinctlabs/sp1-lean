import SP1Clean.Proofs.Operations.HintReadSpan
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # The checked span's exact external assumptions

Only the existing Byte range provider is needed by the address additions. The span has no
Memory, hint, or host-call traffic of its own; a consumer must use its endpoints to build and
verify complete word coverage on those ledgers.
-/

namespace SP1Clean.HintReadSpan

open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem main_other_interactions (target : RawChannel (ZMod p)) (notByte : target ≠ byteChannel.toRaw)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil circuit.base target input offset
  simp [circuit, circuit_norm, notByte]

theorem component_spec_of_byte (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env)
    (byte : ({ circuit := circuit } : Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw env) :
    ({ circuit := circuit } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := circuit } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  have same : selected = byteChannel.toRaw := by simpa [circuit, circuit_norm] using member
  simpa only [same] using byte

end SP1Clean.HintReadSpan
