import SP1Clean.Proofs.Operations.HintNodeAllocate
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.ChannelClosure

/-! # Allocation uses only the existing Byte ledger

All queue-clock, HostCall, and node-publication interactions belong to the enclosing handler.
This checked arithmetic operation contributes only the address adder's three range requests.
Its local contract follows from raw constraints and the enclosing ensemble's Byte guarantees.
-/

namespace SP1Clean.HintNodeAllocate

open Circuit Air.Flat Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem main_other_interactions (target : RawChannel (ZMod p)) (notByte : target ≠ byteChannel.toRaw)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith target = [] := by
  apply InteractionRecovery.interactionsWith_main_eq_nil circuit.base target input offset
  simpa [circuit, circuit_norm, WordRangeCheck.circuit, AddressOrder.circuit,
    AddrAddOperation.circuit, Gadgets.Equality.circuit] using notByte

theorem component_spec_of_byte (env : Environment (ZMod p))
    (constraints : ({ circuit := circuit } : Component (ZMod p)).operations.ConstraintsHold env)
    (bytes : ({ circuit := circuit } : Component (ZMod p)).operations.ChannelGuarantees byteChannel.toRaw env) :
    ({ circuit := circuit } : Component (ZMod p)).Spec env := by
  apply (Component.weakSoundness (by trivial) constraints ?_).1
  rw [Operations.guarantees_iff _ _ _ (({ circuit := circuit } : Component (ZMod p)).inChannelsOrGuarantees env)]
  intro selected member
  change selected ∈ [byteChannel.toRaw] at member
  obtain rfl := List.mem_singleton.mp member
  exact bytes

end SP1Clean.HintNodeAllocate
