import SP1Clean.Proofs.Completeness.Assembly

/-!
# Exact native interaction footprint

Clean's balance predicate includes one non-algebraic capacity condition: each channel's complete
interaction list must be shorter than the field characteristic.  This module gives that condition a
small, explicit carrier.  It is deliberately separate from semantic trace readiness and from
provider multiplicity: aggregate provider counts may wrap as field elements without harming field
balance, while the number of interaction *occurrences* may not reach the characteristic.

`NativeTraceFootprint.ofTrace` measures the actual assembled Clean witness.  A future exact-Core
adapter may add padding and then recompute this value; the unpadded native compiler uses it as-is.
-/

namespace SP1Clean.Soundness

open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Exact per-channel occurrence counts of one native ensemble witness. -/
structure NativeTraceFootprint where
  state : ℕ
  byte : ℕ
  program : ℕ
  memory : ℕ
deriving DecidableEq, Repr

namespace NativeTraceFootprint

/-- Clean's interaction-count capacity condition, stated without any multiplicity bound. -/
def Fits (footprint : NativeTraceFootprint) (characteristic : ℕ) : Prop :=
  footprint.state < characteristic ∧
    footprint.byte < characteristic ∧
    footprint.program < characteristic ∧
    footprint.memory < characteristic

/-- Measure the four channels of the actual generated native witness. -/
noncomputable def ofTrace (trace : SupportedCoreTraceWitness p) : NativeTraceFootprint where
  state := (trace.witness.allTablesWitness.interactionsWith stateChannel.toRaw).length
  byte := (trace.witness.allTablesWitness.interactionsWith byteChannel.toRaw).length
  program := (trace.witness.allTablesWitness.interactionsWith programChannel.toRaw).length
  memory := (trace.witness.allTablesWitness.interactionsWith memoryChannel.toRaw).length

theorem fits_of_balancedChannels (trace : SupportedCoreTraceWitness p)
    (balanced : trace.witness.BalancedChannels) : (ofTrace trace).Fits p := by
  have stateBalanced := balanced stateChannel.toRaw (by
    simp [sp1Ensemble_channels])
  have byteBalanced := balanced byteChannel.toRaw (by
    simp [sp1Ensemble_channels])
  have programBalanced := balanced programChannel.toRaw (by
    simp [sp1Ensemble_channels])
  have memoryBalanced := balanced memoryChannel.toRaw (by
    simp [sp1Ensemble_channels])
  have primePos : 0 < p := (Fact.out : p.Prime).pos
  have charNe : ringChar (ZMod p) ≠ 0 := by
    simpa only [ZMod.ringChar_zmod_n] using (Nat.ne_of_gt primePos)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [ofTrace, Fits, ZMod.ringChar_zmod_n] using
      stateBalanced.1.resolve_right charNe
  · simpa only [ofTrace, ZMod.ringChar_zmod_n] using
      byteBalanced.1.resolve_right charNe
  · simpa only [ofTrace, ZMod.ringChar_zmod_n] using
      programBalanced.1.resolve_right charNe
  · simpa only [ofTrace, ZMod.ringChar_zmod_n] using
      memoryBalanced.1.resolve_right charNe

end NativeTraceFootprint

end SP1Clean.Soundness
