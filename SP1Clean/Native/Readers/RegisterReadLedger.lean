import SP1Clean.Native.Readers.RegisterRead

/-! # Register read Memory projection

The timestamp checks use only Byte. The actual Memory ledger is the gated prior/read-back pair,
with the same register key and word on both sides.
-/

namespace SP1Clean.Readers.RegisterRead

open Circuit Channels
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

theorem main_memory_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pulledIf input.is_real input.prior).toRaw,
       (memoryChannel.pushedIf input.is_real input.pushed).toRaw] := by
  have timestampEmpty := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    RegisterAccessCols.circuit memoryChannel.toRaw (n := offset)
    ⟨input.cols, input.is_real, input.clk_target⟩
    (by simp [RegisterAccessCols.circuit, circuit_norm, memoryChannel, byteChannel]) List.not_mem_nil
  simp only [main, circuit_norm, List.nil_append]
  rw [timestampEmpty, List.nil_append]

end SP1Clean.Readers.RegisterRead
