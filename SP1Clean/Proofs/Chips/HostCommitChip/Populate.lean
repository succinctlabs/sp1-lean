import SP1Clean.Proofs.Chips.HostCommitChip.Formal

/-! # Constructing native commitment rows

Only the selected call's semantic value bounds and strict clock order are supplied. The
comparison and byte columns are computed, including for repeated updates of the same slot.
-/

namespace SP1Clean.HostCommitChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (deferred : Bool) (call : HostCallChip.Message (ZMod p)) (previous : State (ZMod p)) :
    Inputs (ZMod p) :=
  ⟨call, previous, LtOperationUnsigned.populate call.arg2 (BoundedWord.limit (bound p deferred)),
    U16toU8OperationSafe.populate call.arg2⟩

def Domain (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (previous : State (ZMod p)) : Prop :=
  CallSpec deferred slot call ∧
    ClockOrder.Spec ⟨previous.clk_high, previous.clk_low, call.clk_high, call.clk_low⟩

theorem populate_assumptions (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (previous : State (ZMod p)) (valid : Domain deferred slot call previous) :
    ProverAssumptions deferred slot (populate deferred call previous) := by
  refine ⟨⟨valid.1, valid.2, ?_⟩, rfl⟩
  have word : Word.isU64 call.arg2 := valid.1.2.2.2.2.1
  exact U16toU8OperationSafe.spec_populate (word 0) (word 1) (word 2) (word 3) (1 : ZMod p) rfl

end SP1Clean.HostCommitChip
