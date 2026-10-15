import SP1Clean.FormalModel.Contracts.HostCommit
import SP1Clean.Native.Operations.ClockOrder
import SP1Clean.Native.Operations.BoundedWord
import SP1Clean.Circuits.Gadgets.U16toU8Safe
import ToClean.Circuit.InteractionRecovery
import Clean.Gadgets.Equality

/-! # A native commitment call and its mutable bank transition

The bank/slot parameters define sixteen ordinary Clean components. A row has no padding: its
HostCall pull accounts for one actual instruction. PublicValues pushes preserve the original
instruction checks while the separate state channel carries the mutable bank history.
-/

namespace SP1Clean.HostCommitChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
theorem bound_fits (p : ℕ) (deferred : Bool) : bound p deferred < 2 ^ 64 := by
  cases deferred <;> simp only [bound, Bool.false_eq_true, ↓reduceIte, min_lt_iff]
  all_goals norm_num

def main (deferred : Bool) (slot : Fin 8) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.call.code, const (codeWord deferred))
  assertion (Gadgets.Equality.circuit Word) (input.call.arg1, const (slotWord slot))
  assertion (Gadgets.Equality.circuit Word) (input.call.result, const (codeWord deferred))
  assertion (Gadgets.Equality.circuit Word) (input.call.length, const (0 : Word (ZMod p)))
  let _ ← ClockOrder.circuit input.clock
  let _ ← BoundedWord.circuit (bound p deferred) (bound_fits p deferred) ⟨input.call.arg2, input.comparison⟩
  assertion U16toU8OperationSafe.circuit ⟨input.call.arg2, input.bytes, 1⟩
  HostCallChip.channel.pull input.call
  (stateChannel deferred).pull input.previous
  (stateChannel deferred).push (input.next slot)
  -- A `match` rather than `if deferred`: see `HostHintLengthChip.main`.
  match deferred with
  | true =>
    publicValuesChannel.push ⟨147, 1⟩
    publicValuesChannel.push ⟨Expression.const ((72 + slot.val : ℕ) : ZMod p),
      input.call.arg2[0] + input.call.arg2[1] * 65536⟩
  | false =>
    publicValuesChannel.push ⟨145, 1⟩
    forEach (Vector.ofFn (fun i : Fin 4 => i)) fun i =>
      publicValuesChannel.push
        ⟨Expression.const ((32 + 4 * slot.val + i.val : ℕ) : ZMod p), (input.digest (Expression.const (256 : ZMod p)⁻¹))[i]⟩

instance elaborated (deferred : Bool) (slot : Fin 8) :
    ElaboratedCircuit (ZMod p) Inputs unit (main deferred slot) := by
  cases deferred <;> elaborate_circuit

end SP1Clean.HostCommitChip
