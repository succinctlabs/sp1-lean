import SP1Clean.Proofs.Chips.HostCommitChip.Formal
import SP1Clean.Model.Core.HostExecutionLaws

/-! # Native commitment rows implement mutable host slots

Decode the bank carried by the state ledger and compare with the independent host interpreter.
The complete host effect changes only the selected slot; previously committed values may differ
from the new one. The state and instruction ledgers still need assembly into the mixed machine.
-/

namespace SP1Clean.HostCommitChip

open SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def State.decode (state : State (ZMod p)) : Vector (BitVec 32) 8 :=
  state.values.map fun word => (Word.toBitVec64 word).setWidth 32

def State.apply (state : State (ZMod p)) (deferred : Bool) (host : HostState) : HostState :=
  if deferred then { host with deferred := state.decode } else { host with committed := state.decode }

private theorem slot_bound (slot : Fin 8) : Word.isU64 (slotWord (R := ZMod p) slot) := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  apply Word.isU64_of_cases <;> simp only [slotWord, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]
  · rw [ZMod.val_natCast_of_lt (by have := slot.isLt; omega)]
    exact lt_trans slot.isLt (by norm_num)
  all_goals norm_num

private theorem slot_value (slot : Fin 8) : Word.toNat (slotWord (R := ZMod p) slot) = slot.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  simp only [Word.toNat, slotWord, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero, zero_mul, add_zero]
  rw [ZMod.val_natCast_of_lt (by have := slot.isLt; omega)]

private theorem call_bounds (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (valid : CallSpec deferred slot call) :
    (Word.toBitVec64 call.arg1).toNat = slot.val ∧
      (Word.toBitVec64 call.arg2).toNat < bound p deferred := by
  constructor
  · rw [valid.2.1, Word.toBitVec64_toNat (slot_bound slot), slot_value]
  · rw [Word.toBitVec64_toNat valid.2.2.2.2.1]
    exact valid.2.2.2.2.2

private theorem code_value (deferred : Bool) :
    Word.toBitVec64 (codeWord (R := ZMod p) deferred) =
      (if deferred then SyscallKind.commitDeferred else .commit).code := by
  have small (n : ℕ) (bound : n < 2 ^ 17) : (n : ZMod p).val = n :=
    ZMod.val_natCast_of_lt (lt_trans bound (Fact.out (p := 2 ^ 17 < p)))
  have sixteen : (16 : ZMod p).val = 16 := small 16 (by decide)
  have twentySix : (26 : ZMod p).val = 26 := small 26 (by decide)
  cases deferred <;> simp [codeWord, Word.toBitVec64, Word.toNat, sixteen, twentySix, SyscallKind.code]

/-- Update the actual host bank; the call does not choose the values of untouched slots. -/
def execution (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (host : HostState) : HostExecution :=
  ⟨if deferred then .commitDeferred else .commit, Word.toBitVec64 call.arg1,
    Word.toBitVec64 call.arg2, Word.toBitVec64 call.result,
    ⟨if deferred then { host with deferred := host.deferred.set slot ((Word.toBitVec64 call.arg2).setWidth 32) }
      else { host with committed := host.committed.set slot ((Word.toBitVec64 call.arg2).setWidth 32) }, none⟩⟩

private theorem executeKind_of_callSpec (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (valid : CallSpec deferred slot call) (host : HostState) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext) :
    host.executeKind policy context (if deferred then .commitDeferred else .commit)
      (Word.toBitVec64 call.arg1) (Word.toBitVec64 call.arg2) =
        some (execution deferred slot call host).effect := by
  have bounds := call_bounds deferred slot call valid
  cases deferred
  · simp only [bound, Bool.false_eq_true, ↓reduceIte] at bounds
    simp only [HostState.executeKind, bounds.1, dif_pos slot.isLt, if_pos bounds.2, execution,
      Bool.false_eq_true, ↓reduceIte]
  · simp only [bound, ↓reduceIte, lt_min_iff] at bounds
    simp only [HostState.executeKind, bounds.1, dif_pos slot.isLt, characteristic, if_pos bounds.2,
      execution, ↓reduceIte]

/-- The constrained call and actual register observations determine dispatch on any running
host, preserving its other slots. Final bank-ledger agreement is a separate boundary claim. -/
theorem run_of_callSpec (deferred : Bool) (slot : Fin 8) (call : HostCallChip.Message (ZMod p))
    (valid : CallSpec deferred slot call) (host : HostState) (running : host.exitCode = none)
    (policy : HostPolicy) (characteristic : policy.characteristic = p) (context : HostReadContext)
    (code : context.register 5 = some (Word.toBitVec64 call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 call.arg2)) :
    host.run policy context = some (execution deferred slot call host) := by
  apply (host.run_eq_some_iff policy context _).mpr
  refine ⟨running, ?_, arg1, arg2, ?_, executeKind_of_callSpec deferred slot call valid host policy characteristic context⟩
  · simpa only [valid.1, code_value, execution] using code
  · rw [show (execution deferred slot call host).result = Word.toBitVec64 call.result from rfl,
      valid.2.2.1, code_value]
    cases deferred <;> rfl

omit [Fact (2 ^ 25 < p)] in
/-- The decoded state changes exactly the selected 32-bit slot. -/
theorem next_decode (input : Inputs (ZMod p)) (slot : Fin 8) :
    (input.next slot).decode = input.previous.decode.set slot (Word.toBitVec64 input.call.arg2 |>.setWidth 32) := by
  simp only [State.decode, Inputs.next, Vector.map_set]

/-- One native commitment transition is exactly the independent host interpreter's complete effect. -/
theorem executeKind_of_spec (deferred : Bool) (slot : Fin 8) (input : Inputs (ZMod p))
    (valid : Spec deferred slot input) (host : HostState) (policy : HostPolicy)
    (characteristic : policy.characteristic = p) (context : HostReadContext) :
    (input.previous.apply deferred host).executeKind policy context
      (if deferred then .commitDeferred else .commit)
      (Word.toBitVec64 input.call.arg1) (Word.toBitVec64 input.call.arg2) =
      some ⟨(input.next slot).apply deferred host, none⟩ := by
  have bounds := call_bounds deferred slot input.call valid.1
  cases deferred
  · simp only [bound, Bool.false_eq_true, ↓reduceIte] at bounds
    simp only [State.apply, Bool.false_eq_true, ↓reduceIte, HostState.executeKind, bounds.1,
      dif_pos slot.isLt, if_pos bounds.2, next_decode]
  · simp only [bound, ↓reduceIte, lt_min_iff] at bounds
    simp only [State.apply, ↓reduceIte, HostState.executeKind, bounds.1,
      dif_pos slot.isLt, characteristic, if_pos bounds.2, next_decode]

end SP1Clean.HostCommitChip
