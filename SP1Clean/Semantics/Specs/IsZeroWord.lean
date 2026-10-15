module

public import SP1Clean.Semantics.Specs.IsZero
public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.IsZeroWordOperation

/-! # Word zero-test contract

The semantic relation and its result interpretation are independent of the circuit.
The contract includes padding behavior and the shared auxiliary columns used by composition.
-/

@[expose] public section

namespace SP1Clean.IsZeroWordOperation

/-- Inputs for the native word-zero test. -/
structure Inputs (F : Type) where
  /-- The input word. -/
  a : Word F
  /-- The witnessed zero-test columns. -/
  cols : Circuits.Types.IsZeroWordOperation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- The activity flag is binary; the word limbs can be any field elements. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Each active limb carries its zero indicator and inverse. The two half indicators compose
those limb results, and the active word result combines both halves. Padding retains the binary
word result and half products, allowing composing chips to share auxiliary columns. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.cols.result = 0 ∨ input.cols.result = 1) ∧
  (input.cols.is_zero_first_half =
      input.cols.is_zero_limb_0.result * input.cols.is_zero_limb_1.result) ∧
  (input.cols.is_zero_second_half =
      input.cols.is_zero_limb_2.result * input.cols.is_zero_limb_3.result) ∧
  IsZeroOperation.Spec ⟨input.a[0], input.cols.is_zero_limb_0, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[1], input.cols.is_zero_limb_1, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[2], input.cols.is_zero_limb_2, input.is_real⟩ ∧
  IsZeroOperation.Spec ⟨input.a[3], input.cols.is_zero_limb_3, input.is_real⟩ ∧
  (input.is_real = 1 →
      input.cols.result = input.cols.is_zero_first_half * input.cols.is_zero_second_half)

/-- Combining four zero indicators gives the indicator that every limb is zero. -/
theorem result_collapse {a0 a1 a2 a3 z0 z1 z2 z3 first second result : ZMod p}
    (hz0 : z0 = if a0 = 0 then 1 else 0) (hz1 : z1 = if a1 = 0 then 1 else 0)
    (hz2 : z2 = if a2 = 0 then 1 else 0) (hz3 : z3 = if a3 = 0 then 1 else 0)
    (hfirst : first = z0 * z1) (hsecond : second = z2 * z3)
    (hresult : result = first * second) :
    result = if (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0) then 1 else 0 := by
  rw [hresult, hfirst, hsecond, hz0, hz1, hz2, hz3]
  by_cases h0 : a0 = 0 <;> by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;>
    by_cases h3 : a3 = 0 <;> simp [h0, h1, h2, h3]

/-- Semantic exposure: on a real row the `Spec` forces `result` to be the word zero-indicator. -/
theorem result_semantic {input : Inputs (ZMod p)} (h : Spec input) (hr : input.is_real = 1) :
    input.cols.result =
      if (input.a[0] = 0 ∧ input.a[1] = 0 ∧ input.a[2] = 0 ∧ input.a[3] = 0) then 1 else 0 := by
  obtain ⟨_, hf, hs, hS0, hS1, hS2, hS3, hg⟩ := h
  exact result_collapse (hS0 hr).1 (hS1 hr).1 (hS2 hr).1 (hS3 hr).1 hf hs (hg hr)

end SP1Clean.IsZeroWordOperation
