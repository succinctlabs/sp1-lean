import SP1Clean.Faithful.CoreAIR
import SP1Clean.Extracted.InteractionModel
import SP1Clean.Model.InteractionProjection

set_option autoImplicit false

/-! # From the extracted AIR's ℕ-exact balance to a signed ℤ balance

The extracted Core AIR states its interaction balance as an equality of **canonical natural**
multiplicities: for each payload, the total sent equals the total received
(`CoreAIR.Current.Balance.Valid`). It is deliberately not a field-valued sum, because a modular
equality can wrap at the characteristic and would not recover an execution multiset.

The native Clean side speaks a different dialect: a bus is balanced when a **signed ℤ** sum over
each key is zero (`LookupAccessList.multiplicitySum`), with sends positive and receives negative,
and the sign comes from `signedVal` — the *centered* representative in `(-p/2, p/2]`, not from
`ZMod.val`.

This file is the arithmetic step between them, and the one place where the gap between those two
representatives has to be paid for.

## The premise that cannot be dropped

`ZMod.val` and `signedVal` agree only below half the characteristic. A multiplicity above `p/2` has
`signedVal m = m.val - p`, so a payload whose sent and received `val`s agree can still have a
nonzero signed sum. `SmallMultiplicities` is therefore a genuine hypothesis, not bookkeeping: it is
the trace/multiplicity bound the `Balance.Valid` docstring already says the interaction-argument
extractor must supply alongside the equality. For SP1's own traces it is amply true — chip
multiplicities are `±is_real`, so `0` or `1`, and provider multiplicities are occurrence counts far
below `p/2` — but it is true of the traces, not of the relation, so it travels as a premise.

## Scope

This proves the payload-indexed statement: under the extracted balance and the multiplicity bound,
every payload's signed multiplicity sum is zero. Turning that into
`LookupAccessList.multiplicitySum … k = 0` for a projected *key* additionally needs the projection
`payload ↦ key` to be injective — true, since each payload constructor lands on its own bus name and
`ZMod.val` determines the element — and is left for the file that consumes it, together with the
per-table access permutations of `Transport/Table.lean`. See `docs/roadmap.md`.
-/

namespace SP1Clean.Composition

open SP1Clean.CoreAIR.Current
open SP1Clean.Extracted (Dir AirInteraction)
open SP1Clean (signedVal signedVal_neg)

variable {p : ℕ} [Fact p.Prime]

/-- **The multiplicity bound.** Every interaction's multiplicity lies below half the
characteristic, so its centered representative is its `ZMod.val`. -/
def SmallMultiplicities (all : List (Extracted.Interaction (ZMod p))) : Prop :=
  ∀ i ∈ all, 2 * i.mult.val ≤ p

/-- The signed ℤ multiplicity of one extracted interaction, in the native dialect: sends positive,
receives negative, through the centered representative. -/
def signedMult (i : Extracted.Interaction (ZMod p)) : ℤ :=
  signedVal (i.dir.sign i.mult)

/-- **The signed multiplicity sum for one payload** — the ℤ-valued quantity the native bus
balance is stated in terms of. -/
def signedSum (all : List (Extracted.Interaction (ZMod p))) (payload : AirInteraction (ZMod p)) : ℤ :=
  ((all.filter fun i => i.payload = payload).map signedMult).sum

omit [Fact p.Prime] in
@[simp] theorem signedSum_nil (payload : AirInteraction (ZMod p)) :
    signedSum ([] : List (Extracted.Interaction (ZMod p))) payload = 0 := rfl

omit [Fact p.Prime] in
theorem signedSum_cons (i : Extracted.Interaction (ZMod p)) (rest : List (Extracted.Interaction (ZMod p)))
    (payload : AirInteraction (ZMod p)) :
    signedSum (i :: rest) payload =
      (if i.payload = payload then signedMult i else 0) + signedSum rest payload := by
  simp only [signedSum, List.filter_cons]
  by_cases h : i.payload = payload <;> simp [h]

omit [Fact p.Prime] in
theorem sentCount_cons (i : Extracted.Interaction (ZMod p)) (rest : List (Extracted.Interaction (ZMod p)))
    (payload : AirInteraction (ZMod p)) :
    Balance.sentCount Balance.Scope.local (i :: rest) payload =
      (if Balance.directionScope i.dir = Balance.Scope.local ∧ i.payload = payload ∧
          (i.dir = .send ∨ i.dir = .sendGlobal) then i.mult.val else 0) +
        Balance.sentCount Balance.Scope.local rest payload := by
  simp only [Balance.sentCount, List.filter_cons]
  by_cases h : Balance.directionScope i.dir = Balance.Scope.local ∧ i.payload = payload ∧
      (i.dir = .send ∨ i.dir = .sendGlobal) <;> simp [h]

omit [Fact p.Prime] in
theorem receivedCount_cons (i : Extracted.Interaction (ZMod p)) (rest : List (Extracted.Interaction (ZMod p)))
    (payload : AirInteraction (ZMod p)) :
    Balance.receivedCount Balance.Scope.local (i :: rest) payload =
      (if Balance.directionScope i.dir = Balance.Scope.local ∧ i.payload = payload ∧
          (i.dir = .receive ∨ i.dir = .receiveGlobal) then i.mult.val else 0) +
        Balance.receivedCount Balance.Scope.local rest payload := by
  simp only [Balance.receivedCount, List.filter_cons]
  by_cases h : Balance.directionScope i.dir = Balance.Scope.local ∧ i.payload = payload ∧
      (i.dir = .receive ∨ i.dir = .receiveGlobal) <;> simp [h]

omit [Fact p.Prime] in
/-- Below half the characteristic the centered representative *is* `ZMod.val`. -/
theorem signedVal_of_small {x : ZMod p} (h : 2 * x.val ≤ p) : signedVal x = (x.val : ℤ) := by
  simp only [signedVal, if_pos h]

/--
**The signed sum is sent minus received.**

One induction, four cases per step: the interaction either carries this payload or not, and — since
the extracted balance rejects global-scope interactions — its direction is either `send`, where the
signed multiplicity is `+val`, or `receive`, where `signedVal (-mult) = -signedVal mult = -val`.
The multiplicity bound is what licenses that last equality; without it the two representatives part
company above `p / 2`.
-/
theorem signedSum_eq_sent_sub_received (all : List (Extracted.Interaction (ZMod p)))
    (hp : 2 < p)
    (isLocal : ∀ i ∈ all, Balance.directionScope i.dir = Balance.Scope.local)
    (small : SmallMultiplicities all) (payload : AirInteraction (ZMod p)) :
    signedSum all payload =
      (Balance.sentCount Balance.Scope.local all payload : ℤ) -
        (Balance.receivedCount Balance.Scope.local all payload : ℤ) := by
  induction all with
  | nil => simp [Balance.sentCount, Balance.receivedCount]
  | cons i rest ih =>
    have hlocal : Balance.directionScope i.dir = Balance.Scope.local := isLocal i List.mem_cons_self
    have hsmall : 2 * i.mult.val ≤ p := small i List.mem_cons_self
    have ihr := ih (fun j hj => isLocal j (List.mem_cons_of_mem _ hj))
      (fun j hj => small j (List.mem_cons_of_mem _ hj))
    rw [signedSum_cons, sentCount_cons, receivedCount_cons, ihr]
    -- The direction is `send` or `receive`; the two global constructors are excluded by scope.
    have hdir : i.dir = Dir.send ∨ i.dir = Dir.receive := by
      cases hd : i.dir with
      | send => exact Or.inl rfl
      | receive => exact Or.inr rfl
      | sendGlobal => rw [hd] at hlocal; exact absurd hlocal (by decide)
      | receiveGlobal => rw [hd] at hlocal; exact absurd hlocal (by decide)
    by_cases hpay : i.payload = payload
    · rcases hdir with hd | hd
      · have hval : signedMult i = (i.mult.val : ℤ) := by
          simp only [signedMult, hd, Dir.sign]
          exact signedVal_of_small hsmall
        rw [if_pos hpay, hval, if_pos ⟨hlocal, hpay, Or.inl hd⟩,
          if_neg (by rintro ⟨-, -, h | h⟩ <;> exact absurd (hd.symm.trans h) (by decide))]
        push_cast
        ring
      · have hval : signedMult i = -(i.mult.val : ℤ) := by
          simp only [signedMult, hd, Dir.sign]
          rw [signedVal_neg hp, signedVal_of_small hsmall]
        rw [if_pos hpay, hval,
          if_neg (by rintro ⟨-, -, h | h⟩ <;> exact absurd (hd.symm.trans h) (by decide)),
          if_pos ⟨hlocal, hpay, Or.inl hd⟩]
        push_cast
        ring
    · rw [if_neg hpay,
        if_neg (by rintro ⟨-, h, -⟩; exact hpay h),
        if_neg (by rintro ⟨-, h, -⟩; exact hpay h)]
      push_cast
      ring

/--
**The payload-indexed balance transport.** Under the extracted AIR's own ℕ-exact balance and the
multiplicity bound, every payload's signed ℤ multiplicity sum vanishes — the shape the native
Clean bus balance is stated in.
-/
theorem signedSum_eq_zero (all : List (Extracted.Interaction (ZMod p))) (hp : 2 < p)
    (valid : Balance.Valid all) (small : SmallMultiplicities all)
    (payload : AirInteraction (ZMod p)) :
    signedSum all payload = 0 := by
  rw [signedSum_eq_sent_sub_received all hp valid.1 small payload, valid.2 payload, sub_self]

end SP1Clean.Composition
