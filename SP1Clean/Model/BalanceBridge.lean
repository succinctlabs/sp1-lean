import SP1Clean.Model.InteractionBus
import SP1Clean.Model.InteractionProjection
import Clean.Air.Balance
import Mathlib.Data.ZMod.Basic

/-! # The field ⇒ ℤ balance bridge

The mathematical core of the Clean `BalancedInteractions` ↔ native `isConsistentBalanced` reconciliation.

Clean's `BalancedInteractions` balances **field** multiplicities (`∑ mult = 0` in `ZMod p`) with only a
`length < ringChar` count guard; native `isConsistentBalanced` balances **ℤ** multiplicities
(`∑ signedVal = 0`). The two are *not* equivalent for arbitrary field mults — but for the **gated bus**,
where every multiplicity is `±is_real ∈ {0, ±1}`, the centered representatives `signedVal` lie in
`{0, ±1}`, so a per-key ℤ-sum that is `≡ 0 (mod p)` and bounded by the row count `< p` is forced to be
exactly `0`. That is this file's `isConsistentBalanced_of_intCast_zero`.

`hmod` — `∀ k, (↑(multiplicitySum accesses k) : ZMod p) = 0` — is the *native restatement* of
Clean's field balance: `↑(signedVal x) = x` in `ZMod p` (`intCast_signedVal`), so
`↑(∑ signedVal) = ∑ mult = balanceOf` (Clean). The translation of Clean's per-`Array F`-message balance
into this per-`LookupKey` form is also proven here: same-channel interaction keys separate exactly on
the message (`ZMod.val` + `Array.toList` injectivity), so each `LookupKey`'s ℤ-sum casts to one Clean
`balanceOf` (`intCast_multiplicitySum_map_toAccess`), and the whole adapter — Clean
`BalancedInteractions` ⇒ native `isConsistentBalanced` over any access list that permutes to the
`Interaction.toAccess`-image with `{-1, 0, 1}` multiplicities — is
`isConsistentBalanced_of_balancedInteractions` (the roadmap-W1a core). The remaining input — the
witness ↔ access-list correspondence itself — is the decode seam
(`Soundness/WitnessDecode.lean`). -/

namespace SP1Clean.LookupAccessList

/-- A list of integers each in `{-1, 0, 1}` has `|sum| ≤ length`. -/
lemma abs_sum_le_length_of_binary (l : List ℤ) (h : ∀ x ∈ l, x = -1 ∨ x = 0 ∨ x = 1) :
    |l.sum| ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t IH =>
    have ha : |a| ≤ 1 := by rcases h a (by simp) with h' | h' | h' <;> simp [h']
    have hIH := IH (fun x hx => h x (List.mem_cons_of_mem a hx))
    have hab : |a + t.sum| ≤ |a| + |t.sum| := abs_add_le a t.sum
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- **Field balance ⇒ ℤ balance, for a binary bus.** If every multiplicity is in `{-1, 0, 1}`, there are
fewer than `p` accesses, and every key's signed ℤ-sum is `≡ 0 (mod p)` (the native form of Clean's
field `BalancedInteractions`), then the bus is natively balanced (`isConsistentBalanced`, ℤ-sum `= 0`).
The bound `|∑| ≤ count < p` upgrades "`≡ 0 mod p`" to "`= 0`". -/
theorem isConsistentBalanced_of_intCast_zero {p : ℕ} [NeZero p]
    (accesses : LookupAccessList)
    (hlen : accesses.length < p)
    (hbin : ∀ a ∈ accesses, multOf a = -1 ∨ multOf a = 0 ∨ multOf a = 1)
    (hmod : ∀ k, ((multiplicitySum accesses k : ℤ) : ZMod p) = 0) :
    isConsistentBalanced accesses := by
  intro k
  have hdvd : (p : ℤ) ∣ multiplicitySum accesses k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (hmod k)
  have hbound : |multiplicitySum accesses k| ≤ ((filterKey accesses k).map multOf).length := by
    refine abs_sum_le_length_of_binary _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hbin a (List.mem_of_mem_filter ha)
  have hlen2 : ((filterKey accesses k).map multOf).length ≤ accesses.length := by
    rw [List.length_map, filterKey]; exact List.length_filter_le _ _
  have habs : |multiplicitySum accesses k| < (p : ℤ) := by omega
  exact Int.eq_zero_of_abs_lt_dvd hdvd habs

/-! ## The Clean → native translation (the `toAccess` adapter, roadmap W1a)

Clean's `BalancedInteractions` is per-`Array F`-message over evaluated `Interaction (ZMod p)`s; the
native `isConsistentBalanced` is per-`LookupKey` over the `ZMod.val`-projected `LookupAccess`es. For a
**single-channel** interaction list the two key spaces are in bijection — the kind and table name are
pinned by the channel, and `ZMod.val`/`Array.toList` injectivity makes the val-projected message
faithful — so each `LookupKey`'s ℤ-multiplicity-sum casts to exactly one Clean `balanceOf` (or to `0`,
for keys the list never touches). -/

section CleanTranslation

variable {p : ℕ} [Fact p.Prime]

/-- Casting an ℤ-list sum into `ZMod p` distributes over the list. -/
private lemma intCast_list_sum (l : List ℤ) :
    ((l.sum : ℤ) : ZMod p) = (l.map (fun x : ℤ => (x : ZMod p))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- At the key of an observed interaction, the native integer multiplicity sum casts back to
Clean's field-valued balance of that interaction's message.  This is the lossless algebraic core
shared by both directions of the balance bridge; no binary-multiplicity or count bound is needed. -/
theorem intCast_multiplicitySum_map_toAccess_eq_balanceOf
    (interactions : List (Interaction (ZMod p))) (channel : RawChannel (ZMod p))
    (h_channel : ∀ i ∈ interactions, i.channel = channel)
    (i₀ : Interaction (ZMod p)) (hi₀ : i₀ ∈ interactions) :
    ((multiplicitySum (interactions.map Interaction.toAccess)
      (keyOf (Interaction.toAccess i₀)) : ℤ) : ZMod p) =
      balanceOf interactions i₀.msg := by
  have h_pred : ∀ i ∈ interactions,
      decide (keyOf (Interaction.toAccess i) = keyOf (Interaction.toAccess i₀)) =
        decide (i.msg = i₀.msg) := by
    intro i hi
    rw [decide_eq_decide]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Array.toList_inj.mp (List.map_injective_iff.mpr (ZMod.val_injective p)
        (congrArg (fun t => t.2.2) h))
    · simp only [Interaction.toAccess, keyOf, h_channel i hi, h_channel i₀ hi₀, h]
  have h_filter :
      (interactions.map Interaction.toAccess).filter
          (fun a => keyOf a = keyOf (Interaction.toAccess i₀)) =
        (interactions.filter (fun i => i.msg = i₀.msg)).map Interaction.toAccess := by
    rw [List.filter_map]
    exact congrArg (List.map Interaction.toAccess) (List.filter_congr h_pred)
  calc
    ((multiplicitySum (interactions.map Interaction.toAccess)
        (keyOf (Interaction.toAccess i₀)) : ℤ) : ZMod p)
        = ((((interactions.filter (fun i => i.msg = i₀.msg)).map
            (fun i => signedVal i.mult)).sum : ℤ) : ZMod p) := by
          rw [multiplicitySum, filterKey, h_filter, List.map_map]
          rfl
    _ = ((interactions.filter (fun i => i.msg = i₀.msg)).map (fun i => i.mult)).sum := by
          rw [intCast_list_sum, List.map_map]
          exact congrArg List.sum (List.map_congr_left fun i _ => intCast_signedVal i.mult)
    _ = balanceOf interactions i₀.msg := rfl

/-- **Per-key cast-sum zero.** For a single-channel interaction list whose Clean per-message balance
vanishes, the `Interaction.toAccess`-image's ℤ-multiplicity-sum at *every* `LookupKey` is `≡ 0 (mod p)`
— the `hmod` input of `isConsistentBalanced_of_intCast_zero`. Keys of same-channel interactions
separate exactly on the message (`ZMod.val` + `Array.toList` injectivity), so a touched key's sum casts
to one `balanceOf`; an untouched key sums to `0` outright. -/
theorem intCast_multiplicitySum_map_toAccess
    (interactions : List (Interaction (ZMod p))) (channel : RawChannel (ZMod p))
    (h_channel : ∀ i ∈ interactions, i.channel = channel)
    (h_zero : ∀ msg : Array (ZMod p), balanceOf interactions msg = 0)
    (k : LookupKey) :
    ((multiplicitySum (interactions.map Interaction.toAccess) k : ℤ) : ZMod p) = 0 := by
  by_cases h_ex : ∃ i ∈ interactions, keyOf (Interaction.toAccess i) = k
  · obtain ⟨i₀, hi₀, hk₀⟩ := h_ex
    rw [← hk₀]
    exact (intCast_multiplicitySum_map_toAccess_eq_balanceOf interactions channel h_channel
      i₀ hi₀).trans (h_zero i₀.msg)
  · have h0 : multiplicitySum (interactions.map Interaction.toAccess) k = 0 := by
      refine multiplicitySum_eq_zero_of_keyOf_ne fun a ha hak => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact h_ex ⟨i, hi, hak⟩
    rw [h0, Int.cast_zero]

/-- **Clean field balance ⇒ native ℤ balance, through `toAccess` (the W1a adapter).** Any native
access list that (i) permutes to the `Interaction.toAccess`-image of a single-channel interaction list
satisfying Clean's `BalancedInteractions`, and (ii) carries only `{-1, 0, 1}` multiplicities (the gated
bus), is natively balanced. The count guard is Clean's own `length < ringChar (ZMod p) = p` (the
`ringChar = 0` disjunct is impossible at a prime); the per-key `mod p` sums are
`intCast_multiplicitySum_map_toAccess`; the upgrade to exact `0` is
`isConsistentBalanced_of_intCast_zero`. -/
theorem isConsistentBalanced_of_balancedInteractions
    (accesses : LookupAccessList)
    (interactions : List (Interaction (ZMod p))) (channel : RawChannel (ZMod p))
    (h_channel : ∀ i ∈ interactions, i.channel = channel)
    (h_perm : accesses.Perm (interactions.map Interaction.toAccess))
    (h_bal : BalancedInteractions interactions)
    (h_bin : ∀ a ∈ accesses, multOf a = -1 ∨ multOf a = 0 ∨ multOf a = 1) :
    isConsistentBalanced accesses := by
  refine isConsistentBalanced_of_intCast_zero (p := p) accesses ?_ h_bin ?_
  · rcases h_bal.1 with hlt | hchar
    · rw [h_perm.length_eq, List.length_map]; rwa [ZMod.ringChar_zmod_n] at hlt
    · rw [ZMod.ringChar_zmod_n] at hchar; exact absurd hchar (Fact.out (p := p.Prime)).ne_zero
  · intro k
    rw [multiplicitySum_perm _ _ h_perm k]
    exact intCast_multiplicitySum_map_toAccess interactions channel h_channel h_bal.2 k

/-- **Native ℤ balance ⇒ Clean field balance, through `toAccess`.**  Unlike the forward direction,
this implication needs no binary-multiplicity hypothesis: an integer sum which is literally zero
casts to zero in the field.  The explicit count premise is exactly Clean's non-overflow side
condition and is deliberately not inferred from balance. -/
theorem balancedInteractions_of_isConsistentBalanced
    (accesses : LookupAccessList)
    (interactions : List (Interaction (ZMod p))) (channel : RawChannel (ZMod p))
    (h_channel : ∀ i ∈ interactions, i.channel = channel)
    (h_perm : accesses.Perm (interactions.map Interaction.toAccess))
    (h_count : interactions.length < p)
    (h_bal : isConsistentBalanced accesses) :
    BalancedInteractions interactions := by
  constructor
  · left
    simpa only [ZMod.ringChar_zmod_n] using h_count
  · intro msg
    by_cases h_ex : ∃ i ∈ interactions, i.msg = msg
    · obtain ⟨i₀, hi₀, hmsg⟩ := h_ex
      rw [← hmsg, ← intCast_multiplicitySum_map_toAccess_eq_balanceOf interactions channel
        h_channel i₀ hi₀]
      rw [← multiplicitySum_perm accesses _ h_perm _]
      simpa only [Int.cast_zero] using congrArg (fun z : ℤ => (z : ZMod p))
        (h_bal (keyOf (Interaction.toAccess i₀)))
    · have h_filter : interactions.filter (fun i => i.msg = msg) = [] := by
        exact List.filter_eq_nil_iff.mpr fun i hi himsg => h_ex ⟨i, hi, by simpa using himsg⟩
      simp only [balanceOf, h_filter, List.map_nil, List.sum_nil]

end CleanTranslation

end SP1Clean.LookupAccessList
