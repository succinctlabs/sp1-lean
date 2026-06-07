import SP1Clean.Foundations.InteractionBus
import Mathlib.Data.ZMod.Basic

/-! # The field ⇒ ℤ balance bridge (item-5-proper, core)

The genuinely novel mathematical core of the Clean `BalancedInteractions` ↔ native
`isConsistentBalanced` reconciliation (item-5-proper, `docs/roadmap.md` §B5).

Clean's `BalancedInteractions` balances **field** multiplicities (`∑ mult = 0` in `ZMod p`) with only a
`length < ringChar` count guard; native `isConsistentBalanced` balances **ℤ** multiplicities
(`∑ signedVal = 0`). The two are *not* equivalent for arbitrary field mults — but for the **gated bus**,
where every multiplicity is `±is_real ∈ {0, ±1}`, the centered representatives `signedVal` lie in
`{0, ±1}`, so a per-key ℤ-sum that is `≡ 0 (mod p)` and bounded by the row count `< p` is forced to be
exactly `0`. That is this file's `isConsistentBalanced_of_intCast_zero`.

`hmod` here — `∀ k, (↑(multiplicitySum accesses k) : ZMod p) = 0` — is the *native restatement* of
Clean's field balance: `↑(signedVal x) = x` in `ZMod p`, so `↑(∑ signedVal) = ∑ mult = balanceOf`
(Clean). Translating Clean's per-`Array F`-message balance into this per-`LookupKey` form (via `toAccess`
+ `ZMod.val` injectivity), and assembling with the witness↔chipRows correspondence and `weakSoundness`,
are the remaining (large) parts of item-5-proper. -/

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
  -- |multiplicitySum| ≤ (filtered count) ≤ length < p
  have hbound : |multiplicitySum accesses k| ≤ ((filterKey accesses k).map multOf).length := by
    apply abs_sum_le_length_of_binary
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hbin a (List.mem_of_mem_filter ha)
  have hlen2 : ((filterKey accesses k).map multOf).length ≤ accesses.length := by
    rw [List.length_map, filterKey]; exact List.length_filter_le _ _
  have habs : |multiplicitySum accesses k| < (p : ℤ) := by
    have : ((filterKey accesses k).map multOf).length < p := by omega
    have hc : (((filterKey accesses k).map multOf).length : ℤ) < (p : ℤ) := by exact_mod_cast this
    omega
  -- p ∣ x and |x| < p ⇒ x = 0
  by_contra h
  exact absurd (Int.le_of_dvd (abs_pos.mpr h) ((dvd_abs _ _).mpr hdvd)) (by omega)

end SP1Clean.LookupAccessList
