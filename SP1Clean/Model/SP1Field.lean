import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

/-! # SP1's pinned base field

The chip and grounding layers stay generic over a sufficiently large prime field.  Exact SP1 Core
relations, generated-trace conformance, and eventual verifier adapters all instantiate that theory
at KoalaBear.  This module owns that single shared characteristic and its kernel-checked size facts;
higher layers must use `SP1Prime` directly rather than introduce local aliases.
-/

namespace SP1Clean

/-- The characteristic of SP1 v6.4.0's KoalaBear field, `2^31 - 2^24 + 1`. -/
abbrev SP1Prime : ℕ := 2130706433

/-- KoalaBear's characteristic is prime, proved without the test-only compiled decision procedure.
A Lucas certificate (`lucas_primality`: witness `3`, `p - 1 = 2 ^ 24 * 127`, the two prime-cofactor
powers checked by `reduce_mod_char`) rather than `norm_num`'s trial-division certificate, whose proof
term for a 31-bit prime exceeds the kernel's recursion limit from Lean v4.33 on. -/
theorem sp1Prime_prime : SP1Prime.Prime := by
  have hp1 : SP1Prime - 1 = 2 ^ 24 * 127 := by norm_num [SP1Prime]
  refine lucas_primality SP1Prime 3 ?_ fun q hq hdvd => ?_
  · rw [hp1]; reduce_mod_char
  · rw [hp1] at hdvd ⊢
    have hq' : q = 2 ∨ q = 127 := by
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)
    rcases hq' with rfl | rfl <;> (reduce_mod_char; decide)

/-- Every 17-bit native arithmetic limb embeds canonically into KoalaBear. -/
theorem pow17_lt_sp1Prime : 2 ^ 17 < SP1Prime := by
  decide

/-- Every 24-bit Core clock limb embeds canonically into KoalaBear. -/
theorem pow24_lt_sp1Prime : 2 ^ 24 < SP1Prime := by
  decide

/-- The stronger native-ensemble interaction-capacity hypothesis holds at KoalaBear. -/
theorem pow25_lt_sp1Prime : 2 ^ 25 < SP1Prime := by
  decide

instance instFactSP1Prime : Fact SP1Prime.Prime := ⟨sp1Prime_prime⟩

instance instFactPow17LtSP1Prime : Fact (2 ^ 17 < SP1Prime) :=
  ⟨pow17_lt_sp1Prime⟩

instance instFactPow24LtSP1Prime : Fact (2 ^ 24 < SP1Prime) :=
  ⟨pow24_lt_sp1Prime⟩

instance instFactPow25LtSP1Prime : Fact (2 ^ 25 < SP1Prime) :=
  ⟨pow25_lt_sp1Prime⟩

instance instNeZeroSP1Prime : NeZero SP1Prime := ⟨by decide⟩

end SP1Clean
