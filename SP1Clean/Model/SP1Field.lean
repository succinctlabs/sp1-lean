import Mathlib.Tactic.NormNum.Prime

/-! # SP1's pinned base field

The chip and grounding layers stay generic over a sufficiently large prime field.  Exact SP1 Core
relations, generated-trace conformance, and eventual verifier adapters all instantiate that theory
at KoalaBear.  This module owns that single shared characteristic and its kernel-checked size facts;
higher layers must use `SP1Prime` directly rather than introduce local aliases.
-/

namespace SP1Clean

/-- The characteristic of SP1 v6.4.0's KoalaBear field, `2^31 - 2^24 + 1`. -/
abbrev SP1Prime : ℕ := 2130706433

/-- KoalaBear's characteristic is prime, proved without the test-only compiled decision procedure. -/
theorem sp1Prime_prime : SP1Prime.Prime := by
  norm_num [SP1Prime]

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
