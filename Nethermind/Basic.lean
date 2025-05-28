import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Sp1

abbrev BabyBearPrime : ℕ := 2013265921

macro "prime_proof" : term =>
  if System.Platform.isOSX then `(sorry) else `(by norm_num)

lemma prime_BabyBearPrime : Nat.Prime BabyBearPrime := prime_proof

abbrev BabyBear : Type := Fin BabyBearPrime

instance : NeZero BabyBearPrime := by constructor; decide

instance : NoZeroDivisors BabyBear := by
  have : IsDomain (ZMod BabyBearPrime) := ZMod.instIsDomain (hp := ⟨prime_BabyBearPrime⟩)
  simp [ZMod] at this
  infer_instance

lemma fin_val_simp {n : ℕ} (Hlt : n < BabyBearPrime) :
  (@Fin.val Sp1.BabyBearPrime (@OfNat.ofNat.{0} Sp1.BabyBear n (@Fin.instOfNat Sp1.BabyBearPrime Sp1.instNeZeroNatBabyBearPrime n))) = n := by
  simp [BabyBearPrime, OfNat.ofNat] at *; assumption

syntax "PROOF" : term
macro_rules | `(PROOF) => `(sorry)

end Sp1
