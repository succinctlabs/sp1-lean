import SP1Foundations.Misc

/-!
# KoalaBear field setup and bridges to a generic prime field

This file plays two roles:

1. **Concrete field instances on `Fin KB`** (`namespace KoalaBear`): primality,
   `Field`, `NoZeroDivisors`, and a block of high-priority arithmetic instances
   that are perf-critical (see `docs/PERF_PATTERNS.md`).
2. **KB-specific bridges** (free-floating lemmas below the namespace): `rfl`-only
   facts like `(2130673921 : Fin KB) = 65536⁻¹` that translate the literal
   inverse-of-`2^k` values that the SP1 constraint compiler emits into
   `Field`-generic forms (`(2^k : F)⁻¹`). These are inherently KB-specific
   because the literal value is the modular inverse computed in `Fin KB`. They
   are the "instantiation-time bridge" — generic operation lemmas (Phase 3 of
   `docs/FIELD_GENERIC.md`) state their RHS in terms of `(2^k : F)⁻¹` so the
   only KB-coupling is whether the simp set includes the matching bridge.

A second concrete field (e.g. BabyBear) would need its own copies of these
bridges with its own literal values; the constraint compiler would emit a
different literal for `(2^16)⁻¹` mod that prime. See Phase 5 of
`docs/FIELD_GENERIC.md` for the BabyBear instantiation recipe.
-/

notation "KB" => 2130706433
@[simp] lemma BB_eq : KB = 2130706433 := rfl

/-- `Fin n`-level mod equals zero iff the underlying `Nat` mod does. Generic over any
`Fin n`; the only dependence was on `(m : Fin n).val = m.val`. Useful because the
statement naturally arises when bridging between bitvector and modular views. -/
lemma Fin.val_mod_eq_zero_iff {n : ℕ} [NeZero n] (x m : Fin n) :
    x.val % m.val = 0 ↔ x % m = 0 := by
  rw [← Fin.val_inj]; simp [Fin.mod_val]

/-- Literal-compatible variant of `Fin.val_mod_eq_zero_iff`: takes the modulus as a `ℕ`
literal (rather than `m.val` for some `m : Fin n`). The Nat-literal form of `m` on the
LHS is what SP1 chip proofs actually see (e.g. `Main[i].val % 4 = 0`), so this is the
version that fires in `simp` calls. -/
lemma Fin.val_mod_eq_zero_iff_of_lt {n : ℕ} [NeZero n] {x : Fin n} {m : ℕ} (hm : m < n) :
    x.val % m = 0 ↔ x % (Fin.ofNat n m) = 0 := by
  conv_lhs => rw [show m = (Fin.ofNat n m).val from (Nat.mod_eq_of_lt hm).symm]
  exact Fin.val_mod_eq_zero_iff x (Fin.ofNat n m)

/-! ### Ad-hoc `LT` and `Mod` instances on `ZMod p`

Mathlib intentionally omits `LT (ZMod p)` and `Mod (ZMod p)` because `ZMod 0 = ℤ`
and `ZMod (n+1) = Fin (n+1)` have different ordering semantics. With `[NeZero p]`
we are in the `Fin (n+1)` case, where `.val`-level `Nat`-comparison and modulo are
the natural choices. These let the field-genericity work (sub-phase B) reuse
`<` / `%` syntax in `toProp` / `toStateProp` without rephrasing to `.val`-form
(which empirically caused chip proofs to time out). At `p := KB`, `ZMod KB = Fin KB`
definitionally and these instances agree with `Fin.instLT` / `Fin.instMod`. -/

namespace ZMod
instance instLT (p : ℕ) [NeZero p] : LT (ZMod p) where
  lt x y := x.val < y.val
instance instMod (p : ℕ) [NeZero p] : Mod (ZMod p) where
  mod x y := ((x.val % y.val : ℕ) : ZMod p)
end ZMod

namespace KoalaBear

-- dt: Need `#eval`-level `native_decide` strength to make this work on all OS
set_option linter.style.nativeDecide false in
lemma prime_KoalaBearPrime : Nat.Prime KB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime KB) := ⟨prime_KoalaBearPrime⟩
instance : NeZero KB := by constructor; decide

-- dt: Wouldn't need this if `ZMod` was the fundamental object for us.
instance : Field (Fin KB) := ZMod.instField KB
instance : NoZeroDivisors (Fin 2130706433) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

-- High-priority direct instances for Fin KB arithmetic. Without these, Lean's
-- typeclass synth considers 5-9 candidates per Add/Mul/Sub/OfNat query (via
-- AddZero.toAdd, Lean.Grind.Semiring.toAdd, AddSemigroup.toAdd, etc.). The
-- constraints files have thousands of Fin KB arithmetic ops, so this matters —
-- initial profile showed 779s cumulative typeclass inference in ShiftRight.
@[instance 10000] instance instAdd : Add (Fin KB) := Fin.instAdd
@[instance 10000] instance instMul : Mul (Fin KB) := Fin.instMul
@[instance 10000] instance instSub : Sub (Fin KB) := Fin.instSub
@[instance 10000] instance instNeg : Neg (Fin KB) := inferInstance
@[instance 10000] instance instZero : Zero (Fin KB) := inferInstance
@[instance 10000] instance instOne : One (Fin KB) := inferInstance
@[instance 10000] instance instOfNat (n : Nat) : OfNat (Fin KB) n := Fin.instOfNat
@[instance 10000] instance instHAdd : HAdd (Fin KB) (Fin KB) (Fin KB) := ⟨fun a b => a + b⟩
@[instance 10000] instance instHMul : HMul (Fin KB) (Fin KB) (Fin KB) := ⟨fun a b => a * b⟩
@[instance 10000] instance instHSub : HSub (Fin KB) (Fin KB) (Fin KB) := ⟨fun a b => a - b⟩

end KoalaBear

/-! ### Generic field helpers (not KB-specific) -/

@[aesop safe forward]
lemma mul_diff_one_neq {α : Type*} [Field α] {a b c : α} :
    a * (b - c) = 1 → b ≠ c := by aesop

/-! ### KB-specific simp lemmas operating on the symbolic `(N : Fin KB)⁻¹` form

The constraint compiler now emits inverses symbolically (e.g. `(65536 : Fin KB)⁻¹`
instead of the literal `2130673921`). These lemmas help simp/omega/norm_num
reduce expressions involving those symbolic inverses. The earlier
literal-side bridges (`inv_*BB_eq[']`, `shiftl_*BB_eq_one`, etc.) were
removed when sub-phase B.2 landed — see `docs/FIELD_GENERIC.md`. Naming
convention: `<op>_<N>BB` where `BB` is short for "BabyBear-class small prime"
(historical misnomer kept in place; KB is KoalaBear, not BabyBear).
-/

-- Symbolic↔literal Fin KB bridges, with literal on the LHS (so `← `-rewrites
-- normalize symbolic `(N : Fin KB)⁻¹` back to its precomputed Fin KB literal
-- — needed for omega/Fin-arithmetic proofs that expect ground constants).
-- NOT `@[simp]`: they're invoked explicitly in proofs that need omega to see
-- concrete numbers, typically via `simp only [← inv_*BB_eq'] at h ...`.
lemma inv_4BB_eq' : (1598029825 : Fin KB) = ((4 : Fin KB)⁻¹) := rfl
lemma inv_8BB_eq' : (1864368129 : Fin KB) = ((8 : Fin KB)⁻¹) := rfl
lemma inv_256BB_eq' : (2122383361 : Fin KB) = ((256 : Fin KB)⁻¹) := rfl
lemma inv_65536BB_eq' : (2130673921 : Fin KB) = ((65536 : Fin KB)⁻¹) := rfl

@[simp] lemma mul_inv_16BB_eq_one_iff : x * (65536 : Fin KB)⁻¹ = 1 ↔ x = 65536 := by
  rw [mul_inv_eq_one₀ (by trivial)]

@[simp] lemma inv_16BB_zero_or_one {x : Fin KB} : x * 65536⁻¹ = 0 ∨ x * 65536⁻¹ = 1 ↔ x = 0 ∨ x = 65536
  := by aesop

-- Literal-side @[simp] iff bridges. These were originally planned for
-- deletion when sub-phase B.2 landed, but several chip proofs (Sub*, Branch,
-- LoadByte) rely on omega's ability to reason about a chain of
-- `* (literal : Fin KB)` operations. Without these, simp leaves the chain
-- in `* 65536⁻¹` form and omega gives up. We keep them as `@[simp]`,
-- preceded by an explicit `← inv_*BB_eq'` rewrite in the proof, so the
-- literal form is available exactly where it's needed.
@[simp] lemma inv_mul_2BB_eq_iff' : x * (1598029825 : Fin KB) = 1 ↔ x = 4 := by
  rw [show (1598029825 : Fin KB) = (4 : Fin KB)⁻¹ from rfl, mul_inv_eq_one₀ (by decide)]
@[simp] lemma inv_mul_3BB_eq_iff' : x * (1864368129 : Fin KB) = 1 ↔ x = 8 := by
  rw [show (1864368129 : Fin KB) = (8 : Fin KB)⁻¹ from rfl, mul_inv_eq_one₀ (by decide)]
@[simp] lemma inv_mul_8BB_eq_iff' : x * (2122383361 : Fin KB) = 1 ↔ x = 256 := by
  rw [show (2122383361 : Fin KB) = (256 : Fin KB)⁻¹ from rfl, mul_inv_eq_one₀ (by decide)]
@[simp] lemma inv_mul_16BB_eq_iff' : x * (2130673921 : Fin KB) = 1 ↔ x = 65536 := by
  rw [show (2130673921 : Fin KB) = (65536 : Fin KB)⁻¹ from rfl, mul_inv_eq_one₀ (by decide)]

/-! ### Integer helpers (not field-related; lives here for historical reasons) -/

namespace Int

lemma abs_cases {a : ℤ} : abs a = if 0 ≤ a then a else -a := by
  unfold abs; rw [Int.max_def]; omega

lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  · simp_all
  · by_cases 0 < a
    · rw [Int.sign_eq_one_of_pos (by omega)]; omega
    · rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

lemma split_nzp (a : ℤ) (P : Prop) :
  (a < 0 → P) → (a = 0 → P) → (0 < a → P) → P := by
  intro an az ap
  by_cases a = 0
  · apply az (by assumption)
  · by_cases 0 < a
    · apply ap (by omega)
    · apply an (by omega)

end Int
