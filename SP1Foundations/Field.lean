import SP1Foundations.Misc

/-!
# KoalaBear field setup and bridges to a generic prime field

This file plays two roles:

1. **Concrete field instances on `Fin KB`** (`namespace KoalaBear`): primality,
   `Field`, `NoZeroDivisors`, and a block of high-priority arithmetic instances
   that are perf-critical (see `docs/PROOF_PATTERNS.md`).
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
instance instLE (p : ℕ) [NeZero p] : LE (ZMod p) where
  le x y := x.val ≤ y.val
instance instMod (p : ℕ) [NeZero p] : Mod (ZMod p) where
  mod x y := ((x.val % y.val : ℕ) : ZMod p)
end ZMod

/-- `Opcode.ofNat` in the auto-gen `program` interactions reads the opcode
field as a `ℕ`. At `F := Fin n` and `F := ZMod p` the `.val` projection
provides this; the typeclass `CoeHead F ℕ` is the generic surface that
the `` cascade uses to lift readers with `program` clauses
(RTypeReader, ITypeReader, JTypeReader, ALUTypeReader). -/
instance Fin.coeHeadNat {n : ℕ} : CoeHead (Fin n) ℕ := ⟨Fin.val⟩
instance ZMod.coeHeadNat {p : ℕ} [NeZero p] : CoeHead (ZMod p) ℕ := ⟨ZMod.val⟩

/-- Reduces `CoeHead.coe (x : ZMod p)` to `x.val` so simp normalizes the
`Opcode.ofNat` argument inside `program`-clause auto-gen output to match
the iff RHS `Opcode.ofNat opcode.val` form. -/
@[simp] lemma coeHead_zmod_eq_val {p : ℕ} [NeZero p] (x : ZMod p) :
    @CoeHead.coe (ZMod p) ℕ _ x = x.val := rfl

/-- Reduces `CoeHead.coe (x : Fin n)` to `x.val` (sibling of
`coeHead_zmod_eq_val`). -/
@[simp] lemma coeHead_fin_eq_val {n : ℕ} (x : Fin n) :
    @CoeHead.coe (Fin n) ℕ _ x = x.val := rfl

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

/-! ### Polymorphic `.val` helpers over `ZMod p`

These let `` operation iff lemmas reduce `(N : ZMod p).val` to `N` for
the literal values that appear in our auto-gen constraint definitions
(`16` from byte-opcode `Range`, `32` for register-index bounds, `256` /
`65536` for U16/U8 boundaries). Under `[Fact (2 ^ 17 < p)]` (which decides
at `p := KB` and at any prime ≥ 2^17, including BabyBear), every literal
≤ 65536 satisfies the bound mathlib's `ZMod.val_natCast_of_lt` needs.

Naming: `val_<N>_zmod_p` to avoid collision with mathlib's `ZMod.val_*`
namespace conventions. -/

section Polymorphic

variable {p : ℕ} [hp : Fact (2 ^ 17 < p)]

@[simp] lemma val_2_zmod_p : (2 : ZMod p).val = 2 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (2 : ℕ) < p by omega)

@[simp] lemma val_4_zmod_p : (4 : ZMod p).val = 4 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (4 : ℕ) < p by omega)

@[simp] lemma val_8_zmod_p : (8 : ZMod p).val = 8 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (8 : ℕ) < p by omega)

@[simp] lemma val_16_zmod_p : (16 : ZMod p).val = 16 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

-- DivRem opcode values (15-28) needed for chip-level  proofs' opcode reductions.
@[simp] lemma val_15_zmod_p : (15 : ZMod p).val = 15 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (15 : ℕ) < p by omega)

@[simp] lemma val_17_zmod_p : (17 : ZMod p).val = 17 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (17 : ℕ) < p by omega)

@[simp] lemma val_18_zmod_p : (18 : ZMod p).val = 18 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (18 : ℕ) < p by omega)

@[simp] lemma val_25_zmod_p : (25 : ZMod p).val = 25 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (25 : ℕ) < p by omega)

@[simp] lemma val_26_zmod_p : (26 : ZMod p).val = 26 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (26 : ℕ) < p by omega)

@[simp] lemma val_27_zmod_p : (27 : ZMod p).val = 27 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (27 : ℕ) < p by omega)

@[simp] lemma val_28_zmod_p : (28 : ZMod p).val = 28 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (28 : ℕ) < p by omega)

@[simp] lemma val_32_zmod_p : (32 : ZMod p).val = 32 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (32 : ℕ) < p by omega)

@[simp] lemma val_256_zmod_p : (256 : ZMod p).val = 256 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (256 : ℕ) < p by omega)

@[simp] lemma val_64_zmod_p : (64 : ZMod p).val = 64 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (64 : ℕ) < p by omega)

@[simp] lemma val_128_zmod_p : (128 : ZMod p).val = 128 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (128 : ℕ) < p by omega)

@[simp] lemma val_512_zmod_p : (512 : ZMod p).val = 512 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (512 : ℕ) < p by omega)

@[simp] lemma val_1024_zmod_p : (1024 : ZMod p).val = 1024 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (1024 : ℕ) < p by omega)

@[simp] lemma val_2048_zmod_p : (2048 : ZMod p).val = 2048 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (2048 : ℕ) < p by omega)

@[simp] lemma val_4096_zmod_p : (4096 : ZMod p).val = 4096 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (4096 : ℕ) < p by omega)

@[simp] lemma val_8192_zmod_p : (8192 : ZMod p).val = 8192 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (8192 : ℕ) < p by omega)

@[simp] lemma val_16384_zmod_p : (16384 : ZMod p).val = 16384 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (16384 : ℕ) < p by omega)

@[simp] lemma val_32768_zmod_p : (32768 : ZMod p).val = 32768 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (32768 : ℕ) < p by omega)

@[simp] lemma val_65536_zmod_p : (65536 : ZMod p).val = 65536 := by
  have : 131072 < p := by have := hp.out; omega
  exact ZMod.val_natCast_of_lt (show (65536 : ℕ) < p by omega)

/-- Polymorphic non-zero bridge for `(64 : ZMod p)`. -/
lemma val_64_ne_zero : (64 : ZMod p) ≠ 0 := by
  have h : (64 : ZMod p).val = 64 := val_64_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge: `(65536 : ZMod p) ≠ 0` whenever `p > 65536`.
Used by bridge-coupled operation iff lemmas (`AddOperation`, `SubOperation`,
etc.) when `mul_inv_eq_one₀` needs the `(literal : ZMod p) ≠ 0` side
condition. -/
lemma val_65536_ne_zero : (65536 : ZMod p) ≠ 0 := by
  have h : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge for `(256 : ZMod p)`. -/
lemma val_256_ne_zero : (256 : ZMod p) ≠ 0 := by
  have h : (256 : ZMod p).val = 256 := val_256_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge for `(4 : ZMod p)`. -/
lemma val_4_ne_zero : (4 : ZMod p) ≠ 0 := by
  have h : (4 : ZMod p).val = 4 := val_4_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge for `(8 : ZMod p)`. -/
lemma val_8_ne_zero : (8 : ZMod p) ≠ 0 := by
  have h : (8 : ZMod p).val = 8 := val_8_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge for `(2 : ZMod p)`. -/
lemma val_2_ne_zero : (2 : ZMod p) ≠ 0 := by
  have h : (2 : ZMod p).val = 2 := val_2_zmod_p
  intro hz; rw [hz] at h; simp at h

/-- Polymorphic non-zero bridge for `(3 : ZMod p)`. Used in
`LtOperationUnsigned/Signed` `` proofs to discharge impossible
flag-sum combinations (sum = 3 case). -/
lemma val_3_ne_zero : (3 : ZMod p) ≠ 0 := by
  have h : (3 : ZMod p).val = 3 := by
    have hp : 2 ^ 17 < p := hp.out
    rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl]
    apply ZMod.val_natCast_of_lt
    omega
  intro hz; rw [hz] at h; simp at h

/-- The carry-binary clauses in the bridge-coupled op iff lemmas
(`AddOperation`, `SubOperation`, `Addw`, `Subw`, `AddrAdd`) have shape
`x * 65536⁻¹ = 1`; this rewrites it to `x = 65536`. The prime hypothesis
is needed for the `GroupWithZero` instance via `Field (ZMod p)`. -/
lemma mul_inv_65536_eq_one_iff [Fact (Nat.Prime p)] (x : ZMod p) :
    x * (65536 : ZMod p)⁻¹ = 1 ↔ x = 65536 := by
  rw [mul_inv_eq_one₀ val_65536_ne_zero]

/-- Used by AddrAdd/Branch-style ops where `(2^2)⁻¹` appears (PC alignment
carries). -/
lemma mul_inv_4_eq_one_iff [Fact (Nat.Prime p)] (x : ZMod p) :
    x * (4 : ZMod p)⁻¹ = 1 ↔ x = 4 := by
  rw [mul_inv_eq_one₀ val_4_ne_zero]

/-- Carry binarity in Add/Sub iff lemmas factors through this disjunction. -/
lemma inv_65536_zero_or_one [Fact (Nat.Prime p)] (x : ZMod p) :
    x * (65536 : ZMod p)⁻¹ = 0 ∨ x * (65536 : ZMod p)⁻¹ = 1 ↔
      x = 0 ∨ x = 65536 := by
  have h1 : (65536 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero val_65536_ne_zero
  rw [mul_inv_eq_one₀ val_65536_ne_zero, mul_eq_zero]
  aesop

/-- Carry binarity for `(4 : ZMod p)⁻¹`. -/
lemma inv_4_zero_or_one [Fact (Nat.Prime p)] (x : ZMod p) :
    x * (4 : ZMod p)⁻¹ = 0 ∨ x * (4 : ZMod p)⁻¹ = 1 ↔
      x = 0 ∨ x = 4 := by
  have h1 : (4 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero val_4_ne_zero
  rw [mul_inv_eq_one₀ val_4_ne_zero, mul_eq_zero]
  aesop

/-- Small-literal equality bridge for `ZMod p` under `[Fact (2^17 < p)]`.
Converts `(n : ZMod p) = (m : ZMod p)` to `n = m` (Nat-level) for any
`n, m < 2^17`. Used in the LtOperationUnsigned/Signed `` proofs to
handle impossible cases where multiple flag bits are 1 simultaneously. -/
lemma small_nat_eq_zmod {n m : ℕ} (hn : n < 2 ^ 17) (hm : m < 2 ^ 17) :
    ((n : ZMod p) = (m : ZMod p)) ↔ n = m := by
  have hp : 2 ^ 17 < p := hp.out
  haveI : NeZero p := ⟨by omega⟩
  constructor
  · intro h
    have hn' : (n : ZMod p).val = n := ZMod.val_natCast_of_lt (by omega)
    have hm' : (m : ZMod p).val = m := ZMod.val_natCast_of_lt (by omega)
    apply_fun ZMod.val at h
    omega
  · intro h; rw [h]

/-- ZMod p `% k = 0` ↔ `x.val % k = 0` (as naturals), given `0 < k < p`.
The project's `instMod (p : ℕ) [NeZero p] : Mod (ZMod p)` is defined as
`x % y := ((x.val % y.val : ℕ) : ZMod p)`. So `(x : ZMod p) % (k : ZMod p) = 0`
unfolds to `((x.val % k.val : ℕ) : ZMod p) = (0 : ZMod p)`, which (since
`x.val % k.val < k < p`) lifts to `x.val % k.val = 0` via `small_nat_eq_zmod`-
style cast injection. The PC-alignment `(pc : ZMod p) % 4 = 0` and analogous
checks in Branch / Jal / Jalr chip migrations consume this bridge. -/
lemma val_mod_eq_zero_iff_zmod_mod_eq_zero
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (x : ZMod p) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < p) :
    (x % ((k : ℕ) : ZMod p) = (0 : ZMod p)) ↔ x.val % k = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hk_val : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt hk_lt
  -- Unfold the project-defined `instMod`.
  change (((x.val % ((k : ℕ) : ZMod p).val : ℕ) : ZMod p) = (0 : ZMod p)) ↔ x.val % k = 0
  rw [hk_val]
  -- Bridge `((x.val % k : ℕ) : ZMod p) = 0` ↔ `x.val % k = 0` via cast injection.
  have h_lt : x.val % k < p := Nat.lt_of_lt_of_le (Nat.mod_lt _ hk_pos) hk_lt.le
  constructor
  · intro h
    have hv : ((x.val % k : ℕ) : ZMod p).val = x.val % k :=
      ZMod.val_natCast_of_lt h_lt
    apply_fun ZMod.val at h
    rw [hv, ZMod.val_zero] at h
    exact h
  · intro h; rw [h]; push_cast; rfl

/-- Specialization of `val_mod_eq_zero_iff_zmod_mod_eq_zero` for `k = 4`,
the common PC-alignment case. -/
lemma val_mod_4_eq_zero_iff_zmod
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] (x : ZMod p) :
    (x % (4 : ZMod p) = (0 : ZMod p)) ↔ x.val % 4 = 0 := by
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h := val_mod_eq_zero_iff_zmod_mod_eq_zero x 4 (by omega) (by omega)
  rw [show ((4 : ℕ) : ZMod p) = (4 : ZMod p) from by push_cast; rfl] at h
  exact h

/-- Case-split helper for `(a - b).val` over `ZMod p`. The positive branch
matches mathlib's `ZMod.val_sub`; the wrap-around branch follows from
`a - b = -(b - a)` plus `ZMod.neg_val`. The `if`-shape is `omega`-friendly,
making this the missing primitive for `` proofs of operations whose
RHS contains subtraction over `ZMod p` (`AddOperation`, `SubOperation`,
`U16CompareOperation`, etc.). -/
lemma val_sub_cases {p : ℕ} [NeZero p] (a b : ZMod p) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else p - (b.val - a.val) := by
  by_cases h : b.val ≤ a.val
  · rw [if_pos h, ZMod.val_sub h]
  · rw [Nat.not_le] at h
    rw [if_neg (Nat.not_le.mpr h)]
    have hab_eq : a - b = -(b - a) := by ring
    rw [hab_eq, ZMod.neg_val]
    have hba : b - a ≠ 0 := by
      rw [sub_ne_zero]; intro hba; rw [hba] at h; exact lt_irrefl _ h
    rw [if_neg hba, ZMod.val_sub (le_of_lt h)]

end Polymorphic

/-- At `p := KB`, the strong-prime fact decides. Other concrete primes ≥ 2^17
(BabyBear, Mersenne31) similarly decide. Registered as an instance so chip
code that pins `F := Fin KB = ZMod KB` synthesizes the polymorphic helpers
automatically. -/
instance KoalaBear.Fact_2pow17_lt_KB : Fact (2 ^ 17 < KB) := ⟨by decide⟩

/-- Strengthened version of the polymorphic prime-size hypothesis used by the
Mul `` operation lemmas (`core_mul` / `core_mulw` and the
five `MulOperation.spec.<variant>` lemmas). The byte-level carry chain
needs `prod[i].val + carry[i].val * 256 < p` (max ≤ 2 ^ 24 − 1) to lift
the ZMod constraints to Nat equations cleanly. KB ≈ 2^31 satisfies this
trivially; BabyBear and Mersenne31 do as well. -/
instance KoalaBear.Fact_2pow24_lt_KB : Fact (2 ^ 24 < KB) := ⟨by decide⟩

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
