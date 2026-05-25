import SP1Clean.AddChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Add.Common

/-! # `AddChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real` (carried as the chip's
  `Assumptions` in `Circuit.lean`). Closes via recursive `ext` through the
  `@[ext]`-marked nested sub-structures (CPUState, RTypeReader,
  MemoryAccessInSharedCols, etc.) and `Vector.ext` reducing to per-element
  `rfl`s.
- `allHold_iff_structural` — bridges `(_root_.Add.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `AddOp.Spec`, `cpuStateSpec`,
  `rtypeReaderSpec`, the two scalar gates. Used downstream by
  `SailBridge.lean` to reconstruct `(Add.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

-- TODO: relocate `spec_inv` (and `iff_sp1_full` below) alongside
-- `AddOperation.spec` in `SP1Operations/Operation/AddOperation/AddOperation.lean`
-- when the SP1Chips rebuild budget permits. Kept here for now to avoid
-- forcing a full SP1Chips rebuild on every iteration of these proofs.
namespace AddOperation

set_option maxHeartbeats 16000000 in
-- The 4 `linear_combination` carry rearrangements + 4 ZMod-cast lifts
-- + 4 `interval_cases` discharges land in the 4-8M heartbeat range;
-- 16M leaves headroom (mirrors `AddOperation.spec`'s budget).
/-- Inverse direction of `AddOperation.spec`: given that the operand and
result Words all fit in 64 bits and the BitVec sum identity holds, the
8-conjunct `AddOperation.constraints` evaluates to `allHold`. Witnesses
the unique base-65536 carry-chain decomposition of the BitVec sum. -/
theorem spec_inv {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : AddOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64)
    (h_isU64_v : cols.value.isU64)
    (h_bv : cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD) :
    SP1ConstraintList.allHold (AddOperation.constraints a b cols 1) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  rw [AddOperation.allHold_constraints_iff]
  obtain ⟨ha0, ha1, ha2, ha3⟩ := Word.lt_cases_of_isU64 h_isU64_a
  obtain ⟨hbb0, hbb1, hbb2, hbb3⟩ := Word.lt_cases_of_isU64 h_isU64_b
  obtain ⟨hv0, hv1, hv2, hv3⟩ := Word.lt_cases_of_isU64 h_isU64_v
  -- Lift the BitVec equation to a Nat-level equation (same chain as
  -- `AddOperation.spec`, lines 88-94).
  rw [show execute_RTYPE_pure_w a b .ADD = a.toBitVec64 + b.toBitVec64 from rfl,
      ← BitVec.toNat_inj, BitVec.toNat_add,
      Word.toBitVec64_toNat h_isU64_v,
      Word.toBitVec64_toNat h_isU64_b,
      Word.toBitVec64_toNat h_isU64_a,
      Word.toNat_def, Word.toNat_def, Word.toNat_def] at h_bv
  -- Nat-level carries `q0..q3`, each in `{0, 1}` by the limb bounds.
  set q0 : ℕ := (a[0].val + b[0].val) / 65536 with hq0_def
  set q1 : ℕ := (a[1].val + b[1].val + q0) / 65536 with hq1_def
  set q2 : ℕ := (a[2].val + b[2].val + q1) / 65536 with hq2_def
  set q3 : ℕ := (a[3].val + b[3].val + q2) / 65536 with hq3_def
  -- The 4 chained limb equations + carry bounds, all `omega`-discharged
  -- from `h_bv` (Nat-form) + the per-limb `< 65536` bounds.
  have h_chain :
      q0 ≤ 1 ∧ q1 ≤ 1 ∧ q2 ≤ 1 ∧ q3 ≤ 1 ∧
      a[0].val + b[0].val = cols.value[0].val + q0 * 65536 ∧
      a[1].val + b[1].val + q0 = cols.value[1].val + q1 * 65536 ∧
      a[2].val + b[2].val + q1 = cols.value[2].val + q2 * 65536 ∧
      a[3].val + b[3].val + q2 = cols.value[3].val + q3 * 65536 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hq0_def, hq1_def, hq2_def, hq3_def] <;> omega
  obtain ⟨hq0, hq1, hq2, hq3, e0n, e1n, e2n, e3n⟩ := h_chain
  -- Cast each Nat equation to ZMod via `ZMod.natCast_val`.
  have hc0_lift : (a[0] : ZMod p) + b[0] =
      cols.value[0] + (q0 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e0n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc1_lift : (a[1] : ZMod p) + b[1] + (q0 : ZMod p) =
      cols.value[1] + (q1 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e1n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc2_lift : (a[2] : ZMod p) + b[2] + (q1 : ZMod p) =
      cols.value[2] + (q2 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e2n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have hc3_lift : (a[3] : ZMod p) + b[3] + (q2 : ZMod p) =
      cols.value[3] + (q3 : ZMod p) * 65536 := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) e3n
    push_cast at hcast
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
  have h65inv : (65536 : ZMod p) * (65536 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ val_65536_ne_zero
  -- The 4 ZMod-level carry chain rewrites: each carry equals `q_i` (Nat-cast).
  have hc0_eq : (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹ =
      (q0 : ZMod p) := by
    have h : a[0] + b[0] - cols.value[0] = (q0 : ZMod p) * 65536 := by
      linear_combination hc0_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc1_eq : (a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹ = (q1 : ZMod p) := by
    rw [hc0_eq]
    have h : a[1] + b[1] - cols.value[1] + (q0 : ZMod p) =
        (q1 : ZMod p) * 65536 := by
      linear_combination hc1_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc2_eq : (a[2] + b[2] - cols.value[2] + ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹ = (q2 : ZMod p) := by
    rw [hc1_eq]
    have h : a[2] + b[2] - cols.value[2] + (q1 : ZMod p) =
        (q2 : ZMod p) * 65536 := by
      linear_combination hc2_lift
    rw [h, mul_assoc, h65inv, mul_one]
  have hc3_eq : (a[3] + b[3] - cols.value[3] + ((a[2] + b[2] - cols.value[2] +
      ((a[1] + b[1] - cols.value[1] +
      (a[0] + b[0] - cols.value[0]) * (65536 : ZMod p)⁻¹) *
      (65536 : ZMod p)⁻¹)) * (65536 : ZMod p)⁻¹)) *
      (65536 : ZMod p)⁻¹ = (q3 : ZMod p) := by
    rw [hc2_eq]
    have h : a[3] + b[3] - cols.value[3] + (q2 : ZMod p) =
        (q3 : ZMod p) * 65536 := by
      linear_combination hc3_lift
    rw [h, mul_assoc, h65inv, mul_one]
  -- Final discharge: substitute each carry, then `interval_cases` on the
  -- corresponding `q_i ≤ 1` to split into `0 ∨ 1`.
  refine ⟨?_, ?_, ?_, ?_, hv0, hv1, hv2, hv3⟩
  · rw [hc0_eq]; interval_cases q0 <;> simp
  · rw [hc1_eq]; interval_cases q1 <;> simp
  · rw [hc2_eq]; interval_cases q2 <;> simp
  · rw [hc3_eq]; interval_cases q3 <;> simp

end AddOperation

namespace SP1Clean.AddOp

/-- Bidirectional bridge between `AddOperation.allHold` (with multiplicity
fixed to `1`) and the BitVec semantic: a fully-bounded operand triple
satisfies the constraints iff the result is also bounded and the BitVec
sum identity holds. Composes `AddOperation.spec` (forward) with
`AddOperation.spec_inv` (backward). -/
theorem iff_sp1_full {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} {cols : AddOperation (ZMod p)}
    (h_isU64_a : a.isU64) (h_isU64_b : b.isU64) :
    (AddOperation.constraints a b cols 1).allHold ↔
      (cols.value.isU64 ∧
       cols.value.toBitVec64 = execute_RTYPE_pure_w a b .ADD) :=
  ⟨AddOperation.spec h_isU64_a h_isU64_b,
   fun ⟨h_isU64_v, h_bv⟩ =>
     AddOperation.spec_inv h_isU64_a h_isU64_b h_isU64_v h_bv⟩

end SP1Clean.AddOp

namespace SP1Clean.Add

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[32] = is_real` (which
matches the constraint compiler's emission — Main[32] is both `is_real` and
`is_trusted`). Recursive `ext` through `@[ext]`-marked sub-structures plus
`Vector.ext` reduces to per-element equations closed by `rfl` (each
`(toMain cols)[k]` reduces by `@[reducible]` to the matching `cols`
projection) or by the precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : AddCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  -- Break up the cols structure.
  rcases cols with ⟨state, adapter, op_a_write_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  -- Apply all relevant ext lemmas
  simp [this, AddCols.ext_iff, CPUState.ext_iff,
    RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  -- All that remains are trivial Array equality using `interval_cases`.
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Add.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `RTypeReader.Gated.Assertion.Spec`,
`Main[13] = 0` (the chip-level `op_a_0` zero gate), and the semantic
RV64-add conjunct (`isU64` of the result + the BitVec equation), under
`is_real = Main[32] = 1`. The byte-carry decomposition that SP1's
`AddOperation` threads internally is *not* exposed in the RHS — it's
reconstructed from the BitVec equation and the `isU64` bounds of op_b /
op_c (available from `RTypeReader.Gated.Spec`'s `RegisterAccess.Spec`
sub-conjuncts) via `SP1Clean.AddOp.iff_sp1_full`. Used inside the Sail
clause's external bridge (`SailBridge.sail_correct_of_formalSpec`) to
construct an `allHold` from the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[32]⟩ ∧
       SP1Clean.RTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 0,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[28], Main[29], Main[30], Main[31]],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13], op_b := Main[14],
             op_b_memory :=
               { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                 access_timestamp :=
                   { prev_low := Main[19], diff_low_limb := Main[20] } },
             op_c := Main[21],
             op_c_memory :=
               { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                 access_timestamp :=
                   { prev_low := Main[26], diff_low_limb := Main[27] } } },
           Main[32], Main[32]⟩ ∧
       Main[13] = 0 ∧
       Word.isU64 #v[Main[28], Main[29], Main[30], Main[31]] ∧
       Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
         RV64.add (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]])
                  (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Add.allHold_constraints_iff Main, h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.RTypeReader.Gated.Assertion.Spec_iff_sp1]
  -- After the rewrite, LHS is:
  --   AddOperation.allHold (op_b op_c result 1) ∧
  --   CPUState.Gated.Spec ∧ RTypeReader.Gated.Spec ∧ 1*(1-1)=0 ∧ Main[13]=0
  -- We use `iff_sp1_full` to swap `AddOperation.allHold` for `(isU64 ∧ bv_eq)`,
  -- pulling `isU64 op_b/op_c` out of the RTR.Spec sub-conjuncts.
  refine ⟨?_, ?_⟩
  · -- Forward: allHold → structural conjuncts + (isU64 ∧ RV64.add eq).
    -- After the `rw [h_is_real]` above, the `is_real` / `mult` fields in
    -- the rewritten LHS are now literal `1`, so the gating disjunction in
    -- each `RegisterAccess.Spec` resolves via `one_ne_zero`.
    rintro ⟨h_op, h_cpu, h_rtr, _, h_op_a_0⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have ⟨h_isU64_v, h_bv⟩ :=
      (SP1Clean.AddOp.iff_sp1_full h_isU64_b h_isU64_c).mp h_op
    refine ⟨h_cpu, h_rtr, h_op_a_0, h_isU64_v, ?_⟩
    -- `h_bv : v.toBitVec64 = execute_RTYPE_pure_w op_b op_c .ADD`
    --       = op_b.toBitVec64 + op_c.toBitVec64`.
    -- Goal: `v.toBitVec64 = RV64.add op_c.toBitVec64 op_b.toBitVec64`
    --       = `op_b.toBitVec64 + op_c.toBitVec64`. Closes by `RV64.add` defeq.
    simp only [RV64.add]
    exact h_bv
  · -- Backward: structural conjuncts + (isU64 ∧ RV64.add eq) → allHold.
    rintro ⟨h_cpu, h_rtr, h_op_a_0, h_isU64_v, h_bv⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_bv' : Word.toBitVec64 #v[Main[28], Main[29], Main[30], Main[31]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
                             #v[Main[22], Main[23], Main[24], Main[25]] .ADD := by
      simp only [RV64.add] at h_bv
      exact h_bv
    have h_op :=
      (SP1Clean.AddOp.iff_sp1_full h_isU64_b h_isU64_c).mpr ⟨h_isU64_v, h_bv'⟩
    refine ⟨h_op, h_cpu, h_rtr, ?_, h_op_a_0⟩
    ring

end SP1Clean.Add
