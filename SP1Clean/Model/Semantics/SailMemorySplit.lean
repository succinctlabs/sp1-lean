import SP1Clean.Model.Semantics.SailMemoryRead

/-! # Geometry of Sail's physical memory splits

The successful split's own assertion supplies exact byte coverage. The PMA check supplies the
non-wrapping physical window; neither is an extra premise of the instruction preservation law.
-/

namespace SP1Clean.SailMem
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- The configured PMA check, including the out-of-region fault and misaligned split case. -/
theorem run_check_pma_store_all (source : SailState) (cfg : SailConfigured source)
    (address : BitVec 64) (width : ℕ) :
    (check_pma_with_pmp_priority (.Store .Data) .PBMT_PMA .Machine (.Physaddr address)
      width false).run source = .ok
      (if range_subset address (to_bits width) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) then
        .Ok ⟨if is_aligned_paddr (.Physaddr address) width then .CannotSplit else .CanSplit, 0⟩
      else .Err (.E_SAMO_Access_Fault ())) source := by
  have region : matching_pma_region [SP1_PMA_Region] (.Physaddr address) width =
      if range_subset address (to_bits width) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) then
        some SP1_PMA_Region else none := by
    simp [matching_pma_region, matching_pma_region_bits_range, bits_of_physaddr,
      zero_extend, Sail.BitVec.zeroExtend]
  by_cases inside : range_subset address (to_bits width) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true
  all_goals
    simp only [inside, ↓reduceIte] at region ⊢
    simp only [check_pma_with_pmp_priority, pmaCheck, LeanRV64D.readReg, PreSail.readReg,
    Std.ExtDHashMap.get?_eq_some_get (cfg.init _), cfg.pma_regions, region,
    SailME.run, SailME.throw, PreSail.PreSailME.run, PreSail.PreSailME.throw,
    ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Bind.bind, Pure.pure, bind, pure,
    EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get]
  · cases aligned : is_aligned_paddr (.Physaddr address) width <;>
      simp [SP1_PMA, override_PMA, mag_pma_check, is_mag_applicable_access,
        within_pma_mag, mag_of_pma, pma_misaligned_exception, is_vector_access, aligned,
        LeanRV64D.assert, PreSail.assert, LeanRV64D.Functions.not, sys_misaligned_allowed_within_exp,
        EStateM.bind, EStateM.map, EStateM.pure, ExceptT.bindCont, bind, pure]
  · have pmp := run_pmpCheck_none (.Physaddr address) width (.Store .Data) source cfg.init cfg.pmp_off
    change pmpCheck (.Physaddr address) width (.Store .Data) .Machine source = _ at pmp
    simp [accessFaultFromAccessType, EStateM.bind, EStateM.map, ExceptT.bindCont,
      MonadExceptOf.throw, ExceptT.mk, pure, EStateM.pure, pmp]

/-- Successful physical splitting has positive pieces whose total is exactly the requested width. -/
theorem split_misaligned_span (source target : SailState) (address : BitVec 64)
    (width granule : ℕ) (positive : 0 < width) (splittable : Splittability) (count size : ℤ)
    (ran : (split_misaligned (.Physaddr address) width granule splittable).run source =
      .ok (count, size) target) : 0 < count ∧ 0 < size ∧ count * size = width := by
  simp only [split_misaligned] at ran
  split at ran
  · cases ran
    exact ⟨by omega, by omega, by simp⟩
  · change (split_access address width).run source = .ok (count, size) target at ran
    simp only [split_access, PreSail.assert] at ran
    split at ran
    · rename_i checked
      cases ran
      have power : 0 < (2 : ℤ) ^ min (BitVec.countTrailingZeros address : ℤ)
          (BitVec.countTrailingZeros (to_bits (l := 13) width) : ℤ) := by
        change 0 < (2 : ℤ) ^ (min (BitVec.countTrailingZeros address : ℤ)
          (BitVec.countTrailingZeros (to_bits (l := 13) width) : ℤ)).toNat
        positivity
      have product := beq_iff_eq.mp checked
      let piece : ℤ := (2 : ℤ) ^ min (BitVec.countTrailingZeros address : ℤ)
        (BitVec.countTrailingZeros (to_bits (l := 13) width) : ℤ)
      change width = ((↑width : ℤ).tdiv piece * piece).toNat at product
      have productPositive : 0 < (↑width : ℤ).tdiv piece * piece := by omega
      refine ⟨?_, power, ?_⟩
      · exact Int.pos_of_mul_pos_left productPositive power
      · change (↑width : ℤ).tdiv piece * piece = ↑width
        omega
    · cases ran

/-- The actual PMA interval check bounds the entire nonempty access without address wraparound. -/
theorem bounds_of_sp1_pma (address : BitVec 64) (width : ℕ) (small : width ≤ 8)
    (checked : range_subset address (to_bits width) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    2 ^ 16 ≤ address.toNat ∧ address.toNat + width ≤ 2 ^ 48 := by
  have size : (to_bits width : BitVec 64).toNat = width := by
    simp [to_bits, get_slice_int]
  have p16 : (2#64 ^ 16).toNat = 65536 := by decide
  have p48 : (2#64 ^ 48).toNat = 281474976710656 := by decide
  have le : ∀ x y : BitVec 64, (zopz0zIzJ_u x y = true) ↔ (x.toNat ≤ y.toNat) :=
    fun _ _ => by simp [zopz0zIzJ_u, BitVec.toNatInt]
  unfold range_subset at checked
  rw [Bool.and_eq_true, Bool.and_eq_true, le, le, le] at checked
  simp only [BitVec.toNat_sub, BitVec.toNat_add, size, p16, p48] at checked
  have := address.isLt
  omega

/-- Every byte of every physical split lies inside the original natural-address interval. -/
theorem split_byte_address (address : BitVec 64) (width : ℕ) (count size : ℤ)
    (countPositive : 0 < count) (sizePositive : 0 < size) (total : count * size = width)
    (bounded : address.toNat + width ≤ 2 ^ 48)
    (index byte : ℕ) (indexBound : index < count.toNat) (byteBound : byte < size.toNat) :
    ∃ offset < width, (BitVec.addInt address (↑index * size)).toNat + byte = address.toNat + offset := by
  have countCast := Int.toNat_of_nonneg (le_of_lt countPositive)
  have sizeCast := Int.toNat_of_nonneg (le_of_lt sizePositive)
  have product : count.toNat * size.toNat = width := by
    have natural := total
    rw [← countCast, ← sizeCast, ← Int.natCast_mul] at natural
    exact_mod_cast natural
  have piecePositive : 0 < size.toNat := by omega
  have offsetBound : index * size.toNat + byte < width := by
    nlinarith
  have noWrap : address.toNat + index * size.toNat < 2 ^ 64 := by omega
  have addressEq : (BitVec.addInt address (↑index * size)).toNat =
      address.toNat + index * size.toNat := by
    rw [← sizeCast, ← Int.natCast_mul]
    simp only [BitVec.addInt, BitVec.ofInt_natCast, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : index * size.toNat < 2 ^ 64), Nat.mod_eq_of_lt noWrap]
    rw [Int.toNat_natCast]
  exact ⟨index * size.toNat + byte, offsetBound, by rw [addressEq]; omega⟩

end SP1Clean.SailMem
