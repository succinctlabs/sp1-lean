import SP1Clean.Model.Semantics.SailReadOnly

/-! # Read-only stages of ordinary Sail memory accesses

Physical checks, split loads and effective-address checks preserve the complete state, including
fault results. The split loop is handled at arbitrary fuel, without assuming aligned addresses.
-/

namespace SP1Clean.SailMem
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.SailFrame SP1Clean.Soundness.Target SP1Clean.TryStepReduction

private theorem readOnly_readByte (source : SailState) (address : ℕ) :
    ReadOnlyAt source (PreSail.readByte address) := by
  intro value target ran
  cases found : source.mem[address]? with
  | some byte => exact ReadOnlyAt.of_run (run_readByte address byte source found) value target ran
  | none =>
    simp [PreSail.readByte, bind, EStateM.bind, EStateM.run,
      getThe, MonadStateOf.get, MonadState.get, get, EStateM.get, found,
      throw, throwThe] at ran
    cases ran

private theorem readOnly_readBytes (source : SailState) (width address : ℕ) :
    ReadOnlyAt source (PreSail.readBytes width address) := by
  induction width generalizing address with
  | zero => exact ReadOnlyAt.pure source _
  | succ width ih =>
    cases width with
    | zero => exact (readOnly_readByte source address).bind fun _ => ReadOnlyAt.pure source _
    | succ width =>
      apply (readOnly_readByte source address).bind
      intro byte
      apply (ih (address + 1)).bind
      rintro ⟨bytes, tag⟩
      exact ReadOnlyAt.pure source _

/-- A physical RAM read either fails or leaves the entire state unchanged. -/
theorem readOnly_read_ram (source : SailState) (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (read_ram read_kind.Read_plain address width false) := by
  simp only [read_ram, pure_bind]
  apply ReadOnlyAt.bind
  · exact (readOnly_readBytes source width (bits_of_physaddr address).toNat).bind
      fun _ => ReadOnlyAt.pure source _
  · intro result
    cases result
    · exact ReadOnlyAt.pure source _
    · exact ReadOnlyAt.throw source _

private theorem readOnly_assert (source : SailState) (condition : Bool) (message : String) :
    ReadOnlyAt source (LeanRV64D.assert condition message) := by
  cases condition
  · exact ReadOnlyAt.throw source _
  · exact ReadOnlyAt.pure source _

/-- Splitting chooses sizes and checks arithmetic; it does not modify the machine. -/
theorem readOnly_split_misaligned (source : SailState) (address : physaddr) (width granule : ℕ)
    (splittable : Splittability) :
    ReadOnlyAt source (split_misaligned address width granule splittable) := by
  rcases address with ⟨address⟩
  simp only [split_misaligned]
  split
  · exact ReadOnlyAt.pure source _
  · change ReadOnlyAt source (split_access address width)
    exact (readOnly_assert source _ _).bind fun _ => ReadOnlyAt.pure source _

private theorem readOnly_mag (source : SailState) (address : physaddr) (width : ℕ)
    (attributes : PMA) (store : Bool) :
    ReadOnlyAt source (mag_pma_check attributes
      (if store then .Store .Data else .Load .Data) address width) := by
  cases store <;> simp only [Bool.false_eq_true, ↓reduceIte, mag_pma_check,
    is_mag_applicable_access, pure_bind]
  all_goals
    split
    · exact ReadOnlyAt.pure source _
    · simp only [pma_misaligned_exception, pure_bind]
      split
      · exact ReadOnlyAt.pure source _
      · split <;> exact ReadOnlyAt.pure source _

private theorem readOnly_pma (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) (store : Bool) :
    ReadOnlyAt source (pmaCheck address width (if store then .Store .Data else .Load .Data)
      .PBMT_PMA false) := by
  unfold pmaCheck
  apply ReadOnlyAt.runE
  apply ReadOnlyAt.bindE
  · apply ReadOnlyAt.bindE
    · exact (ReadOnlyAt.of_run (Sail.run_readReg_of_isInitialized source _ cfg.init)).lift
    · intro regions
      split
      · cases store <;> exact ReadOnlyAt.pure source _
      · exact ReadOnlyAt.pure source _
  · intro attributes
    have mag := readOnly_mag source address width attributes store
    cases store <;>
      simp only [Bool.false_eq_true, ↓reduceIte, LeanRV64D.Functions.not, Bool.not_false,
        PreSail.assert]
    all_goals
      apply ReadOnlyAt.bindE (ReadOnlyAt.pure source _)
      intro canAccess
      split
      · exact ReadOnlyAt.pure source _
      · apply ReadOnlyAt.bindE
        · exact mag.lift
        · intro result
          rcases result with (⟨splittable, granule⟩ | error)
          · exact ReadOnlyAt.pure source _
          · cases error <;> exact ReadOnlyAt.pure source _

/-- PMP priority and PMA lookup preserve state for both ordinary data-access directions. -/
theorem readOnly_check_pma (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) (store : Bool) :
    ReadOnlyAt source (check_pma_with_pmp_priority
      (if store then .Store .Data else .Load .Data) .PBMT_PMA .Machine address width false) := by
  unfold check_pma_with_pmp_priority
  apply (readOnly_pma source cfg address width store).bind
  intro result
  cases result
  · exact ReadOnlyAt.pure source _
  · apply (ReadOnlyAt.of_run (run_pmpCheck_none address width _ source cfg.init
      cfg.toValidMemConfig.h_pmp_off)).bind
    intro result
    cases result <;> exact ReadOnlyAt.pure source _

/-- MMIO is absent at every physical address in the configured platform. -/
theorem run_mmio_readable_false (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    (within_mmio_readable address width).run source = .ok false source := by
  rcases address with ⟨address⟩
  have ran := run_within_mmio_readable_mmio address 0 width source cfg.init cfg.toValidMemConfig.h_htif_disabled
  change (within_mmio_readable (.Physaddr (address + 0#64 + 0#64)) width).run source = _ at ran
  have zero : ∀ a : BitVec 64, a + 0#64 = a := BitVec.add_zero
  simpa only [zero] using ran

/-- A checked load preserves all state even when the physical access is split or faults. -/
theorem readOnly_checked_mem_read (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (checked_mem_read (.Load .Data) .PBMT_PMA .Machine address width
      false false false false) := by
  unfold checked_mem_read
  apply ReadOnlyAt.runE
  apply ReadOnlyAt.bindE
  · apply (readOnly_check_pma source cfg address width false).lift.bindE
    intro result
    cases result <;> exact ReadOnlyAt.pure source _
  · rintro ⟨splittable, granule⟩
    apply (readOnly_split_misaligned source address width granule splittable).lift.bindE
    rintro ⟨count, size⟩
    apply ReadOnlyAt.bindE_of_run (show (read_kind_of_flags false false false).run source =
      .ok read_kind.Read_plain source from rfl)
    apply ReadOnlyAt.bindE
    · apply ReadOnlyAt.bindE
      · apply ReadOnlyAt.untilE
        · intro value
          exact ReadOnlyAt.pure source _
        · rintro ⟨data, finished, index⟩
          apply ReadOnlyAt.bindE_of_run (show (LeanRV64D.assert true "loop dummy assert").run source =
            .ok () source from rfl)
          apply ReadOnlyAt.bindE_of_run (run_pmpCheck_none _ _ _ source cfg.init cfg.toValidMemConfig.h_pmp_off)
          apply ReadOnlyAt.bindE_of_run (run_mmio_readable_false source cfg _ _)
          apply ReadOnlyAt.bindE
          · apply (readOnly_read_ram source _ _).lift.bindE
            rintro ⟨data, metadata⟩
            exact ReadOnlyAt.pure source _
          · intro data
            exact ReadOnlyAt.pure source _
      · intro value
        exact ReadOnlyAt.pure source _
    · intro value
      exact ReadOnlyAt.pure source _

/-- Ordinary accesses use the configured machine privilege, without changing state. -/
theorem run_effectivePrivilege_configured (source : SailState) (cfg : SailConfigured source)
    (access : MemoryAccessType mem_payload) :
    (effectivePrivilege access (source.regs.get Register.mstatus (cfg.init _))
      (source.regs.get Register.cur_privilege (cfg.init _))).run source =
        .ok Privilege.Machine source := by
  rw [cfg.toValidMemConfig.h_cur_privilege]
  exact run_effectivePrivilege_of_mprv_clear access _ _ source cfg.mprv_disabled

/-- The complete physical load path, including callbacks and split accesses, is read-only. -/
theorem readOnly_mem_read (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (mem_read (.Load .Data) .PBMT_PMA address width false false false) := by
  unfold mem_read
  apply ReadOnlyAt.bind_of_run (Sail.run_readReg_of_isInitialized source Register.mstatus cfg.init)
  apply ReadOnlyAt.bind_of_run (Sail.run_readReg_of_isInitialized source Register.cur_privilege cfg.init)
  apply ReadOnlyAt.bind_of_run (run_effectivePrivilege_configured source cfg _)
  unfold mem_read_priv mem_read_priv_meta
  apply ReadOnlyAt.bind
  · exact (readOnly_checked_mem_read source cfg address width).bind fun _ => ReadOnlyAt.pure source _
  · intro result
    exact ReadOnlyAt.pure source _

/-- The store's effective-address validation performs no writes, including on faults. -/
theorem readOnly_mem_write_ea (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    ReadOnlyAt source (mem_write_ea address width (.Store .Data) .PBMT_PMA false false false) := by
  unfold mem_write_ea
  apply ReadOnlyAt.runE
  apply ReadOnlyAt.bindE_of_run (Sail.run_readReg_of_isInitialized source Register.mstatus cfg.init)
  apply ReadOnlyAt.bindE_of_run (Sail.run_readReg_of_isInitialized source Register.cur_privilege cfg.init)
  apply ReadOnlyAt.bindE_of_run (run_effectivePrivilege_configured source cfg _)
  apply ReadOnlyAt.bindE
  · apply (readOnly_check_pma source cfg address width true).lift.bindE
    intro result
    cases result <;> exact ReadOnlyAt.pure source _
  · rintro ⟨splittable, granule⟩
    apply (readOnly_split_misaligned source address width granule splittable).lift.bindE
    rintro ⟨count, size⟩
    apply ReadOnlyAt.bindE_of_run (show (write_kind_of_flags false false false).run source =
      .ok write_kind.Write_plain source from rfl)
    apply ReadOnlyAt.bindE
    · apply ReadOnlyAt.untilE
      · intro value
        exact ReadOnlyAt.pure source _
      · rintro ⟨finished, index⟩
        apply ReadOnlyAt.bindE_of_run (show (LeanRV64D.assert true "loop dummy assert").run source =
          .ok () source from rfl)
        apply ReadOnlyAt.bindE_of_run (run_pmpCheck_none _ _ _ source cfg.init cfg.toValidMemConfig.h_pmp_off)
        exact ReadOnlyAt.pure source _
    · intro value
      exact ReadOnlyAt.pure source _

/-- Computing the virtual page split is read-only, including a failed internal assertion. -/
theorem readOnly_split_on_page_boundary (source : SailState) (address : BitVec 64) (width : ℕ) :
    ReadOnlyAt source (split_on_page_boundary address width) := by
  simp only [split_on_page_boundary]
  split
  · exact ReadOnlyAt.pure source _
  · exact (readOnly_assert source _ _).bind fun _ => ReadOnlyAt.pure source _

/-- Creating a memory trap reports the current privilege and PC without taking the trap. -/
theorem run_memory_exception (source : SailState) (cfg : SailConfigured source)
    (address : virtaddr) (error : ExceptionType) :
    (memory_exception address error).run source = .ok
      (.Trap (source.regs.get Register.cur_privilege (cfg.init _),
        make_sync_exception error (bits_of_virtaddr address),
        source.regs.get Register.PC (cfg.init _))) source := by
  simp only [memory_exception, trap]
  rw [Sail.run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
    Sail.run_readReg_bind_of_isInitialized source Register.PC cfg.init]
  rfl

end SP1Clean.SailMem
