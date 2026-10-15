import SP1Clean.Model.Semantics.SailMemorySplit

/-! # Protected-byte frames for actual Sail writes

The frame preserves the complete register map and every selected byte, including absence. It is
proved for Sail's byte writes and composed through its actual bounded physical-access loop.
-/

namespace SP1Clean.SailMem
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.Advance

/-- Register identity and byte-level preservation on a specified selected region. -/
structure ProtectedMemoryFrame (readOnly : ℕ → Bool) (source target : SailState) : Prop where
  /-- A RAM write does not modify any architectural or platform register. -/
  registers : target.regs = source.regs
  /-- Both the value and presence of every selected byte remain unchanged. -/
  memory : ∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address
  /-- Writes may insert or replace bytes, but never remove an existing byte. -/
  present : ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome

/-- An unchanged state satisfies every selected-byte frame. -/
theorem ProtectedMemoryFrame.refl (readOnly : ℕ → Bool) (source : SailState) :
    ProtectedMemoryFrame readOnly source source := ⟨rfl, fun _ _ => rfl, fun _ present => present⟩

/-- Consecutive actual writes compose their selected-byte frames. -/
theorem ProtectedMemoryFrame.trans {readOnly : ℕ → Bool} {source middle target : SailState}
    (first : ProtectedMemoryFrame readOnly source middle)
    (second : ProtectedMemoryFrame readOnly middle target) :
    ProtectedMemoryFrame readOnly source target :=
  ⟨second.registers.trans first.registers, fun address selected =>
    (second.memory address selected).trans (first.memory address selected),
    fun address present => second.present address (first.present address present)⟩

/-- Identity of the complete register map preserves platform configuration. -/
theorem ProtectedMemoryFrame.configured {readOnly : ℕ → Bool} {source target : SailState}
    (frame : ProtectedMemoryFrame readOnly source target) (cfg : SailConfigured source) :
    SailConfigured target := by
  apply SailConfigured.congr cfg
  · simpa only [SailState.isInitialized, frame.registers] using cfg.init
  · intro register _
    rw [frame.registers]

private theorem run_writeByte_frame (readOnly : ℕ → Bool) (source : SailState)
    (address : ℕ) (value : BitVec 8) (allowed : readOnly address = false) :
    ∃ target, (PreSail.writeByte address value : SailM PUnit).run source = .ok () target ∧
      ProtectedMemoryFrame readOnly source target := by
  refine ⟨{ source with mem := source.mem.insert address value }, rfl, rfl, ?_, ?_⟩
  · intro query selected
    have different : address ≠ query := by intro same; subst query; simp_all
    simp [Std.ExtHashMap.getElem?_insert, different]
  · intro query present
    by_cases same : address = query
    · simp [same]
    · simpa [Std.ExtHashMap.getElem?_insert, same] using present

private theorem run_writeList_frame (readOnly : ℕ → Bool) (source : SailState)
    (bytes : List (ℕ × BitVec 8)) (allowed : ∀ entry ∈ bytes, readOnly entry.1 = false) :
    ∃ target, (bytes.forM fun entry => PreSail.writeByte entry.1 entry.2 : SailM PUnit).run source =
      .ok () target ∧ ProtectedMemoryFrame readOnly source target := by
  induction bytes generalizing source with
  | nil => exact ⟨source, rfl, .refl readOnly source⟩
  | cons byte bytes ih =>
    obtain ⟨middle, first, frame⟩ := run_writeByte_frame readOnly source byte.1 byte.2
      (allowed byte List.mem_cons_self)
    obtain ⟨target, rest, tail⟩ := ih middle (fun entry member => allowed entry (List.mem_cons_of_mem _ member))
    refine ⟨target, ?_, frame.trans tail⟩
    change (PreSail.writeByte byte.1 byte.2 >>= fun _ => _).run source = _
    rw [run_bind_of_run' source middle _ () first]
    exact rest

/-- Sail's little-endian bulk write preserves every byte outside the requested interval. -/
theorem run_writeBytes_frame (readOnly : ℕ → Bool) (source : SailState) (address width : ℕ)
    (value : BitVec (8 * width)) (allowed : ∀ index < width, readOnly (address + index) = false) :
    ∃ target, (PreSail.writeBytes address value : SailM Bool).run source = .ok true target ∧
      ProtectedMemoryFrame readOnly source target := by
  obtain ⟨target, written, frame⟩ := run_writeList_frame readOnly source
    (List.ofFn fun index : Fin width => (address + index.val, value.extractLsb' (8 * index.val) 8)) (by
      intro entry member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact allowed index.val index.isLt)
  refine ⟨target, ?_, frame⟩
  unfold PreSail.writeBytes
  rw [run_bind_of_run' source target _ () written]
  rfl

/-- A physical RAM write is total and preserves registers and all selected bytes. -/
theorem run_write_ram_frame (readOnly : ℕ → Bool) (source : SailState) (address : BitVec 64)
    (width : ℕ) (value : BitVec (8 * width))
    (allowed : ∀ index < width, readOnly (address.toNat + index) = false) :
    ∃ target, (write_ram .Write_plain (.Physaddr address) width value ()).run source = .ok true target ∧
      ProtectedMemoryFrame readOnly source target := by
  obtain ⟨target, written, frame⟩ := run_writeBytes_frame readOnly source address.toNat width value allowed
  refine ⟨target, ?_, frame⟩
  simp only [write_ram, pure_bind, LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.sail_mem_write, bind_assoc]
  rw [run_bind_of_run' source target _ true written]
  rfl

/-- An invariant of the real bounded Sail loop follows from state-threaded body executions. -/
theorem run_untilFuelM_invariant {α β : Type} (condition : α → Bool) (body : α → SailME β α)
    (invariant : α → SailState → Prop)
    (step : ∀ value source, invariant value source → ∃ next target,
      (ExceptT.run (body value)).run source = .ok (.ok next) target ∧ invariant next target)
    (fuel : ℕ) (initial : α) (source : SailState) (start : invariant initial source) :
    ∃ value target, (ExceptT.run (untilFuelM fuel (fun value => pure (condition value)) initial body)).run source =
      .ok (.ok value) target ∧ invariant value target := by
  unfold untilFuelM
  induction fuel generalizing initial source with
  | zero => exact ⟨initial, source, rfl, start⟩
  | succ fuel ih =>
    obtain ⟨value, middle, executed, preserved⟩ := step initial source start
    simp only [untilFuelM.go]
    rw [run_ME_bind_ok _ _ source middle value executed]
    rw [run_ME_bind_ok _ _ middle middle (condition value) (run_ME_pure _ middle)]
    cases checked : condition value
    · exact ih value middle preserved
    · exact ⟨value, middle, rfl, preserved⟩

private theorem frame_of_untilFuelM {α β : Type} (condition : α → Bool) (body : α → SailME β α)
    (finish : α → β) (invariant : α → SailState → Prop) (frame : SailState → Prop)
    (step : ∀ value source, invariant value source → ∃ next target,
      (ExceptT.run (body value)).run source = .ok (.ok next) target ∧ invariant next target)
    (fuel : ℕ) (initial : α) (source target : SailState) (result : β)
    (start : invariant initial source) (conclude : ∀ value state, invariant value state → frame state)
    (ran : (SailME.run (do
      let value ← untilFuelM fuel (fun value => pure (condition value)) initial body
      pure (finish value))).run source = .ok result target) : frame target := by
  obtain ⟨value, actual, loopRun, preserved⟩ :=
    run_untilFuelM_invariant condition body invariant step fuel initial source start
  have complete : (SailME.run (do
      let value ← untilFuelM fuel (fun value => pure (condition value)) initial body
      pure (finish value))).run source = .ok (finish value) actual :=
    run_PreSailME_of_ok _ source actual _ ((run_ME_bind_ok _ _ source actual value loopRun).trans rfl)
  rw [complete] at ran
  cases ran
  exact conclude _ _ preserved

/-- MMIO writes are absent at every physical address in the configured platform. -/
theorem run_mmio_writable_false (source : SailState) (cfg : SailConfigured source)
    (address : physaddr) (width : ℕ) :
    (within_mmio_writable address width).run source = .ok false source := by
  rcases address with ⟨address⟩
  have ran := run_within_mmio_writable_mmio address 0 width source cfg.init cfg.htif_disabled
  change (within_mmio_writable (.Physaddr (address + 0#64 + 0#64)) width).run source = _ at ran
  have zero : ∀ a : BitVec 64, a + 0#64 = a := BitVec.add_zero
  simpa only [zero] using ran

/-- Actual checked writes preserve every protected byte under permission for the decoded span.
The physical window and split geometry are recovered from the executed checks. -/
theorem checked_mem_write_frame (readOnly : ℕ → Bool) (source : SailState)
    (cfg : SailConfigured source) (address : BitVec 64) (width : ℕ)
    (positive : 0 < width) (small : width ≤ 8) (data : BitVec (8 * width))
    (allowed : ∀ index < width, readOnly (address.toNat + index) = false)
    (result : Result Bool (physaddr × ExceptionType)) (target : SailState)
    (ran : (checked_mem_write (.Physaddr address) width data (.Store .Data) .PBMT_PMA
      .Machine () false false false).run source = .ok result target) :
    ProtectedMemoryFrame readOnly source target := by
  simp only [checked_mem_write, bind_assoc, SailME.run, run_SailME_liftM_bind] at ran
  rw [run_bind_of_run source _ _ (run_check_pma_store_all source cfg address width)] at ran
  by_cases inside : range_subset address (to_bits width) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true
  · simp only [inside, ↓reduceIte, pure_bind, run_SailME_liftM_bind] at ran
    obtain ⟨middle, pieces, splitRun, rest⟩ := run_bind_success _ _ source target result ran
    have unchanged := readOnly_split_misaligned source (.Physaddr address) width 0 _ pieces middle splitRun
    subst middle
    rcases pieces with ⟨count, size⟩
    obtain ⟨countPositive, sizePositive, total⟩ :=
      split_misaligned_span source source address width 0 positive _ count size splitRun
    have bounded := (bounds_of_sp1_pma address width small inside).2
    rw [run_bind_of_run source _ _ (show (write_kind_of_flags false false false).run source =
      .ok write_kind.Write_plain source from rfl)] at rest
    clear ran splitRun inside
    refine frame_of_untilFuelM _ _ _
      (fun (value : Bool × ℕ × Bool) state => value.2.1 < count.toNat ∧
        ProtectedMemoryFrame readOnly source state)
      (ProtectedMemoryFrame readOnly source) ?_ _ _ _ _ _
      ⟨by change 0 < count.toNat; omega,
        .refl readOnly source⟩ (fun _ _ valid => valid.2) rest
    rintro ⟨finished, index, success⟩ state ⟨indexBound, frame⟩
    have stateCfg := frame.configured cfg
    have permitted : ∀ byte < size.toNat,
        readOnly ((BitVec.addInt address (↑index * size)).toNat + byte) = false := by
      intro byte byteBound
      obtain ⟨offset, offsetBound, same⟩ := split_byte_address address width count size
        countPositive sizePositive total bounded index byte indexBound byteBound
      rw [same]
      exact allowed offset offsetBound
    obtain ⟨next, written, preserved⟩ := run_write_ram_frame readOnly state
      (BitVec.addInt address (↑index * size)) size.toNat
      ((Sail.BitVec.extractLsb data (8 * (↑index + 1) * size - 1).toNat
        (8 * ↑index * size).toNat).setWidth (8 * size.toNat)) permitted
    let control : Bool × ℕ := if index == (count - 1).toNat then
      (true, index) else (finished, (↑index + 1 : ℤ).toNat)
    refine ⟨(control.1, control.2, success && true), next, ?_, ?_, frame.trans preserved⟩
    · refine (run_ME_bind_ok _ _ state state ()
        (run_ME_liftM _ state state () rfl)).trans ?_
      refine (run_ME_bind_ok _ _ state state none (run_ME_liftM _ state state _
        (run_pmpCheck_none _ _ _ state stateCfg.init stateCfg.pmp_off))).trans ?_
      dsimp only
      refine (run_ME_bind_ok _ _ state state false (run_ME_liftM _ state state _
        (run_mmio_writable_false state stateCfg _ _))).trans ?_
      simp only [Bool.false_eq_true, if_false, bind_assoc, pure_bind]
      exact (run_ME_bind_ok _ _ state next true (run_ME_liftM _ state next _ written)).trans rfl
    · dsimp only [control]
      split
      · exact indexBound
      · rename_i notLast
        have different : index ≠ (count - 1).toNat := by simpa only [beq_iff_eq] using notLast
        change (↑index + 1 : ℤ).toNat < count.toNat
        change index < count.toNat at indexBound
        omega
  · simp only [inside] at ran
    cases ran
    exact .refl readOnly source

/-- Privilege selection and the write callback retain the physical store's byte frame. -/
theorem mem_write_value_frame (readOnly : ℕ → Bool) (source : SailState)
    (cfg : SailConfigured source) (address : BitVec 64) (width : ℕ)
    (positive : 0 < width) (small : width ≤ 8) (data : BitVec (8 * width))
    (allowed : ∀ index < width, readOnly (address.toNat + index) = false)
    (result : Result Bool (physaddr × ExceptionType)) (target : SailState)
    (ran : (mem_write_value (.Physaddr address) width data (.Store .Data) .PBMT_PMA
      false false false).run source = .ok result target) :
    ProtectedMemoryFrame readOnly source target := by
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta at ran
  rw [run_readReg_bind_of_isInitialized source Register.mstatus cfg.init,
    run_readReg_bind_of_isInitialized source Register.cur_privilege cfg.init,
    run_bind_of_run source _ _ (run_effectivePrivilege_configured source cfg _)] at ran
  obtain ⟨middle, value, written, rest⟩ := run_bind_success _ _ source target result ran
  have frame := checked_mem_write_frame readOnly source cfg address width positive small data allowed
    value middle written
  cases rest
  exact frame

end SP1Clean.SailMem
