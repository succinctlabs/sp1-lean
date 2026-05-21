import SP1Foundations.Assumptions

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

attribute [simp] LeanRV64D.Functions.xlen_bytes Sail.assert PreSail.assert
  ext_data_get_addr
  -- LeanRV64D.Functions.plat_enable_misaligned_access
  split_misaligned misaligned_order
  allowed_misaligned sys_misaligned_order_decreasing
  -- get_config_print_platform
  LeanRV64D.Functions.xlen
  _get_Mstatus_MPP _get_Mstatus_MPRV
  -- privLevel_of_bits
  effectivePrivilege
  zopz0zI_u zopz0zK_u
  BitVec.toNatInt
  htif_tohost_size
  LeanRV64D.Functions.not

/-- In sail-v4, `jump_to target` runs:
  1. an extension hook `ext_control_check_pc target` (constant `none`),
  2. an `assert` that `target` bit 0 is `0`,
  3. an `if (bit_to_bool (target bit 1)) && (not (← currentlyEnabled Ext_Zca))`
     guard, and otherwise
  4. `writeReg nextPC target; pure RETIRE_SUCCESS`.
For `target % 4 = 0` both bit 0 and bit 1 are 0, so the assert passes and
`bit_to_bool 0#1 = false` short-circuits the `&&` regardless of the Zca read's
value. The Zca read still executes monadically (reading `misa`), but is
state-preserving on `isInitialized s` — handled by `SailME_run_readReg_map_writeReg`. -/
theorem jump_to_of_mod4_eq_zero (target : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s) (h_aligned : target % 4#64 = 0) :
    EStateM.run (jump_to target) s =
      EStateM.Result.ok LeanRV64D.Functions.RETIRE_SUCCESS
        { s with regs := s.regs.insert Register.nextPC target } := by
  have h0 : target[0] = false := by bv_decide
  have h1 : target[1] = false := by bv_decide
  have hs_misa : (s.regs.get? Register.misa).isSome := by
    simp [Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [jump_to, ext_control_check_pc, h0, h1]
  exact SailME_run_readReg_map_writeReg s Register.misa Register.nextPC hs_misa target
    (fun _ => RETIRE_SUCCESS)

lemma update_elp_state_of_isInitialized (rs1 : regidx) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs' : isValidMemConfig s hs) :
    EStateM.run (update_elp_state rs1) s = EStateM.Result.ok () s := by
  simp [update_elp_state, run_readReg_of_isInitialized s _ hs, hs'.h_cur_privilege,
    get_xLPE, _get_Seccfg_MLPE, hartSupports, hs'.h_mseccfg_disabled]

set_option linter.style.nativeDecide false in
/-- The CLINT region sits at `[plat_clint_base, plat_clint_base + plat_clint_size)`
with `plat_clint_base = 2 ^ 25 = 33554432`. Every caller below supplies a bound
placing the access strictly below this region. -/
lemma run_within_mmio_writable_mmio (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℕ) (s : SailState) (hs : SailState.isInitialized s)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none) :
    (within_mmio_writable (physaddr.Physaddr
      (zero_extend (BitVec.addInt (reg_val + offset) 0))) width).run s = .ok false s := by
  have h_base : BitVec.toNat plat_clint_base = 33554432 := by native_decide
  have h_bv : (reg_val + offset).toNat = (reg_val.toNat + offset.toNat) % 18446744073709551616 :=
    BitVec.toNat_add reg_val offset
  simp [within_mmio_writable, get_config_rvfi, within_clint]
  simp [run_readReg_of_isInitialized s _ hs, within_htif_writable, h_htif,
    BitVec.addInt, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.toNatInt,
    plat_have_clint, within_sig]

set_option linter.style.nativeDecide false in
/-- Read counterpart of `run_within_mmio_writable_mmio`. -/
lemma run_within_mmio_readable_mmio (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℕ) (s : SailState) (hs : SailState.isInitialized s)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none) :
    (within_mmio_readable (physaddr.Physaddr
      (zero_extend (BitVec.addInt (reg_val + offset) 0))) width).run s = .ok false s := by
  have h_base : BitVec.toNat plat_clint_base = 33554432 := by native_decide
  have h_bv : (reg_val + offset).toNat = (reg_val.toNat + offset.toNat) % 18446744073709551616 :=
    BitVec.toNat_add reg_val offset
  simp [within_mmio_readable, get_config_rvfi, within_clint]
  simp [run_readReg_of_isInitialized s _ hs, h_htif, within_htif_readable,
    within_htif_writable, BitVec.addInt, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt, within_sig]


lemma run_checked_mem_write_one_byte_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region]) :
    let paddr_nat := BitVec.toNat (w := 64) (zero_extend (BitVec.addInt (reg_val + offset) 0))
    (checked_mem_write
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 1
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run s
      = .ok (.Ok true) { s with mem := s.mem.insert paddr_nat data } := by
  simp [checked_mem_write, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_writable_mmio reg_val offset 1 s hs h_htif]
  simp [write_kind_of_flags, write_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_write, PreSail.ConcurrencyInterfaceV1.sail_mem_write]
  simp [PreSail.writeBytes, PreSail.writeByte]

/-- One-byte `mem_write_value` under kernel config: the `effectivePrivilege`
resolves to `Machine` (via `h_mprv_disabled` + `h_cur_privilege`), the
alignment precondition is vacuous (`rl = con = false`), and the rest reduces
via `run_checked_mem_write_one_byte_of_isInitialized`. -/
lemma run_mem_write_value_one_byte_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    (mem_write_value
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 1
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run s
      = .ok (.Ok true) { s with mem := s.mem.insert paddr_nat data } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, _, h_htif, h_pma⟩ := hconfig
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  apply run_checked_mem_write_one_byte_of_isInitialized reg_val offset data
    s hs h_in_range h_htif h_pma

/-- Two-byte `checked_mem_write` under kernel config. Same structure as the
one-byte version; the final state has two `mem.insert`s for the low and high
bytes of `data : BitVec 16`. -/
lemma run_checked_mem_write_two_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 16)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region]) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := (s.mem.insert paddr_nat (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))
    (checked_mem_write
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 2
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  simp [checked_mem_write, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_writable_mmio reg_val offset 2 s hs h_htif]
  simp [write_kind_of_flags, write_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_write, PreSail.ConcurrencyInterfaceV1.sail_mem_write]
  simp [PreSail.writeBytes, PreSail.writeByte,
    List.ofFn, List.forM, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb', BitVec.toNat_setWidth]

/-- Two-byte `mem_write_value` under kernel config. -/
lemma run_mem_write_value_two_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 16)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := (s.mem.insert paddr_nat (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))
    (mem_write_value
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 2
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  apply run_checked_mem_write_two_bytes_of_isInitialized reg_val offset data
    s hs h_in_range h_htif h_pma

/-- Four-byte `checked_mem_write` under kernel config. -/
lemma run_checked_mem_write_four_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 32)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region]) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := ((((s.mem.insert paddr_nat
      (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (paddr_nat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (paddr_nat + 3) (BitVec.ofNat 8 (data.toNat >>> 24)))
    (checked_mem_write
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 4
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  simp [checked_mem_write, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_writable_mmio reg_val offset 4 s hs h_htif]
  simp [write_kind_of_flags, write_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_write, PreSail.ConcurrencyInterfaceV1.sail_mem_write]
  simp [PreSail.writeBytes, PreSail.writeByte,
    List.ofFn, List.forM, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb', BitVec.toNat_setWidth]

/-- Four-byte `mem_write_value` under kernel config. -/
lemma run_mem_write_value_four_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 32)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := ((((s.mem.insert paddr_nat
      (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (paddr_nat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (paddr_nat + 3) (BitVec.ofNat 8 (data.toNat >>> 24)))
    (mem_write_value
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 4
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  apply run_checked_mem_write_four_bytes_of_isInitialized reg_val offset data
    s hs h_in_range h_htif h_pma

/-- Eight-byte `checked_mem_write` under kernel config. -/
lemma run_checked_mem_write_eight_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region]) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := ((((((((s.mem.insert paddr_nat
      (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (paddr_nat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (paddr_nat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
      (paddr_nat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
      (paddr_nat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
      (paddr_nat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
      (paddr_nat + 7) (BitVec.ofNat 8 (data.toNat >>> 56)))
    (checked_mem_write
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 8
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine () false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  simp [checked_mem_write, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_writable_mmio reg_val offset 8 s hs h_htif]
  simp [write_kind_of_flags, write_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_write, PreSail.ConcurrencyInterfaceV1.sail_mem_write]
  simp [PreSail.writeBytes, PreSail.writeByte,
    List.ofFn, List.forM, Fin.foldr, Fin.foldr.loop,
    BitVec.extractLsb', BitVec.toNat_setWidth]

/-- Eight-byte `mem_write_value` under kernel config. -/
lemma run_mem_write_value_eight_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs) :
    let paddr_nat :=
      BitVec.toNat ((zero_extend (BitVec.addInt (reg_val + offset) 0)) : BitVec 64)
    let new_mem := ((((((((s.mem.insert paddr_nat
      (BitVec.ofNat 8 data.toNat)).insert
      (paddr_nat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
      (paddr_nat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
      (paddr_nat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
      (paddr_nat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
      (paddr_nat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
      (paddr_nat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
      (paddr_nat + 7) (BitVec.ofNat 8 (data.toNat >>> 56)))
    (mem_write_value
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 8
        data (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA false false false).run s
      = .ok (.Ok true) { s with mem := new_mem } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  apply run_checked_mem_write_eight_bytes_of_isInitialized reg_val offset data
    s hs h_in_range h_htif h_pma

/-- One-byte `checked_mem_read` under kernel config. Assumes the byte lives in
memory at `paddr`. -/
lemma run_checked_mem_read_one_byte_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region])
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 1
        false false false false).run s = .ok (.Ok (data, ())) s := by
  simp [checked_mem_read, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_readable_mmio reg_val offset 1 s hs h_htif]
  simp [read_kind_of_flags, read_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_read, PreSail.ConcurrencyInterfaceV1.sail_mem_read]
  simp only [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data := by
    rw [show (reg_val.toNat + offset.toNat) % 18446744073709551616 = (reg_val + offset).toNat from
      (BitVec.toNat_add reg_val offset).symm]
    exact hmem₀
  simp [PreSail.readBytes, PreSail.readByte, hmem₀',
    bind, Bind.bind, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    pure, Pure.pure, Functor.map, getThe, MonadStateOf.get, MonadState.get, get,
    EStateM.get, MemoryOpResult_add_meta]

/-- One-byte `mem_read` under kernel config. Handles `effectivePrivilege = Machine`
then chains to `run_checked_mem_read_one_byte_of_isInitialized`. -/
lemma run_mem_read_one_byte_of_isInitialized
    (reg_val offset : BitVec 64) (data : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 1
        false false false).run s = .ok (.Ok data) s := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_read, mem_read_priv, mem_read_priv_meta, MemoryOpResult_drop_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  exact ⟨_, run_checked_mem_read_one_byte_of_isInitialized reg_val offset data
    s hs h_in_range h_htif h_pma hmem₀, rfl⟩

/-- Two-byte `checked_mem_read` under kernel config. -/
lemma run_checked_mem_read_two_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data₀ data₁ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region])
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 2
        false false false false).run s
      = .ok (.Ok (data₁ ++ data₀, ())) s := by
  simp [checked_mem_read, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_readable_mmio reg_val offset 2 s hs h_htif]
  simp [read_kind_of_flags, read_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_read, PreSail.ConcurrencyInterfaceV1.sail_mem_read]
  simp only [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  -- Need `s.mem[...]? = some data₀` and `s.mem[...+1]? = some data₁` matching
  -- the exact form after zero_extend normalization.
  have hmod : (reg_val + offset).toNat = (reg_val.toNat + offset.toNat) % 18446744073709551616 :=
    BitVec.toNat_add reg_val offset
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rw [← hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rw [← hmod]; exact hmem₁
  simp [PreSail.readBytes, PreSail.readByte, hmem₀', hmem₁',
    bind, Bind.bind, EStateM.bind, EStateM.map, EStateM.pure,
    EStateM.run, pure, Pure.pure, Functor.map, getThe, MonadStateOf.get, MonadState.get,
    get, EStateM.get, MemoryOpResult_add_meta]

/-- Two-byte `mem_read` under kernel config. -/
lemma run_mem_read_two_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data₀ data₁ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 2
        false false false).run s = .ok (.Ok (data₁ ++ data₀)) s := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_read, mem_read_priv, mem_read_priv_meta, MemoryOpResult_drop_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  exact ⟨_, run_checked_mem_read_two_bytes_of_isInitialized reg_val offset data₀ data₁
    s hs h_in_range h_htif h_pma hmem₀ hmem₁, rfl⟩

/-- Four-byte `checked_mem_read` under kernel config. -/
lemma run_checked_mem_read_four_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region])
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + offset).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + offset).toNat + 3]? = some data₃) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 4
        false false false false).run s
      = .ok (.Ok (data₃ ++ data₂ ++ data₁ ++ data₀, ())) s := by
  simp [checked_mem_read, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_readable_mmio reg_val offset 4 s hs h_htif]
  simp [read_kind_of_flags, read_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_read, PreSail.ConcurrencyInterfaceV1.sail_mem_read]
  simp only [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  have hmod : (reg_val + offset).toNat = (reg_val.toNat + offset.toNat) % 18446744073709551616 :=
    BitVec.toNat_add reg_val offset
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rw [← hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rw [← hmod]; exact hmem₁
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 2]? = some data₂ := by
    rw [← hmod]; exact hmem₂
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 3]? = some data₃ := by
    rw [← hmod]; exact hmem₃
  simp [PreSail.readBytes, PreSail.readByte, hmem₀', hmem₁', hmem₂', hmem₃',
    bind, Bind.bind, EStateM.bind, EStateM.map, EStateM.pure,
    EStateM.run, pure, Pure.pure, Functor.map, getThe, MonadStateOf.get, MonadState.get,
    get, EStateM.get, MemoryOpResult_add_meta]

/-- Four-byte `mem_read` under kernel config. -/
lemma run_mem_read_four_bytes_of_isInitialized
    (reg_val offset : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + offset).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + offset).toNat + 3]? = some data₃) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 4
        false false false).run s
      = .ok (.Ok (data₃ ++ data₂ ++ data₁ ++ data₀)) s := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_read, mem_read_priv, mem_read_priv_meta, MemoryOpResult_drop_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  exact ⟨_, run_checked_mem_read_four_bytes_of_isInitialized reg_val offset
    data₀ data₁ data₂ data₃ s hs h_in_range h_htif h_pma hmem₀ hmem₁ hmem₂ hmem₃, rfl⟩

/-- Eight-byte `checked_mem_read` under kernel config. -/
lemma run_checked_mem_read_eight_bytes_of_isInitialized
    (reg_val offset : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_htif : s.regs.get Register.htif_tohost_base (hs _) = none)
    (h_pma : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region])
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + offset).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + offset).toNat + 3]? = some data₃)
    (hmem₄ : s.mem[(reg_val + offset).toNat + 4]? = some data₄)
    (hmem₅ : s.mem[(reg_val + offset).toNat + 5]? = some data₅)
    (hmem₆ : s.mem[(reg_val + offset).toNat + 6]? = some data₆)
    (hmem₇ : s.mem[(reg_val + offset).toNat + 7]? = some data₇) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 8
        false false false false).run s
      = .ok (.Ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀, ())) s := by
  simp [checked_mem_read, phys_access_check, pmpCheck, SailME.run, PreSail.PreSailME.run]
  simp [pmaCheck, run_readReg_of_isInitialized s _ hs, h_pma]
  simp [matching_pma_region, matching_pma_region_bits_range]
  erw [h_in_range]
  simp [EStateM.Result.map, accessFaultFromAccessType,
    pma_misaligned_exception, SP1_PMA]
  simp [is_aligned_paddr, override_PMA, - EStateM.run_bind]
  erw [EStateM.run_bind, run_within_mmio_readable_mmio reg_val offset 8 s hs h_htif]
  simp [read_kind_of_flags, read_ram]
  simp [ConcurrencyInterfaceV1.sail_mem_read, PreSail.ConcurrencyInterfaceV1.sail_mem_read]
  simp only [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  have hmod : (reg_val + offset).toNat = (reg_val.toNat + offset.toNat) % 18446744073709551616 :=
    BitVec.toNat_add reg_val offset
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rw [← hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rw [← hmod]; exact hmem₁
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 2]? = some data₂ := by
    rw [← hmod]; exact hmem₂
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 3]? = some data₃ := by
    rw [← hmod]; exact hmem₃
  have hmem₄' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 4]? = some data₄ := by
    rw [← hmod]; exact hmem₄
  have hmem₅' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 5]? = some data₅ := by
    rw [← hmod]; exact hmem₅
  have hmem₆' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 6]? = some data₆ := by
    rw [← hmod]; exact hmem₆
  have hmem₇' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 7]? = some data₇ := by
    rw [← hmod]; exact hmem₇
  simp [PreSail.readBytes, PreSail.readByte,
    hmem₀', hmem₁', hmem₂', hmem₃', hmem₄', hmem₅', hmem₆', hmem₇',
    bind, Bind.bind, EStateM.bind, EStateM.map, EStateM.pure,
    EStateM.run, pure, Pure.pure, Functor.map, getThe, MonadStateOf.get, MonadState.get,
    get, EStateM.get, MemoryOpResult_add_meta]

/-- Eight-byte `mem_read` under kernel config. -/
lemma run_mem_read_eight_bytes_of_isInitialized
    (reg_val offset : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + offset).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + offset).toNat + 3]? = some data₃)
    (hmem₄ : s.mem[(reg_val + offset).toNat + 4]? = some data₄)
    (hmem₅ : s.mem[(reg_val + offset).toNat + 5]? = some data₅)
    (hmem₆ : s.mem[(reg_val + offset).toNat + 6]? = some data₆)
    (hmem₇ : s.mem[(reg_val + offset).toNat + 7]? = some data₇) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0))) 8
        false false false).run s
      = .ok (.Ok (data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀)) s := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, _, h_htif, h_pma⟩ := hconfig
  simp [mem_read, mem_read_priv, mem_read_priv_meta, MemoryOpResult_drop_meta,
    run_readReg_of_isInitialized s _ hs,
    h_mprv_disabled, h_cur_privilege]
  exact ⟨_, run_checked_mem_read_eight_bytes_of_isInitialized reg_val offset
    data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ s hs h_in_range h_htif h_pma
    hmem₀ hmem₁ hmem₂ hmem₃ hmem₄ hmem₅ hmem₆ hmem₇, rfl⟩

-- /-- For good states there is not `phys_mem` bound on size. -/
-- lemma run_within_phys_mem (reg_val : BitVec 64) (offset : BitVec 64)
--     (width : ℤ)
--     (s : SailState)
--     (hs : SailState.isInitialized s)
--     (h_plat_ram_base : s.regs.get Register.plat_ram_base (hs _) = 0)
--     (h_plat_rom_base : s.regs.get Register.plat_rom_base (hs _) = 0)
--     (h_does_fit : reg_val.toNat + offset.toNat + width ≤
--       (s.regs.get Register.plat_ram_size (hs _)).toNat) :
--     (within_phys_mem (physaddr.Physaddr (reg_val + offset)) width).run s = .ok true s := by
--   simp [within_phys_mem]
--   simp [run_readReg_of_isInitialized s _ hs]
--   simp [h_plat_ram_base, h_plat_rom_base]
--   split_ifs with h1 <;> simp; omega

/-- Convert the Sail-level alignment check to a plain `Nat`-mod fact. -/
lemma is_aligned_vaddr_iff_mod (addr : BitVec 64) (N : ℕ) :
    is_aligned_vaddr (virtaddr.Virtaddr addr) N = true ↔ addr.toNat % N = 0 := by
  rw [is_aligned_vaddr]
  simp only [Sail.BitVec.toNatInt, beq_iff_eq]
  rw [show (Int.ofNat addr.toNat : ℤ) = ((addr.toNat : ℕ) : ℤ) from rfl,
      show (N : ℤ) = ((N : ℕ) : ℤ) from rfl, ← Int.ofNat_tmod, Nat.cast_eq_zero]

/-- Bridge: every access whose `addr` lives in `[2^16, 2^48 - N]` falls inside
the SP1 PMA window `[2^16, 2^48)`. Chip-side proofs derive `addr ≥ 2^16` from
the `AddressOperation` top-two-limb inverse trick and `addr.toNat + N ≤ 2^48`
from the AddrAddOperation u48 bound (plus per-width alignment), then call this
to satisfy the `h_in_range` precondition of every `run_vmem_*_of_width_*'`. -/
lemma range_subset_sp1_pma (addr : BitVec 64) (N : ℕ) (hN_pos : 0 < N)
    (h_lo : 2 ^ 16 ≤ addr.toNat) (h_hi : addr.toNat + N ≤ 2 ^ 48) :
    range_subset (zero_extend (BitVec.addInt addr 0) : BitVec 64)
      (to_bits N : BitVec 64) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
  have hzext : (zero_extend (BitVec.addInt addr 0) : BitVec 64) = addr := by
    simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend, BitVec.ofInt]
  rw [hzext]
  have h_to_bits : (to_bits N : BitVec 64).toNat = N := by
    simp [to_bits, get_slice_int, BitVec.toNat_ofInt]; omega
  have h_p16 : (2#64 ^ 16).toNat = 65536 := by decide
  have h_p48 : (2#64 ^ 48).toNat = 281474976710656 := by decide
  have h_eq : ∀ x y : BitVec 64, (zopz0zIzJ_u x y = true) ↔ (x.toNat ≤ y.toNat) :=
    fun _ _ => by simp [zopz0zIzJ_u, BitVec.toNatInt]
  unfold range_subset
  rw [Bool.and_eq_true, Bool.and_eq_true, h_eq, h_eq, h_eq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [BitVec.toNat_sub, BitVec.toNat_add, h_to_bits, h_p16, h_p48] <;> omega

lemma run_vmem_write_of_width_1'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 8)
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (_h_does_fit : reg_val.toNat + offset.toNat + 1 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (vmem_write (.Regidx rs_addr_bv) offset 1 data
      (MemoryAccessType.Store mem_payload.Data) false false false).run s = .ok (.Ok true)
        { s with mem := s.mem.insert (reg_val + offset).toNat data } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Store mem_payload.Data != MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  -- Stage 1: unfold `vmem_write` → `vmem_write_addr` → `ext_data_get_addr` and
  -- push the monad tower through `s`. `hrx` collapses the `rX_bits` read;
  -- `h_aligned` picks the aligned branch of `split_misaligned` so the outer loop
  -- is fuel-1.
  unfold vmem_write vmem_write_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  -- Stage 2: reduce `translateAddr` in Machine/MPRV=0/Bare mode down to
  -- `Ok (Physaddr (reg_val + offset), PBMT_PMA, init_ext_ptw)`.
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  -- Stage 3: unfold `mem_write_ea` and `is_store_conditional` to push through
  -- the pre-`mem_write_value` scaffolding (these are pure / `rl = con = false`).
  -- Do NOT unfold `mem_write_value` — we use the proven
  -- `run_mem_write_value_one_byte_of_isInitialized` below.
  simp [mem_write_ea, is_store_conditional, write_kind_of_flags, hfetch,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.run,
    bind, Bind.bind, pure, Pure.pure, Functor.map,
    ExceptT.bindCont, ExceptT.pure, ExceptT.bind]
  -- Stage 4: apply the dedicated `run_mem_write_value_one_byte_of_isInitialized`
  -- lemma. It handles `effectivePrivilege → Machine` plus
  -- `checked_mem_write → mem.insert` in one shot.
  have hconfig : SailState.isValidMemConfig s hs :=
    ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩
  have h := run_mem_write_value_one_byte_of_isInitialized reg_val offset data s hs h_in_range
    hconfig
  simp only [EStateM.run] at h
  -- Normalize `zero_extend (BitVec.addInt (reg_val + offset) 0)` → `reg_val + offset`
  -- in both the goal and `h` so they match syntactically.
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  -- `h` now rewrites the innermost `mem_write_value ... s` call directly.
  conv_lhs => rw [h]
  -- The outer match tower over `EStateM.Result.ok/error` reduces by constructor.
  rfl

lemma run_vmem_write_of_width_2'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64)
    (offset : BitVec 64)
    (data : BitVec 16)
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (_h_does_fit : reg_val.toNat + offset.toNat + 2 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (vmem_write (.Regidx rs_addr_bv) offset 2 data
      (MemoryAccessType.Store mem_payload.Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Store mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  unfold vmem_write vmem_write_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  simp [mem_write_ea, is_store_conditional, write_kind_of_flags, hfetch,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.run,
    bind, Bind.bind, pure, Pure.pure, Functor.map,
    ExceptT.bindCont, ExceptT.pure, ExceptT.bind]
  have hconfig : SailState.isValidMemConfig s hs :=
    ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩
  have h := run_mem_write_value_two_bytes_of_isInitialized reg_val offset data s hs h_in_range
    hconfig
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  rfl

lemma run_vmem_write_of_width_4
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64)
    (offset : BitVec 64)
    (data : BitVec 32)
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (_h_does_fit : reg_val.toNat + offset.toNat + 4 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (vmem_write (.Regidx rs_addr_bv) offset 4 data
      (MemoryAccessType.Store mem_payload.Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          ((reg_val + offset).toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          ((reg_val + offset).toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Store mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  unfold vmem_write vmem_write_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  simp [mem_write_ea, is_store_conditional, write_kind_of_flags, hfetch,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.run,
    bind, Bind.bind, pure, Pure.pure, Functor.map,
    ExceptT.bindCont, ExceptT.pure, ExceptT.bind]
  have hconfig : SailState.isValidMemConfig s hs :=
    ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩
  have h := run_mem_write_value_four_bytes_of_isInitialized reg_val offset data s hs h_in_range
    hconfig
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  rfl

lemma run_vmem_write_of_width_8
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64)
    (offset : BitVec 64)
    (data : BitVec 64)
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 8 = true)
    (hconfig : SailState.isValidMemConfig s hs)
    (_h_does_fit : reg_val.toNat + offset.toNat + 8 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true) :
    (vmem_write (.Regidx rs_addr_bv) offset 8 data
      (MemoryAccessType.Store mem_payload.Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((((((((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          ((reg_val + offset).toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          ((reg_val + offset).toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
          ((reg_val + offset).toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
          ((reg_val + offset).toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
          ((reg_val + offset).toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
          ((reg_val + offset).toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) } := by
  obtain ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Store mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  unfold vmem_write vmem_write_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  simp [mem_write_ea, is_store_conditional, write_kind_of_flags, hfetch,
    EStateM.map, EStateM.bind, EStateM.pure, EStateM.run,
    bind, Bind.bind, pure, Pure.pure, Functor.map,
    ExceptT.bindCont, ExceptT.pure, ExceptT.bind]
  have hconfig : SailState.isValidMemConfig s hs :=
    ⟨h_cur_privilege, h_mprv_disabled, h_mseccfg_disabled, h_htif, h_pma⟩
  have h := run_mem_write_value_eight_bytes_of_isInitialized reg_val offset data s hs h_in_range
    hconfig
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  rfl

/-- Sp1-side reduction of a 1-byte `write_ram` call at bare `BitVec`. Pairs with
`run_vmem_write_of_width_1'` to let `Store*Chip.correct` discharge the post-`rw` bullet-1
equation without invoking the default simp set on a `Word (ZMod p)`-carrying goal — the
trigger documented in `docs/PROOF_PATTERNS.md` §3 (2026-05-19 sorry-bisect) for the kernel
deep-recursion. The polymorphic instance graph never enters this helper's olean. -/
lemma run_write_ram_of_width_1 (s : SailState) (addr : BitVec 64) (data : BitVec 8) :
    EStateM.run (Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr data) s
    = EStateM.Result.ok () { s with mem := s.mem.insert addr.toNat data } := by
  simp [Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
    PreSail.writeBytes, PreSail.writeByte,
    bind, pure, EStateM.bind, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
    List.forM, List.ofFn, Fin.foldr, Fin.foldr.loop, forM,
    Functor.mapConst, Function.const]

/-- Bullet-1 equation for byte stores, lifted to bare `BitVec 64`/`BitVec 8`. Pairs with
`run_vmem_write_of_width_1'` (which reduces the spec-side `vmem_write` to a `.ok (.Ok true) S`
form): together they collapse the bullet-1 equation produced by
`rw [run_vmem_write_of_width_1' ...]` in a `Store*Chip.correct` proof, without needing the
default simp set on a `Word (ZMod p)`-carrying goal — the trigger documented in
`docs/PROOF_PATTERNS.md` §3 (2026-05-19 sorry-bisect). -/
lemma store_byte_post_vmem_eq
    (s : SailState) (pc addr : BitVec 64) (data : BitVec 8) :
    (match (EStateM.Result.ok (α := Result Bool ExecutionResult)
              (Result.Ok true)
              { s with regs := s.regs.insert Register.nextPC pc,
                       mem := s.mem.insert addr.toNat data }) with
       | .ok x s' => EStateM.run (match x with
                                  | .Ok _ => pure RETIRE_SUCCESS
                                  | .Err e => pure e) s'
       | .error e s' => EStateM.Result.error e s')
    = EStateM.Result.map (fun _ : Unit => RETIRE_SUCCESS)
        (EStateM.run
          (Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr data)
          { s with regs := s.regs.insert Register.nextPC pc }) := by
  rw [run_write_ram_of_width_1]
  rfl

/-- Sp1-side reduction of a 2-byte `write_ram` call at bare `BitVec`. Width-2 analogue of
`run_write_ram_of_width_1`; see that lemma's docstring for the kernel-recursion context. -/
lemma run_write_ram_of_width_2 (s : SailState) (addr : BitVec 64) (data : BitVec 16) :
    EStateM.run (Sail.ConcurrencyInterfaceV1.write_ram 64 2 0#64 addr data) s
    = EStateM.Result.ok ()
        { s with mem :=
            ((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
              (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) } := by
  simp [Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
    PreSail.writeBytes, PreSail.writeByte,
    bind, pure, EStateM.bind, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
    List.forM, List.ofFn, Fin.foldr, Fin.foldr.loop, forM,
    Functor.mapConst, Function.const]

/-- Width-2 analogue of `store_byte_post_vmem_eq`. -/
lemma store_half_post_vmem_eq
    (s : SailState) (pc addr : BitVec 64) (data : BitVec 16) :
    (match (EStateM.Result.ok (α := Result Bool ExecutionResult)
              (Result.Ok true)
              { s with regs := s.regs.insert Register.nextPC pc,
                       mem := ((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
                                (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) }) with
       | .ok x s' => EStateM.run (match x with
                                  | .Ok _ => pure RETIRE_SUCCESS
                                  | .Err e => pure e) s'
       | .error e s' => EStateM.Result.error e s')
    = EStateM.Result.map (fun _ : Unit => RETIRE_SUCCESS)
        (EStateM.run
          (Sail.ConcurrencyInterfaceV1.write_ram 64 2 0#64 addr data)
          { s with regs := s.regs.insert Register.nextPC pc }) := by
  rw [run_write_ram_of_width_2]
  rfl

/-- Sp1-side reduction of a 4-byte `write_ram` call at bare `BitVec`. Width-4 analogue of
`run_write_ram_of_width_1`. -/
lemma run_write_ram_of_width_4 (s : SailState) (addr : BitVec 64) (data : BitVec 32) :
    EStateM.run (Sail.ConcurrencyInterfaceV1.write_ram 64 4 0#64 addr data) s
    = EStateM.Result.ok ()
        { s with mem :=
            ((((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
              (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
              (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
              (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) } := by
  simp [Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
    PreSail.writeBytes, PreSail.writeByte,
    bind, pure, EStateM.bind, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
    List.forM, List.ofFn, Fin.foldr, Fin.foldr.loop, forM,
    Functor.mapConst, Function.const]

/-- Width-4 analogue of `store_byte_post_vmem_eq`. -/
lemma store_word_post_vmem_eq
    (s : SailState) (pc addr : BitVec 64) (data : BitVec 32) :
    (match (EStateM.Result.ok (α := Result Bool ExecutionResult)
              (Result.Ok true)
              { s with regs := s.regs.insert Register.nextPC pc,
                       mem := ((((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
                                 (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
                                 (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
                                 (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) }) with
       | .ok x s' => EStateM.run (match x with
                                  | .Ok _ => pure RETIRE_SUCCESS
                                  | .Err e => pure e) s'
       | .error e s' => EStateM.Result.error e s')
    = EStateM.Result.map (fun _ : Unit => RETIRE_SUCCESS)
        (EStateM.run
          (Sail.ConcurrencyInterfaceV1.write_ram 64 4 0#64 addr data)
          { s with regs := s.regs.insert Register.nextPC pc }) := by
  rw [run_write_ram_of_width_4]
  rfl

/-- Sp1-side reduction of an 8-byte `write_ram` call at bare `BitVec`. Width-8 analogue of
`run_write_ram_of_width_1`. -/
lemma run_write_ram_of_width_8 (s : SailState) (addr : BitVec 64) (data : BitVec 64) :
    EStateM.run (Sail.ConcurrencyInterfaceV1.write_ram 64 8 0#64 addr data) s
    = EStateM.Result.ok ()
        { s with mem :=
            ((((((((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
                (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
                (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
                (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
                (addr.toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
                (addr.toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
                (addr.toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
                (addr.toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) } := by
  simp [Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
    PreSail.writeBytes, PreSail.writeByte,
    bind, pure, EStateM.bind, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
    EStateM.modifyGet, Functor.map, ExceptT.run, ExceptT.bind, ExceptT.pure,
    List.forM, List.ofFn, Fin.foldr, Fin.foldr.loop, forM,
    Functor.mapConst, Function.const]

/-- Width-8 analogue of `store_byte_post_vmem_eq`. -/
lemma store_double_post_vmem_eq
    (s : SailState) (pc addr : BitVec 64) (data : BitVec 64) :
    (match (EStateM.Result.ok (α := Result Bool ExecutionResult)
              (Result.Ok true)
              { s with regs := s.regs.insert Register.nextPC pc,
                       mem := ((((((((s.mem.insert addr.toNat (BitVec.ofNat 8 data.toNat)).insert
                                  (addr.toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
                                  (addr.toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
                                  (addr.toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
                                  (addr.toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
                                  (addr.toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
                                  (addr.toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
                                  (addr.toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) }) with
       | .ok x s' => EStateM.run (match x with
                                  | .Ok _ => pure RETIRE_SUCCESS
                                  | .Err e => pure e) s'
       | .error e s' => EStateM.Result.error e s')
    = EStateM.Result.map (fun _ : Unit => RETIRE_SUCCESS)
        (EStateM.run
          (Sail.ConcurrencyInterfaceV1.write_ram 64 8 0#64 addr data)
          { s with regs := s.regs.insert Register.nextPC pc }) := by
  rw [run_write_ram_of_width_8]
  rfl

lemma run_vmem_read_of_width_1'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 1 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data)
      :
    let width := 1
    (vmem_read (.Regidx rs_addr_bv) offset width (MemoryAccessType.Load mem_payload.Data)
      false false false).run s = .ok (.Ok data) s := by
  have h_mprv_disabled := hconfig.h_mprv_disabled
  have h_cur_privilege := hconfig.h_cur_privilege
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Load mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  have hmem₀' : s.mem[(reg_val + offset).toNat]? = some data := by
    rwa [show (reg_val + offset).toNat = reg_val.toNat + offset.toNat from by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega]
  unfold vmem_read vmem_read_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  have h := run_mem_read_one_byte_of_isInitialized reg_val offset data s hs h_in_range
    hconfig hmem₀'
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  simp [BitVec.updateSubrange, BitVec.updateSubrange', Sail.BitVec.updateSubrange,
    BitVec.setWidth_eq]
  rfl

lemma run_vmem_read_of_width_2'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data₀ data₁ : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 2 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁) :
    let width := 2
    let data := data₁ ++ data₀
    (vmem_read (.Regidx rs_addr_bv) offset width (MemoryAccessType.Load mem_payload.Data)
      false false false).run s = .ok (.Ok data) s := by
  have h_mprv_disabled := hconfig.h_mprv_disabled
  have h_cur_privilege := hconfig.h_cur_privilege
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Load mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  have hmod : (reg_val + offset).toNat = reg_val.toNat + offset.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hmem₀' : s.mem[(reg_val + offset).toNat]? = some data₀ := by rw [hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val + offset).toNat + 1]? = some data₁ := by rw [hmod]; exact hmem₁
  unfold vmem_read vmem_read_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  have h := run_mem_read_two_bytes_of_isInitialized reg_val offset data₀ data₁ s hs h_in_range
    hconfig hmem₀' hmem₁'
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  simp [BitVec.updateSubrange, BitVec.updateSubrange', Sail.BitVec.updateSubrange,
    BitVec.setWidth_eq]
  rfl

lemma run_vmem_read_of_width_4'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 4 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + offset.toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + offset.toNat + 3]? = some data₃) :
    let width := 4
    let data := data₃ ++ data₂ ++ data₁ ++ data₀
    (vmem_read (.Regidx rs_addr_bv) offset width (MemoryAccessType.Load mem_payload.Data)
      false false false).run s = .ok (.Ok data) s := by
  have h_mprv_disabled := hconfig.h_mprv_disabled
  have h_cur_privilege := hconfig.h_cur_privilege
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Load mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  have hmod : (reg_val + offset).toNat = reg_val.toNat + offset.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hmem₀' : s.mem[(reg_val + offset).toNat]? = some data₀ := by rw [hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val + offset).toNat + 1]? = some data₁ := by rw [hmod]; exact hmem₁
  have hmem₂' : s.mem[(reg_val + offset).toNat + 2]? = some data₂ := by rw [hmod]; exact hmem₂
  have hmem₃' : s.mem[(reg_val + offset).toNat + 3]? = some data₃ := by rw [hmod]; exact hmem₃
  unfold vmem_read vmem_read_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  have h := run_mem_read_four_bytes_of_isInitialized reg_val offset
    data₀ data₁ data₂ data₃ s hs h_in_range hconfig hmem₀' hmem₁' hmem₂' hmem₃'
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  simp [BitVec.updateSubrange, BitVec.updateSubrange', Sail.BitVec.updateSubrange,
    BitVec.setWidth_eq]
  rfl

-- deeply nested `run_vmem_read` unfolds
lemma run_vmem_read_of_width_8'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 8 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 8 < 2 ^ 64)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (reg_val + offset) 0))
      (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + offset.toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + offset.toNat + 3]? = some data₃)
    (hmem₄ : s.mem[reg_val.toNat + offset.toNat + 4]? = some data₄)
    (hmem₅ : s.mem[reg_val.toNat + offset.toNat + 5]? = some data₅)
    (hmem₆ : s.mem[reg_val.toNat + offset.toNat + 6]? = some data₆)
    (hmem₇ : s.mem[reg_val.toNat + offset.toNat + 7]? = some data₇) :
    let width := 8
    let data := data₇ ++ data₆ ++ data₅ ++ data₄ ++ data₃ ++ data₂ ++ data₁ ++ data₀
    (vmem_read (.Regidx rs_addr_bv) offset width (MemoryAccessType.Load mem_payload.Data)
      false false false).run s = .ok (.Ok data) s := by
  have h_mprv_disabled := hconfig.h_mprv_disabled
  have h_cur_privilege := hconfig.h_cur_privilege
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (MemoryAccessType.Load mem_payload.Data !=
      MemoryAccessType.InstructionFetch ()) = true := rfl
  have hrx : rX_bits (regidx.Regidx rs_addr_bv) s = .ok reg_val s := by
    have h := @run_rX_bits rs_addr_bv s
    simp only [EStateM.run] at h
    rw [h, h_reg_val]
  have hmod : (reg_val + offset).toNat = reg_val.toNat + offset.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hmem₀' : s.mem[(reg_val + offset).toNat]? = some data₀ := by rw [hmod]; exact hmem₀
  have hmem₁' : s.mem[(reg_val + offset).toNat + 1]? = some data₁ := by rw [hmod]; exact hmem₁
  have hmem₂' : s.mem[(reg_val + offset).toNat + 2]? = some data₂ := by rw [hmod]; exact hmem₂
  have hmem₃' : s.mem[(reg_val + offset).toNat + 3]? = some data₃ := by rw [hmod]; exact hmem₃
  have hmem₄' : s.mem[(reg_val + offset).toNat + 4]? = some data₄ := by rw [hmod]; exact hmem₄
  have hmem₅' : s.mem[(reg_val + offset).toNat + 5]? = some data₅ := by rw [hmod]; exact hmem₅
  have hmem₆' : s.mem[(reg_val + offset).toNat + 6]? = some data₆ := by rw [hmod]; exact hmem₆
  have hmem₇' : s.mem[(reg_val + offset).toNat + 7]? = some data₇ := by rw [hmod]; exact hmem₇
  unfold vmem_read vmem_read_addr ext_data_get_addr
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift, Functor.map, Except.map,
    Bind.bind, Pure.pure, SailME.throw, PreSail.PreSailME.throw,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, EStateM.run,
    hrx, h_aligned, split_misaligned, misaligned_order, untilFuelM, untilFuelM.go,
    LeanRV64D.Functions.not]
  simp [translateAddr, translationMode, effectivePrivilege,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.lift, ExceptT.map, ExceptT.pure,
    MonadLift.monadLift, liftM, monadLift,
    bind, pure, EStateM.bind, EStateM.map, EStateM.pure, Functor.map,
    Sail.readReg, PreSail.readReg, run_readReg_of_isInitialized s _ hs,
    Std.ExtDHashMap.get?_eq_some_get (hs _),
    getThe, MonadStateOf.get, MonadState.get, get, EStateM.get,
    modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet,
    privLevel_bits_backwards, privLevel_bits_forwards,
    h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    hfetch, is_shadow_stack_access]
  have h := run_mem_read_eight_bytes_of_isInitialized reg_val offset
    data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ s hs h_in_range hconfig
    hmem₀' hmem₁' hmem₂' hmem₃' hmem₄' hmem₅' hmem₆' hmem₇'
  simp only [EStateM.run] at h
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend] at h ⊢
  conv_lhs => rw [h]
  simp [BitVec.updateSubrange, BitVec.updateSubrange', Sail.BitVec.updateSubrange,
    BitVec.setWidth_eq]
  rfl
