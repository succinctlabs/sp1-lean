import SP1Foundations.Assumptions

open LeanRV64D.Functions Sail SailState

attribute [simp] LeanRV64D.Functions.xlen_bytes Sail.assert PreSail.assert
  ext_data_get_addr check_misaligned
  LeanRV64D.Functions.plat_enable_misaligned_access
  split_misaligned misaligned_order
  allowed_misaligned sys_misaligned_order_decreasing
  get_config_print_platform
  LeanRV64D.Functions.xlen
  _get_Mstatus_MPP _get_Mstatus_MPRV
  privLevel_of_bits default_write_acc
  effectivePrivilege

/-- For good states there is no `mmio` region. -/
lemma run_within_mmio_writable_mmio (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℕ) (hw : 0 < width) (s : SailState) (hs : SailState.isInitialized s)
    (hclint_base : s.regs.get Register.plat_clint_base (hs _) = 0)
    (hclint_size : s.regs.get Register.plat_clint_size (hs _) = 0) :
    (within_mmio_writable (physaddr.Physaddr
      (zero_extend (BitVec.addInt (reg_val + offset) 0))) width).run s = .ok false s := by
  simp [within_mmio_writable, get_config_rvfi, within_clint]
  simp [run_readReg_of_isInitialized s _ hs, hclint_base, hclint_size]
  simp [within_htif_writable, htif_tohost_base]
  omega

/-- For good states there is no `mmio` region. -/
lemma run_within_mmio_readable_mmio (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℕ) (hw : 0 < width) (s : SailState) (hs : SailState.isInitialized s)
    (hclint_base : s.regs.get Register.plat_clint_base (hs _) = 0)
    (hclint_size : s.regs.get Register.plat_clint_size (hs _) = 0) :
    (within_mmio_readable (physaddr.Physaddr
      (zero_extend (BitVec.addInt (reg_val + offset) 0))) width).run s = .ok false s := by
  simp [within_mmio_readable, get_config_rvfi, within_clint]
  simp [run_readReg_of_isInitialized s _ hs, hclint_base, hclint_size]
  simp [within_htif_readable, htif_tohost_base]
  omega

/-- For good states there is not `phys_mem` bound on size. -/
lemma run_within_phys_mem (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℤ)
    (s : SailState) (hs : SailState.isInitialized s)
    (h_plat_rom_base : s.regs.get Register.plat_rom_base (hs _) = 0)
    (h_low_range : (s.regs.get Register.plat_ram_base (hs _)).toNat ≤
      reg_val.toNat + offset.toNat)
    (h_does_fit : reg_val.toNat + offset.toNat + width ≤
      (s.regs.get Register.plat_ram_base (hs _) +
      s.regs.get Register.plat_ram_size (hs _)).toNat)
    (h_valid : (s.regs.get Register.plat_ram_base (hs _)).toNat +
      (s.regs.get Register.plat_ram_size (hs _)).toNat < 2^64) :
    (within_phys_mem (physaddr.Physaddr (reg_val + offset)) width).run s = .ok true s := by
  have hrvo : reg_val.toNat + offset.toNat + width < 2^64 :=
    by exact lt_of_le_of_lt h_does_fit (BitVec.isLt _)
  simp [within_phys_mem]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_plat_rom_base]
  rw [BitVec.toNat_add_of_lt h_valid] at h_does_fit
  split_ifs with h1 <;> simp
  omega

lemma run_vmem_write_of_width_1'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 8) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit' : (s.regs.get Register.plat_ram_base (hs _)).toNat ≤
      reg_val.toNat + offset.toNat)
    (h_does_fit : reg_val.toNat + offset.toNat + 1 ≤ --width
      (s.regs.get Register.plat_ram_base (hs _) +
      s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (vmem_write (.Regidx rs_addr_bv) offset 1 data
      (AccessType.Write Data) false false false).run s = .ok (.Ok true)
        { s with mem := s.mem.insert (reg_val + offset).toNat data } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base, h_plat_ram_size⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (AccessType.Write Data != AccessType.InstructionFetch ()) = true := rfl
  simp [vmem_write, vmem_write_addr, SailME.run, h_reg_val, h_aligned]
  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [privLevel_bits_backwards]
  simp [h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare]
  simp [mem_write_ea, write_kind_of_flags, mem_write_value, mem_write_value_meta]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [effectivePrivilege, hfetch, h_mprv_disabled]
  simp [mem_write_value_priv_meta, checked_mem_write, h_cur_privilege, phys_access_check, SailME.run]
  simp [LeanRV64D.Functions.sys_pmp_count]
  simp [pmp_check_machine reg_val offset s hs]
  simp [run_within_mmio_writable_mmio reg_val offset 1 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  have := run_within_phys_mem reg_val offset 1 s hs h_plat_rom_base h_does_fit' h_does_fit
    (by simp [h_plat_ram_base, h_plat_ram_size])
  simp [this]
  simp [write_kind_of_flags, phys_mem_write, LeanRV64D.Functions.write_ram,
    sail_mem_write, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, Except.map, BitVec.addInt]

lemma run_vmem_write_of_width_2'
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 16) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 2 ≤ --width
      (s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (vmem_write (.Regidx rs_addr_bv) offset 2 data
      (AccessType.Write Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))) } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (AccessType.Write Data != AccessType.InstructionFetch ()) = true := rfl
  simp [vmem_write, vmem_write_addr, SailME.run, h_reg_val, h_aligned]
  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [privLevel_bits_backwards]
  simp [h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare]
  simp [mem_write_ea, write_kind_of_flags, mem_write_value, mem_write_value_meta]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [effectivePrivilege, hfetch, h_mprv_disabled]
  simp [mem_write_value_priv_meta, checked_mem_write, h_cur_privilege, phys_access_check, SailME.run]
  simp [LeanRV64D.Functions.sys_pmp_count, pmp_check_machine reg_val offset s hs]
  simp [run_within_mmio_writable_mmio reg_val offset 2 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 2 s hs h_plat_ram_base h_plat_rom_base h_does_fit]
  simp [write_kind_of_flags, phys_mem_write, LeanRV64D.Functions.write_ram,
    sail_mem_write, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, Except.map, BitVec.addInt]

lemma run_vmem_write_of_width_4
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 32) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 4 ≤ --width
      (s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (vmem_write (.Regidx rs_addr_bv) offset 4 data
      (AccessType.Write Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          ((reg_val + offset).toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          ((reg_val + offset).toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))) } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (AccessType.Write Data != AccessType.InstructionFetch ()) = true := rfl
  simp [vmem_write, vmem_write_addr, SailME.run, h_reg_val, h_aligned]
  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [privLevel_bits_backwards]
  simp [h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare]
  simp [mem_write_ea, write_kind_of_flags, mem_write_value, mem_write_value_meta]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [effectivePrivilege, hfetch, h_mprv_disabled]
  simp [mem_write_value_priv_meta, checked_mem_write, h_cur_privilege, phys_access_check, SailME.run]
  simp [LeanRV64D.Functions.sys_pmp_count, pmp_check_machine reg_val offset s hs]
  simp [run_within_mmio_writable_mmio reg_val offset 4 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 4 s hs h_plat_ram_base h_plat_rom_base h_does_fit]
  simp [write_kind_of_flags, phys_mem_write, LeanRV64D.Functions.write_ram,
    sail_mem_write, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, Except.map, BitVec.addInt]

lemma run_vmem_write_of_width_8
    (rs_addr_bv : BitVec 5)
    (reg_val : BitVec 64) -- thing inside `rs_addr_bv`
    (offset : BitVec 64)
    (data : BitVec 64) -- bigger for others
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_reg_val : s.get_reg? rs_addr_bv = some reg_val)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 8 = true) ---width
    (hconfig : SailState.isValidMemConfig s hs)
    (h_does_fit : reg_val.toNat + offset.toNat + 8 ≤ --width
      (s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (vmem_write (.Regidx rs_addr_bv) offset 8 data
      (AccessType.Write Data) false false false).run s = .ok (.Ok true)
        { s with mem := ((((((((s.mem.insert
          (reg_val + offset).toNat (BitVec.ofNat 8 data.toNat)).insert
          ((reg_val + offset).toNat + 1) (BitVec.ofNat 8 (data.toNat >>> 8))).insert
          ((reg_val + offset).toNat + 2) (BitVec.ofNat 8 (data.toNat >>> 16))).insert
          ((reg_val + offset).toNat + 3) (BitVec.ofNat 8 (data.toNat >>> 24))).insert
          ((reg_val + offset).toNat + 4) (BitVec.ofNat 8 (data.toNat >>> 32))).insert
          ((reg_val + offset).toNat + 5) (BitVec.ofNat 8 (data.toNat >>> 40))).insert
          ((reg_val + offset).toNat + 6) (BitVec.ofNat 8 (data.toNat >>> 48))).insert
          ((reg_val + offset).toNat + 7) (BitVec.ofNat 8 (data.toNat >>> 56))) } := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hconfig
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hfetch : (AccessType.Write Data != AccessType.InstructionFetch ()) = true := rfl
  simp [vmem_write, vmem_write_addr, SailME.run, h_reg_val, h_aligned]
  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [privLevel_bits_backwards]
  simp [h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare]
  simp [mem_write_ea, write_kind_of_flags, mem_write_value, mem_write_value_meta]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [effectivePrivilege, hfetch, h_mprv_disabled]
  simp [mem_write_value_priv_meta, checked_mem_write, h_cur_privilege, phys_access_check, SailME.run]
  simp [LeanRV64D.Functions.sys_pmp_count, pmp_check_machine reg_val offset s hs]
  simp [run_within_mmio_writable_mmio reg_val offset 8 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 8 s hs h_plat_ram_base h_plat_rom_base h_does_fit]
  simp [write_kind_of_flags, phys_mem_write, LeanRV64D.Functions.write_ram,
    sail_mem_write, PreSail.sail_mem_write, PreSail.writeBytes,
    PreSail.writeByte, Except.map, BitVec.addInt]

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
    (h_does_fit : reg_val.toNat + offset.toNat + 1 < 2^64)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data)
      :
    let width := 1
    (vmem_read (.Regidx rs_addr_bv) offset width (AccessType.Read ())
      false false false).run s = .ok (.Ok data) s := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base, h_plat_ram_size⟩ := hconfig
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega

  simp [vmem_read, SailME.run, h_reg_val, h_aligned]

  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [hfetch, h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _),
    SailME.run,
    mem_read, mem_read_priv, MemoryOpResult_drop_meta, mem_read_priv_meta,
    checked_mem_read, phys_access_check, LeanRV64D.Functions.sys_pmp_count,
    pmp_check_machine' reg_val offset s hs]

  simp [run_within_mmio_readable_mmio reg_val offset 1 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 1 s hs h_plat_ram_base h_plat_rom_base
    (by simp [h_plat_ram_size]; clear *- h_does_fit; omega)]
  simp [write_kind_of_flags, phys_mem_read, LeanRV64D.Functions.read_ram,
    read_kind_of_flags,
    sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, Except.map, BitVec.addInt]

  simp [hmem₀']
  simp [Except.map]
  simp [BitVec.updateSubrange, BitVec.updateSubrange']

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
    (h_does_fit : reg_val.toNat + offset.toNat + 2 < 2^64)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁) :
    let width := 2
    let data := data₁ ++ data₀
    (vmem_read (.Regidx rs_addr_bv) offset width (AccessType.Read ())
      false false false).run s = .ok (.Ok data) s := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base, h_plat_ram_size⟩ := hconfig
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega

  simp [vmem_read, SailME.run, h_reg_val, h_aligned]

  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [hfetch, h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _),
    SailME.run,
    mem_read, mem_read_priv, MemoryOpResult_drop_meta, mem_read_priv_meta,
    checked_mem_read, phys_access_check, LeanRV64D.Functions.sys_pmp_count,
    pmp_check_machine' reg_val offset s hs]

  simp [run_within_mmio_readable_mmio reg_val offset 2 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 2 s hs h_plat_ram_base h_plat_rom_base
    (by simp [h_plat_ram_size]; clear *- h_does_fit; omega)]
  simp [write_kind_of_flags, phys_mem_read, LeanRV64D.Functions.read_ram,
    read_kind_of_flags,
    sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, Except.map, BitVec.addInt]

  simp [hmem₀', hmem₁']
  simp [Except.map]
  simp [BitVec.updateSubrange, BitVec.updateSubrange']

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
    (h_does_fit : reg_val.toNat + offset.toNat + 4 < 2^64)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + offset.toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + offset.toNat + 3]? = some data₃) :
    let width := 4
    let data := data₃ ++ data₂ ++ data₁ ++ data₀
    (vmem_read (.Regidx rs_addr_bv) offset width (AccessType.Read ())
      false false false).run s = .ok (.Ok data) s := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base, h_plat_ram_size⟩ := hconfig
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 2]? = some data₂ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 3]? = some data₃ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega

  simp [vmem_read, SailME.run, h_reg_val, h_aligned]

  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [hfetch, h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _),
    SailME.run,
    mem_read, mem_read_priv, MemoryOpResult_drop_meta, mem_read_priv_meta,
    checked_mem_read, phys_access_check, LeanRV64D.Functions.sys_pmp_count,
    pmp_check_machine' reg_val offset s hs]
  stop
  simp [run_within_mmio_readable_mmio reg_val offset 4 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  simp [run_within_phys_mem reg_val offset 4 s hs h_plat_ram_base h_plat_rom_base
    (by simp [h_plat_ram_size]; clear *- h_does_fit; omega)]
  simp [write_kind_of_flags, phys_mem_read, LeanRV64D.Functions.read_ram,
    read_kind_of_flags,
    sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, Except.map, BitVec.addInt]

  simp [hmem₀', hmem₁', hmem₂', hmem₃']
  simp [Except.map]
  simp [BitVec.updateSubrange, BitVec.updateSubrange']

set_option maxHeartbeats 2000000
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
    (h_does_fit : reg_val.toNat + offset.toNat + 8 < 2^64)
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
    (vmem_read (.Regidx rs_addr_bv) offset width (AccessType.Read ())
      false false false).run s = .ok (.Ok data) s := by
  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base, h_plat_ram_size⟩ := hconfig
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616]? = some data₀ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 1]? = some data₁ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 2]? = some data₂ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 18446744073709551616 + 3]? = some data₃ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega

  simp [vmem_read, SailME.run, h_reg_val, h_aligned]

  simp [untilFuelM, untilFuelM.go]
  simp [translateAddr, translationMode, effectivePrivilege]
  simp [run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _)]
  simp [hfetch, h_mprv_disabled, h_cur_privilege, hmachine, hsatp_bare,
    run_readReg_of_isInitialized s _ hs, Std.ExtDHashMap.get?_eq_some_get (hs _),
    SailME.run,
    mem_read, mem_read_priv, MemoryOpResult_drop_meta, mem_read_priv_meta,
    checked_mem_read, phys_access_check, LeanRV64D.Functions.sys_pmp_count,
    pmp_check_machine' reg_val offset s hs]

  simp [run_within_mmio_readable_mmio reg_val offset 8 (by omega) s hs h_clint_base h_clint_size]
  simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend]
  stop
  simp [run_within_phys_mem reg_val offset 8 s hs h_plat_ram_base h_plat_rom_base
    (by simp [h_plat_ram_size]; clear *- h_does_fit; omega)]
  simp [write_kind_of_flags, phys_mem_read, LeanRV64D.Functions.read_ram,
    read_kind_of_flags,
    sail_mem_read, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, Except.map, BitVec.addInt]

  have : (reg_val.toNat + offset.toNat) % 18446744073709551616 = reg_val.toNat + offset.toNat := by
    rw [Nat.mod_eq_of_lt]; omega

  simp [this, add_assoc]
  simp [hmem₀, hmem₁, hmem₂, hmem₃, hmem₄, hmem₅, hmem₆, hmem₇, ← add_assoc]
  simp [Except.map]
  simp [BitVec.updateSubrange, BitVec.updateSubrange']
