import SP1Foundations.SailM

open LeanRV64D.Functions Sail SailState

axiom pmp_check_machine (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    EStateM.run (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (AccessType.Write Data) Privilege.Machine) s = EStateM.Result.ok none s

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

/-- For good states there is not `phys_mem` bound on size. -/
lemma run_within_phys_mem (reg_val : BitVec 64) (offset : BitVec 64)
    (width : ℤ)
    (s : SailState)
    (hs : SailState.isInitialized s)
    (h_plat_ram_base : s.regs.get Register.plat_ram_base (hs _) = 0)
    (h_plat_rom_base : s.regs.get Register.plat_rom_base (hs _) = 0)
    (h_does_fit : reg_val.toNat + offset.toNat + width ≤
      (s.regs.get Register.plat_ram_size (hs _)).toNat) :
    (within_phys_mem (physaddr.Physaddr (reg_val + offset)) width).run s = .ok true s := by
  simp [within_phys_mem]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_plat_ram_base, h_plat_rom_base]
  split_ifs with h1 <;> simp <;> omega
