import SP1Clean.Model.Semantics.SailStepReduction

/-! # Official Sail fetch from authenticated code memory

Configuration and committed ROM bytes determine the actual Sail fetch result. The PC-dependent
fetch facts are derived only at an executed address; configuration itself remains independent of PC.
These lemmas are shared by the semantic execution model and the existing instruction bridges.
-/

open LeanRV64D.Defs
namespace SP1Clean.Advance

open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.SailMem

/-- **L1 — little-endian byte reassembly.** The four `RomLoaded` bytes of a fetched word `w`
(`data₀..₃ = w.extractLsb' (8·i) 8`), concatenated high-to-low, reassemble `w`. The `: BitVec 32`
ascription normalizes the `8+8+8+8` append width to `32` so `bv_decide` sees a well-typed goal. -/
theorem word_reassemble (w : BitVec 32) :
    (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 : BitVec 32) = w := by
  bv_decide

/-- **L2 — 4-alignment clears the low two pc bits.** A `pc` with `pc.toNat % 4 = 0` has bit 0 and bit 1
zero — the `access0`/`access1` fields the fetch reduction needs. -/
theorem pc_align_bits (pc : BitVec 64) (h : pc.toNat % 4 = 0) :
    BitVec.ofBool pc[0] = 0#1 ∧ BitVec.ofBool pc[1] = 0#1 := by
  have hb : pc[0] = false ∧ pc[1] = false := by
    simp only [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not]
    omega
  rw [hb.1, hb.2]; exact ⟨rfl, rfl⟩

/-! ## The `StraightLineReady` producer (the `toStraightLineReady` body) -/

/-- **`StraightLineReady` on the post-`minstret_increment`-write state.** From the quiescent machine-mode
config facts on `s` — initialized, machine privilege, active hart, `mstatus.MIE = 0`, `mideleg = 0`, no
landing-pad expectation, valid memory config, PC 4-aligned, and the ROM word present in memory — the
`try_step` post-write state `{s with regs.insert minstret_increment b}` is `StraightLineReady` for the
fetched word `data₃ ++ … ++ data₀`. Pure assembly: the two deep fields come from the `_writeMinstret`
frame lemmas (`run_dispatchInterrupt_machine_none_writeMinstret` / `run_fetch_eq_F_Base_writeMinstret`);
the three register-read fields frame through the disjoint `minstret_increment` insert. This is the body of
the eventual `SailConfigured.toStraightLineReady` (its hypotheses are the strengthened config's fields). -/
theorem straightLineReady_writeMinstret
    (s : SailState) (b : Bool) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (hinit : s.isInitialized)
    (hconfig : SailMem.SailState.isValidMemConfig s hinit)
    (hmie : _get_Mstatus_MIE (s.regs.get Register.mstatus (hinit _)) = 0#1)
    (hmideleg : s.regs.get Register.mideleg (hinit _) = zeros)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ()))
    (h_elp : s.regs.get? Register.elp
      ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED))
    (h_pc : s.regs.get Register.PC (hinit _) = pc)
    (h_access0 : BitVec.ofBool pc[0] = 0#1) (h_access1 : BitVec.ofBool pc[1] = 0#1)
    (h_aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true)
    (h_in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
      (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true)
    (h_align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0)
    (h_not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false)
    (hmem₀ : s.mem[(pc + 0).toNat]? = some data₀) (hmem₁ : s.mem[(pc + 0).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(pc + 0).toNat + 2]? = some data₂) (hmem₃ : s.mem[(pc + 0).toNat + 3]? = some data₃) :
    StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) where
  init := SailState.isInitialized_insert s hinit _ _
  priv := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_priv
  active := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_active
  no_interrupt := run_dispatchInterrupt_machine_none_writeMinstret s hinit b hmie hmideleg
  fetched := run_fetch_eq_F_Base_writeMinstret pc data₀ data₁ data₂ data₃ s hinit b hconfig h_pc
    h_access0 h_access1 h_aligned h_in_range h_align h_not_rvc hmem₀ hmem₁ hmem₂ hmem₃
  no_landing_pad := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact h_elp

/-- **The PC-dependent local fetch predicate** — the *local* half of the `try_step` precondition (the
persist-able global half is `SailConfigured`). At `s`'s current pc, the pc is 4-aligned and the 4 ROM
bytes are present in memory, so the base-instruction fetch yields the little-endian word
`data₃ ++ … ++ data₀`. Kept separate from `SailConfigured` (not persist-able) because it is about *this*
pc — in the walk it is derived at each row from `RomLoaded` + the guest program's `rom_aligned` + the row's
pc-match, not carried as a state invariant. -/
structure FetchReady (s : SailState) (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8) : Prop where
  /-- The current pc. -/
  pc_eq : s.regs.get? Register.PC = some pc
  access0 : BitVec.ofBool pc[0] = 0#1
  access1 : BitVec.ofBool pc[1] = 0#1
  aligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true
  in_range : range_subset (zero_extend (BitVec.addInt (pc + 0) 0))
    (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true
  align : Int.tmod (↑(zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64).toNat) 4 = 0
  not_rvc : isRVC (Sail.BitVec.extractLsb (data₃ ++ data₂ ++ data₁ ++ data₀) 15 0) = false
  mem0 : s.mem[(pc + 0).toNat]? = some data₀
  mem1 : s.mem[(pc + 0).toNat + 1]? = some data₁
  mem2 : s.mem[(pc + 0).toNat + 2]? = some data₂
  mem3 : s.mem[(pc + 0).toNat + 3]? = some data₃

/-- **`SailConfigured` + the local fetch facts assemble `StraightLineReady`** — the uniform bridge from the
audit-surface config (`RefinesAt.cfg`) to the ladder's readiness predicate on the post-`minstret`-write
state. The global `SailConfigured` supplies the seven persist-able fields; `FetchReady` supplies the
PC-dependent fetch facts. This is the packaged form of `straightLineReady_writeMinstret`. -/
theorem SailConfigured.toStraightLineReady {s : SailState} (cfg : SailConfigured s) (b : Bool)
    (pc : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (hfetch : FetchReady s pc data₀ data₁ data₂ data₃) :
    StraightLineReady ({s with regs := s.regs.insert Register.minstret_increment b})
      (data₃ ++ data₂ ++ data₁ ++ data₀) :=
  straightLineReady_writeMinstret s b pc data₀ data₁ data₂ data₃
    cfg.init cfg.toValidMemConfig cfg.mie cfg.mideleg cfg.priv cfg.active cfg.no_landing_pad
    (by have h := hfetch.pc_eq; rwa [Std.ExtDHashMap.get?_eq_some_get (cfg.init _), Option.some_inj] at h)
    hfetch.access0 hfetch.access1 hfetch.aligned hfetch.in_range hfetch.align hfetch.not_rvc
    hfetch.mem0 hfetch.mem1 hfetch.mem2 hfetch.mem3

/-- **L7 — the `FetchReady` producer.** At a state whose PC is a ROM address `pc` (`fetchWord pc = some w`)
with the ROM bytes present (`RomLoaded`), the PC-dependent local fetch facts hold: alignment (from the
program's `rom_aligned`), `in_range` (from `rom_in_window` via `range_subset_sp1_pma`), `not_rvc` (from
`rom_full_width` + the byte reassembly `word_reassemble`), and the four ROM bytes (from `RomLoaded`). This
is the derivation the split promised — `FetchReady` reconstructed at each row from the committed program +
the pc match, so it need not be a persist-able state invariant. -/
theorem fetchReady_of_romLoaded
    (prog : GuestProgram) (s : SailState) (pc : BitVec 64) (w : BitVec 32)
    (hrom : RomLoaded prog s) (hfetch : prog.fetchWord pc = some w)
    (hpc : s.regs.get? Register.PC = some pc) :
    FetchReady s pc (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8)
      (w.extractLsb' 24 8) := by
  have hfacts : pc.toNat % 4 = 0 ∧ (2 ^ 16 ≤ pc.toNat ∧ pc.toNat + 4 ≤ 2 ^ 48)
      ∧ w.extractLsb' 0 2 = 0b11#2 := by
    have hf := hfetch
    rw [GuestProgram.fetchWord, Option.map_eq_some_iff] at hf
    obtain ⟨e, hfind, hew⟩ := hf
    have hmem := List.mem_of_find?_eq_some hfind
    have hpc' : e.1 = pc := by have := List.find?_some hfind; simpa using this
    refine ⟨?_, ?_, ?_⟩
    · rw [← hpc']; exact prog.rom_aligned e.1 (List.mem_map_of_mem hmem)
    · rw [← hpc']; exact prog.rom_in_window e hmem
    · rw [← hew]; exact prog.rom_full_width e hmem
  obtain ⟨hmod4, ⟨hlo, hhi⟩, h_fw⟩ := hfacts
  have hz : (zero_extend (BitVec.addInt (pc + 0) 0) : BitVec 64) = pc := by
    simp [zero_extend, BitVec.addInt, Sail.BitVec.zeroExtend, BitVec.ofInt]
  exact
    { pc_eq := hpc
      access0 := (pc_align_bits pc hmod4).1
      access1 := (pc_align_bits pc hmod4).2
      aligned := (SailMem.is_aligned_vaddr_iff_mod pc 4).mpr hmod4
      in_range := by
        rw [show (pc + 0 : BitVec 64) = pc from by bv_decide]
        exact SailMem.range_subset_sp1_pma pc 4 (by norm_num) hlo hhi
      align := by rw [hz, show (4:ℤ) = ((4:ℕ):ℤ) from rfl, ← Int.ofNat_tmod, hmod4]; rfl
      not_rvc := by
        rw [word_reassemble w]
        simp only [isRVC, Sail.BitVec.extractLsb, BitVec.extractLsb]
        rw [show BitVec.extractLsb' 0 (1 - 0 + 1) (BitVec.extractLsb' 0 (15 - 0 + 1) w)
              = w.extractLsb' 0 2 from by
          apply BitVec.eq_of_getLsbD_eq; intro i; simp [BitVec.getLsbD_extractLsb']]
        rw [h_fw]; decide
      mem0 := by have h := hrom pc w hfetch 0; simpa using h
      mem1 := by have h := hrom pc w hfetch 1; simpa using h
      mem2 := by have h := hrom pc w hfetch 2; simpa using h
      mem3 := by have h := hrom pc w hfetch 3; simpa using h }

/-- **`SailConfigured` survives the `minstret_increment` write.** Every config field re-derives on
`{s with regs.insert minstret_increment b}` (the register is disjoint from every config CSR) — the fact the
ladder needs to apply the (∀-configured-state) decode and `toStraightLineReady` at the post-write state. -/
theorem SailConfigured.writeMinstret {s : SailState} (cfg : SailConfigured s) (b : Bool) :
    SailConfigured ({s with regs := s.regs.insert Register.minstret_increment b}) where
  init := SailState.isInitialized_insert s cfg.init _ _
  priv := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.priv
  active := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.active
  mie := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mie
  mideleg := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mideleg
  no_landing_pad := by rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]; exact cfg.no_landing_pad
  mprv_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mprv_disabled
  mseccfg_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mseccfg_disabled
  mseccfg_pmm := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.mseccfg_pmm
  htif_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.htif_disabled
  pmp_off := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.pmp_off
  misa_m := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.misa_m
  misa_c_disabled := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.misa_c_disabled
  pma_regions := by rw [get_writeMinstret_ne (by decide) s b (cfg.init _)]; exact cfg.pma_regions

/-- **`SailConfigured` transfers along a config-register frame.** A state `sf` that is initialized and agrees
with `s` on the nine config registers is itself `SailConfigured` — the `RowEffect.cfg` persistence clause. -/
theorem SailConfigured.congr {sf s : SailState} (cfg : SailConfigured s) (hinit : sf.isInitialized)
    (hf : ∀ R : Register, R = Register.cur_privilege ∨ R = Register.hart_state ∨ R = Register.mstatus
      ∨ R = Register.mideleg ∨ R = Register.elp ∨ R = Register.mseccfg ∨ R = Register.htif_tohost_base
      ∨ R = Register.pma_regions ∨ R = Register.pmpcfg_n ∨ R = Register.misa →
      sf.regs.get? R = s.regs.get? R) :
    SailConfigured sf := by
  have hget : ∀ (R : Register) (hsf : R ∈ sf.regs), sf.regs.get? R = s.regs.get? R →
      sf.regs.get R hsf = s.regs.get R (cfg.init R) := by
    intro R hsf heq
    rw [Std.ExtDHashMap.get?_eq_some_get hsf, Std.ExtDHashMap.get?_eq_some_get (cfg.init R)] at heq
    exact Option.some.injEq _ _ |>.mp heq
  exact
    { init := hinit
      priv := by rw [hf _ (by tauto)]; exact cfg.priv
      active := by rw [hf _ (by tauto)]; exact cfg.active
      mie := by rw [hget Register.mstatus (hinit _) (hf _ (by tauto))]; exact cfg.mie
      mideleg := by rw [hget Register.mideleg (hinit _) (hf _ (by tauto))]; exact cfg.mideleg
      no_landing_pad := by rw [hf _ (by tauto)]; exact cfg.no_landing_pad
      mprv_disabled := by rw [hget Register.mstatus (hinit _) (hf _ (by tauto))]; exact cfg.mprv_disabled
      mseccfg_disabled := by rw [hget Register.mseccfg (hinit _) (hf _ (by tauto))]; exact cfg.mseccfg_disabled
      mseccfg_pmm := by rw [hget Register.mseccfg (hinit _) (hf _ (by tauto))]; exact cfg.mseccfg_pmm
      htif_disabled := by rw [hget Register.htif_tohost_base (hinit _) (hf _ (by tauto))]; exact cfg.htif_disabled
      pmp_off := by rw [hget Register.pmpcfg_n (hinit _) (hf _ (by tauto))]; exact cfg.pmp_off
      misa_m := by rw [hget Register.misa (hinit _) (hf _ (by tauto))]; exact cfg.misa_m
      misa_c_disabled := by rw [hget Register.misa (hinit _) (hf _ (by tauto))]; exact cfg.misa_c_disabled
      pma_regions := by rw [hget Register.pma_regions (hinit _) (hf _ (by tauto))]; exact cfg.pma_regions }

/-- The native platform disables the compressed-instruction mode consulted by Sail jump alignment.
The generated model supports C/Zca, so this follows from the checked CSR, not a constant platform hook. -/
theorem currentlyEnabled_zca_eq_false (source : SailState) (cfg : SailConfigured source) :
    (currentlyEnabled .Ext_Zca).run source = .ok false source := by
  have supportsC : hartSupports .Ext_C = true := by
    simp [hartSupports, LeanRV64D.Functions.xlen, LeanRV64D.Functions.not]
  simp only [currentlyEnabled,
    show hartSupports .Ext_Zca = true by simp [hartSupports], supportsC, bind_assoc, pure_bind]
  rw [run_bind_of_run source _ _ (Sail.run_readReg_of_isInitialized source Register.misa cfg.init)]
  simp [cfg.misa_c_disabled, LeanRV64D.Functions.not]

/-- Actual Sail fetch returns the authenticated committed word without changing state. This
requires a fetch only at the current executed PC, never at a successor or terminal boundary. -/
theorem fetch_eq_of_romLoaded {program : GuestProgram} {source : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    {pc : BitVec 64} {word : BitVec 32}
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) :
    (fetch ()).run source = .ok (FetchResult.F_Base word) source := by
  have ready := fetchReady_of_romLoaded program source pc word loaded fetched atPc
  have actual := SailMem.run_fetch_eq_F_Base_of_isInitialized pc _ _ _ _ source
    configured.init configured.toValidMemConfig
    (by rw [Std.ExtDHashMap.get?_eq_some_get (configured.init _)] at atPc; exact Option.some.inj atPc)
    ready.access0 ready.access1 ready.aligned ready.in_range ready.align ready.not_rvc
    ready.mem0 ready.mem1 ready.mem2 ready.mem3
  rwa [word_reassemble] at actual

end SP1Clean.Advance
