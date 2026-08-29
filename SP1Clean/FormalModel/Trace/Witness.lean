import SP1Clean.Model.Machine.Execution
import SP1Clean.Model.Semantics.GuestProgram

/-! # W6b — the non-vacuity witness: `IsInitialState` is satisfiable

The capstone's boundary bundle (`InitialBoundaryFacts`, `Soundness/ProviderBindings.lean`) demands an
initial Sail state that loads the program and is configured; a vacuous `IsInitialState` would make every
such hypothesis unsatisfiable-vacuous. This file exhibits a concrete configured, fully-initialized
Sail state and a guest program it loads, proving `IsInitialState` is **satisfiable** (axiom-clean).

The reusable machinery is `configuredState pc` — a state with **every** register present
(`cfgState_init`: the `isInitialized` requirement, all `Register` constructors), the program counter pinned
to `pc` (`cfgState_pc`), `cur_privilege = Machine` (`cfgState_priv`), and the SP1 PMA region set up
(`pma_regions = [SP1_PMA_Region]`). Built by folding `insert` over `Finset.univ` (`Fintype Register` is
derived here) with each register's `default` value (every `RegisterType r` is `Inhabited`), overriding
`PC`/`cur_privilege`/`pma_regions`/`misa` (M set). Every other register's `default` already satisfies the (strengthened)
`SailConfigured` — `hart_state = HART_ACTIVE`, `mstatus.MIE = 0`, `mideleg = zeros`, `htif = none`,
`elp ≠ LP_EXPECTED`, the `mprv`/`mseccfg` disable bits clear — so only `pma_regions` (default `[]`) needs an
explicit override. Enriching the witness to a non-empty ROM (real instruction bytes loaded into `mem`, so
`romLoaded` carries content) reuses `configuredState` and adds the byte-level `mem` lookups. -/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions SP1Clean.SailMem

-- All `Register` constructors are enumerable — derived so `Finset.univ` enumerates them.
-- The derivation recurses once per `Register` constructor, so it just misses the 512 default;
-- ladder-measured, 512 fails and 600 passes — floor bracket (512, 600], set here with slack.
-- The former file-wide 100000 stamp was ~150x over and covered the whole file; nothing else here
-- needs any budget.
set_option maxRecDepth 800 in
deriving instance Fintype for Register

/-- Every register's value type is inhabited, so a register can be default-filled. -/
noncomputable def regDefault : (r : Register) → RegisterType r := fun r => by cases r <;> exact default

/-- The fully-initialized register map: every register present, holding its `default` value. -/
noncomputable def fullRegs : Std.ExtDHashMap Register RegisterType :=
  (Finset.univ : Finset Register).toList.foldr
    (fun r (m : Std.ExtDHashMap Register RegisterType) => m.insert r (regDefault r)) ∅

private lemma mem_foldr_insert {l : List Register} {r : Register} (h : r ∈ l) :
    r ∈ l.foldr (fun r (m : Std.ExtDHashMap Register RegisterType) => m.insert r (regDefault r)) ∅ := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.foldr_cons, Std.ExtDHashMap.mem_insert]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Or.inl (by simp)
    · exact Or.inr (ih hmem)

/-- Every register is a key of `fullRegs` (`r ∈ univ`, and the fold inserts every list element). -/
lemma mem_fullRegs (r : Register) : r ∈ fullRegs :=
  mem_foldr_insert (Finset.mem_toList.mpr (Finset.mem_univ r))

private lemma get?_foldr_insert {l : List Register} {r : Register} (h : r ∈ l) :
    (l.foldr (fun r (m : Std.ExtDHashMap Register RegisterType) => m.insert r (regDefault r)) ∅).get? r
      = some (regDefault r) := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · rw [Std.ExtDHashMap.get?_insert_self]
    · rw [Std.ExtDHashMap.get?_insert]
      split
      · rename_i hEq; obtain rfl := beq_iff_eq.mp hEq; simp
      · exact ih hmem

/-- Each register's value in `fullRegs` is its `default` (the fold inserts `regDefault r` for every `r`,
and each key is inserted with that same value, so whichever insert wins the value is `regDefault r`). -/
lemma get?_fullRegs (r : Register) : fullRegs.get? r = some (regDefault r) :=
  get?_foldr_insert (Finset.mem_toList.mpr (Finset.mem_univ r))

/-- A runnable initial Sail state: every register initialized, PC pinned to `pc`, machine mode, and the
SP1 PMA region configured (the one non-default the strengthened `SailConfigured` requires). -/
noncomputable def configuredState (pc : BitVec 64) : SailState :=
  { (default : SailState) with
    regs := (((fullRegs.insert Register.misa 4096#64).insert Register.PC pc).insert
      Register.cur_privilege Privilege.Machine).insert
      Register.pma_regions [SP1_PMA_Region] }

lemma cfgState_init (pc : BitVec 64) : (configuredState pc).isInitialized := by
  intro reg
  simp only [configuredState, Std.ExtDHashMap.mem_insert]
  exact Or.inr (Or.inr (Or.inr (Or.inr (mem_fullRegs reg))))

lemma cfgState_pc (pc : BitVec 64) : (configuredState pc).regs.get? Register.PC = some pc := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide), Std.ExtDHashMap.get?_insert,
    dif_neg (by decide), Std.ExtDHashMap.get?_insert_self]

lemma cfgState_priv (pc : BitVec 64) :
    (configuredState pc).regs.get? Register.cur_privilege = some Privilege.Machine := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide), Std.ExtDHashMap.get?_insert_self]

/-- Any register other than the four overridden ones keeps its `fullRegs` default in `configuredState`. -/
lemma cfgState_get?_other (pc : BitVec 64) (reg : Register)
    (h1 : reg ≠ Register.PC) (h2 : reg ≠ Register.cur_privilege) (h3 : reg ≠ Register.pma_regions)
    (h4 : reg ≠ Register.misa) :
    (configuredState pc).regs.get? reg = some (regDefault reg) := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h3 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h4 (beq_iff_eq.mp hc).symm)]
  exact get?_fullRegs reg

/-- The `.get` form of `cfgState_get?_other` (for the `isValidMemConfig`/`mie`/`mideleg` fields, which read
the value with a membership proof). -/
lemma cfgState_get_other (pc : BitVec 64) (reg : Register)
    (h1 : reg ≠ Register.PC) (h2 : reg ≠ Register.cur_privilege) (h3 : reg ≠ Register.pma_regions)
    (h4 : reg ≠ Register.misa)
    (hmem : reg ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get reg hmem = regDefault reg := by
  have h := cfgState_get?_other pc reg h1 h2 h3 h4
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

lemma cfgState_pma (pc : BitVec 64) (hmem : Register.pma_regions ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get Register.pma_regions hmem = [SP1_PMA_Region] := by
  have h : (configuredState pc).regs.get? Register.pma_regions = some [SP1_PMA_Region] := by
    simp only [configuredState, Std.ExtDHashMap.get?_insert_self]
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

/-- The overridden `misa` value: M enabled (bit 12), the `SailConfigured.misa_m` residue. Only the
M bit is read on any proved path (`currentlyEnabled Ext_M`); the other extension bits stay clear. -/
lemma cfgState_misa (pc : BitVec 64) (hmem : Register.misa ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get Register.misa hmem = 4096#64 := by
  have h : (configuredState pc).regs.get? Register.misa = some (4096#64) := by
    simp only [configuredState]
    rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide),
        Std.ExtDHashMap.get?_insert, dif_neg (by decide),
        Std.ExtDHashMap.get?_insert, dif_neg (by decide),
        Std.ExtDHashMap.get?_insert_self]
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

/-- A minimal guest program (empty ROM/data, entry pc 0). Enough to exhibit that `IsInitialState` is
satisfiable; a richer program (real ROM bytes) reuses `configuredState` + adds `mem` content. -/
def emptyProgram : GuestProgram := ⟨[], 0, [], by simp, by simp, by simp, by simp⟩

/-- The configured core state satisfies the whole strengthened `SailConfigured` at any pc:
`init`/`priv`/`active`/`mie`/`mideleg`/`no_landing_pad` from the register defaults, and
the memory configuration from the overridden `pma_regions` + the disable-bit defaults. -/
theorem cfgState_configured (pc : BitVec 64) : SailConfigured (configuredState pc) :=
       { init := cfgState_init pc
         priv := cfgState_priv pc
         active := by
           rw [cfgState_get?_other pc Register.hart_state (by decide) (by decide) (by decide) (by decide)]; rfl
         mie := by
           rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
           exact (by decide : _get_Mstatus_MIE (default : RegisterType Register.mstatus) = 0#1)
         mideleg := by
           rw [cfgState_get_other pc Register.mideleg (by decide) (by decide) (by decide) (by decide)]
           exact (by decide : (default : RegisterType Register.mideleg) = zeros)
         no_landing_pad := by
           rw [cfgState_get?_other pc Register.elp (by decide) (by decide) (by decide) (by decide)]
           exact (by decide : ¬ (some (default : RegisterType Register.elp)
             = some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)))
         mprv_disabled := by
           rw [cfgState_get_other pc Register.mstatus (by decide) (by decide) (by decide) (by decide)]
           exact (by decide :
             BitVec.ofNat 1 ((default : RegisterType Register.mstatus).toNat >>> 17) = 0#1)
         mseccfg_disabled := by
           rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
           exact (by decide :
             BitVec.ofNat 1 ((default : RegisterType Register.mseccfg).toNat >>> 10) = 0#1)
         mseccfg_pmm := by
           rw [cfgState_get_other pc Register.mseccfg (by decide) (by decide) (by decide) (by decide)]
           exact (by decide :
             BitVec.ofNat 2 ((default : RegisterType Register.mseccfg).toNat >>> 32) = 0#2)
         htif_disabled := by
           rw [cfgState_get_other pc Register.htif_tohost_base (by decide) (by decide) (by decide) (by decide)]
           exact (by decide : (default : RegisterType Register.htif_tohost_base) = none)
         pmp_off := by
           rw [cfgState_get_other pc Register.pmpcfg_n (by decide) (by decide) (by decide) (by decide)]
           exact (by decide :
             (default : RegisterType Register.pmpcfg_n) = Vector.replicate 64 0#8)
         misa_m := by rw [cfgState_misa pc _]; decide
         pma_regions := cfgState_pma pc _ }

/-- **The W6b non-vacuity witness.** `IsInitialState` is satisfiable: the configured initial state loads
the (minimal) guest program. So the target theorem's universally-quantified hypothesis is not vacuous. The
`configured` field discharges the whole strengthened `SailConfigured`: `init`/`priv`/`active`/`mie`/
`mideleg`/`no_landing_pad` from the register defaults, and `memcfg` (`isValidMemConfig`) from the
overridden `pma_regions` + the disable-bit defaults. -/
theorem isInitialState_nonvacuous : ∃ s0, IsInitialState emptyProgram s0 :=
  ⟨configuredState 0,
   { initialized := cfgState_init 0
     pc := cfgState_pc 0
     romLoaded := by intro a w hf; simp [emptyProgram, GuestProgram.fetchWord] at hf
     imageLoaded := by intro av hav; simp [emptyProgram] at hav
     configured := cfgState_configured 0 }⟩

/-! ## The loaded boot witness

The enrichment the file header promises: a program with a real instruction word and a real
data-image byte, loaded into memory byte by byte, whose configured state also carries SP1's
zeroed integer register file — the joint satisfiability core of `BootBoundaryFacts`
(`Soundness/ProviderBindings.lean`). -/

/-- One real instruction — `ADDI x0, x0, 0` (encoding `0x00000013`) — at the bottom of the SP1
code window, plus one data-image byte above it. -/
def oneInstrProgram : GuestProgram where
  rom := [(65536#64, 0x00000013#32)]
  pc_start := 65536#64
  memImage := [(131072#64, 0xAB#8)]
  rom_nodup := by simp
  rom_aligned := by intro a ha; simp at ha; subst ha; decide
  rom_in_window := by intro aw haw; simp at haw; subst haw; decide
  rom_full_width := by intro aw haw; simp at haw; subst haw; decide

/-- The configured core with `oneInstrProgram`'s four ROM bytes and one image byte in memory. -/
noncomputable def loadedState : SailState :=
  { configuredState 65536#64 with
    mem := ((((((∅ : Std.ExtHashMap ℕ (BitVec 8)).insert 65536 0x13#8).insert
      65537 0x00#8).insert 65538 0x00#8).insert 65539 0x00#8).insert 131072 0xAB#8) }

/-- Every `x`-register index maps away from the four registers `configuredState` overrides. -/
private lemma reg_idx_ne_overrides : ∀ idx : BitVec 5,
    reg_idx_to_Register idx ≠ Register.PC ∧
    reg_idx_to_Register idx ≠ Register.cur_privilege ∧
    reg_idx_to_Register idx ≠ Register.pma_regions ∧
    reg_idx_to_Register idx ≠ Register.misa := by
  decide

/-- The default value of every `x`-register, transported to its 64-bit form, is zero. -/
private lemma regDefault_reg_idx (idx : BitVec 5) :
    (reg_idx_must_64 idx ▸
      (some (regDefault (reg_idx_to_Register idx)) :
        Option (RegisterType (reg_idx_to_Register idx))) : Option (BitVec 64)) = some 0 := by
  obtain ⟨⟨n, hn⟩⟩ := idx
  interval_cases n <;> rfl

/-- SP1's zeroed integer register file holds on the configured core: `x0` is hardwired and every
other `x`-register keeps its (zero) default. -/
theorem registersZero_configuredState (pc : BitVec 64) :
    SP1Clean.Machine.RegistersZero (configuredState pc) := by
  intro idx
  by_cases h0 : idx = 0
  · simp [SailState.get_reg?, h0]
  · rw [SailState.get_reg?, if_neg h0]
    have hne := reg_idx_ne_overrides idx
    rw [cfgState_get?_other pc _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2]
    exact regDefault_reg_idx idx

/-- **The loaded boot witness**: `IsInitialState` over a program with real ROM and image content,
jointly with SP1's zeroed register file. -/
theorem isInitialState_nonvacuous_loaded :
    ∃ s0, IsInitialState oneInstrProgram s0 ∧ SP1Clean.Machine.RegistersZero s0 := by
  refine ⟨loadedState,
    { initialized := cfgState_init 65536#64
      pc := cfgState_pc 65536#64
      romLoaded := ?_
      imageLoaded := ?_
      configured :=
        { init := (cfgState_configured 65536#64).init
          priv := (cfgState_configured 65536#64).priv
          active := (cfgState_configured 65536#64).active
          mie := (cfgState_configured 65536#64).mie
          mideleg := (cfgState_configured 65536#64).mideleg
          no_landing_pad := (cfgState_configured 65536#64).no_landing_pad
          mprv_disabled := (cfgState_configured 65536#64).mprv_disabled
          mseccfg_disabled := (cfgState_configured 65536#64).mseccfg_disabled
          mseccfg_pmm := (cfgState_configured 65536#64).mseccfg_pmm
          htif_disabled := (cfgState_configured 65536#64).htif_disabled
          pmp_off := (cfgState_configured 65536#64).pmp_off
          misa_m := (cfgState_configured 65536#64).misa_m
          pma_regions := (cfgState_configured 65536#64).pma_regions } },
    registersZero_configuredState 65536#64⟩
  · intro a w hf i
    unfold GuestProgram.fetchWord oneInstrProgram at hf
    simp only [List.find?] at hf
    rcases hcond : ((65536#64, 0x00000013#32).1 == a) with - | -
    · rw [hcond] at hf
      simp at hf
    · rw [hcond] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      obtain rfl : a = 65536#64 := by
        have := (beq_iff_eq).mp hcond
        simpa using this.symm
      subst hf
      fin_cases i <;>
        · simp only [loadedState, Std.ExtHashMap.get?_eq_getElem?,
            Std.ExtHashMap.getElem?_insert]
          decide
  · intro av hav
    simp only [oneInstrProgram, List.mem_singleton] at hav
    subst hav
    simp only [loadedState, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    decide

end SP1Clean.Soundness.Target
