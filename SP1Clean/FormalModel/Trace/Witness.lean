import SP1Clean.Model.Semantics.GuestProgram

/-! # W6b — the non-vacuity witness: `IsInitialState` is satisfiable

The target theorem (`Soundness/TargetVm.lean`) is `∀ s0, IsInitialState prog s0 → …`; a vacuous
`IsInitialState` would make it trivially true. This file exhibits a concrete configured, fully-initialized
Sail state and a guest program it loads, proving `IsInitialState` is **satisfiable** (axiom-clean).

The reusable machinery is `configuredState pc` — a state with **every** register present
(`cfgState_init`: the `isInitialized` requirement, all `Register` constructors), the program counter pinned
to `pc` (`cfgState_pc`), `cur_privilege = Machine` (`cfgState_priv`), and the SP1 PMA region set up
(`pma_regions = [SP1_PMA_Region]`). Built by folding `insert` over `Finset.univ` (`Fintype Register` is
derived here) with each register's `default` value (every `RegisterType r` is `Inhabited`), overriding
`PC`/`cur_privilege`/`pma_regions`. Every other register's `default` already satisfies the (strengthened)
`SailConfigured` — `hart_state = HART_ACTIVE`, `mstatus.MIE = 0`, `mideleg = zeros`, `htif = none`,
`elp ≠ LP_EXPECTED`, the `mprv`/`mseccfg` disable bits clear — so only `pma_regions` (default `[]`) needs an
explicit override. Enriching the witness to a non-empty ROM (real instruction bytes loaded into `mem`, so
`romLoaded` carries content) reuses `configuredState` and adds the byte-level `mem` lookups. -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions SP1Clean.SailMem

set_option maxRecDepth 100000

-- All `Register` constructors are enumerable — derived so `Finset.univ` enumerates them.
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
    regs := ((fullRegs.insert Register.PC pc).insert Register.cur_privilege Privilege.Machine).insert
      Register.pma_regions [SP1_PMA_Region] }

lemma cfgState_init (pc : BitVec 64) : (configuredState pc).isInitialized := by
  intro reg
  simp only [configuredState, Std.ExtDHashMap.mem_insert]
  exact Or.inr (Or.inr (Or.inr (mem_fullRegs reg)))

lemma cfgState_pc (pc : BitVec 64) : (configuredState pc).regs.get? Register.PC = some pc := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide), Std.ExtDHashMap.get?_insert, dif_neg (by decide),
    Std.ExtDHashMap.get?_insert_self]

lemma cfgState_priv (pc : BitVec 64) :
    (configuredState pc).regs.get? Register.cur_privilege = some Privilege.Machine := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide), Std.ExtDHashMap.get?_insert_self]

/-- Any register other than the three overridden ones keeps its `fullRegs` default in `configuredState`. -/
lemma cfgState_get?_other (pc : BitVec 64) (reg : Register)
    (h1 : reg ≠ Register.PC) (h2 : reg ≠ Register.cur_privilege) (h3 : reg ≠ Register.pma_regions) :
    (configuredState pc).regs.get? reg = some (regDefault reg) := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h3 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h2 (beq_iff_eq.mp hc).symm),
      Std.ExtDHashMap.get?_insert, dif_neg (fun hc => h1 (beq_iff_eq.mp hc).symm)]
  exact get?_fullRegs reg

/-- The `.get` form of `cfgState_get?_other` (for the `isValidMemConfig`/`mie`/`mideleg` fields, which read
the value with a membership proof). -/
lemma cfgState_get_other (pc : BitVec 64) (reg : Register)
    (h1 : reg ≠ Register.PC) (h2 : reg ≠ Register.cur_privilege) (h3 : reg ≠ Register.pma_regions)
    (hmem : reg ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get reg hmem = regDefault reg := by
  have h := cfgState_get?_other pc reg h1 h2 h3
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

lemma cfgState_pma (pc : BitVec 64) (hmem : Register.pma_regions ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get Register.pma_regions hmem = [SP1_PMA_Region] := by
  have h : (configuredState pc).regs.get? Register.pma_regions = some [SP1_PMA_Region] := by
    simp only [configuredState, Std.ExtDHashMap.get?_insert_self]
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

lemma cfgState_curpriv_get (pc : BitVec 64) (hmem : Register.cur_privilege ∈ (configuredState pc).regs) :
    (configuredState pc).regs.get Register.cur_privilege hmem = Privilege.Machine := by
  have h := cfgState_priv pc
  rwa [Std.ExtDHashMap.get?_eq_some_get hmem, Option.some_inj] at h

/-- A minimal guest program (empty ROM/data, entry pc 0). Enough to exhibit that `IsInitialState` is
satisfiable; a richer program (real ROM bytes) reuses `configuredState` + adds `mem` content. -/
def emptyProgram : GuestProgram := ⟨[], 0, [], by simp, by simp⟩

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
     configured :=
       { init := cfgState_init 0
         priv := cfgState_priv 0
         active := by
           rw [cfgState_get?_other 0 Register.hart_state (by decide) (by decide) (by decide)]; rfl
         mie := by
           rw [cfgState_get_other 0 Register.mstatus (by decide) (by decide) (by decide)]
           exact (by decide : _get_Mstatus_MIE (default : RegisterType Register.mstatus) = 0#1)
         mideleg := by
           rw [cfgState_get_other 0 Register.mideleg (by decide) (by decide) (by decide)]
           exact (by decide : (default : RegisterType Register.mideleg) = zeros)
         no_landing_pad := by
           rw [cfgState_get?_other 0 Register.elp (by decide) (by decide) (by decide)]
           exact (by decide : ¬ (some (default : RegisterType Register.elp)
             = some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)))
         memcfg :=
           { h_cur_privilege := cfgState_curpriv_get 0 _
             h_mprv_disabled := by
               rw [cfgState_get_other 0 Register.mstatus (by decide) (by decide) (by decide)]
               exact (by decide :
                 BitVec.ofNat 1 ((default : RegisterType Register.mstatus).toNat >>> 17) = 0#1)
             h_mseccfg_disabled := by
               rw [cfgState_get_other 0 Register.mseccfg (by decide) (by decide) (by decide)]
               exact (by decide :
                 BitVec.ofNat 1 ((default : RegisterType Register.mseccfg).toNat >>> 10) = 0#1)
             h_htif_disabled := by
               rw [cfgState_get_other 0 Register.htif_tohost_base (by decide) (by decide) (by decide)]
               exact (by decide : (default : RegisterType Register.htif_tohost_base) = none)
             h_pma_regions := cfgState_pma 0 _ } } }⟩

end SP1Clean.Soundness.Target
