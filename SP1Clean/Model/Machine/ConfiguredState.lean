import SP1Clean.Model.Machine.Execution
import ToMathlib.ExtDHashMapOfFintype
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases

/-! # Canonical SP1 register initialization

Every Sail register is initialized, integer registers start at zero, and the platform registers
select the configured SP1 machine mode and memory region. This construction is shared by the
checked program loader and the concrete execution witnesses. It was previously local to the
non-vacuity examples; keeping it in the Model layer lets the execution model own its boot state.
-/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions SP1Clean.SailMem

-- All `Register` constructors are enumerable — derived so `Finset.univ` enumerates them.
-- The derivation recurses once per `Register` constructor, so it just misses the 512 default;
-- ladder-measured, 512 fails and 600 passes — floor bracket (512, 600], set here with slack.
-- The former file-wide 100000 stamp was ~150x over and covered the whole file; nothing else here
-- needs any budget.
set_option maxRecDepth 800 in
-- Mathlib's `Fintype` deriving handler closes its `complete` field with `rw [Finset.mem_mk, …]` on
-- a `Finset.mk ↑enumList enumList_nodup` whose `nodup` field is well-typed only up to unfolding
-- `Multiset.Nodup`; under v4.33's transparency-respecting unifier that `rw` fails for every enum,
-- and Mathlib's own `MathlibTest/DeriveFintype.lean` disables the check around each derive exactly
-- like this.
set_option backward.isDefEq.respectTransparency false in
deriving instance Fintype for Register

/-- Every register's value type is inhabited, so a register can be default-filled. -/
def regDefault : (r : Register) → RegisterType r := fun r => by cases r <;> exact default

/-- The fully initialized register map: every register present, holding its `default` value.
The finite fold is executable; proofs use its lookup lemmas to avoid normalizing the whole map. -/
@[irreducible] def fullRegs : Std.ExtDHashMap Register RegisterType := Std.ExtDHashMap.ofFintype regDefault

/-- Every register is a key of `fullRegs`. -/
lemma mem_fullRegs (r : Register) : r ∈ fullRegs := by
  have present : fullRegs.get? r = some (regDefault r) := by
    unfold fullRegs
    exact Std.ExtDHashMap.get?_ofFintype _ _
  exact Std.ExtDHashMap.mem_iff_isSome_get?.mpr (Option.isSome_of_eq_some present)

/-- Each register's value in `fullRegs` is its `default`, independently of insertion order. -/
lemma get?_fullRegs (r : Register) : fullRegs.get? r = some (regDefault r) := by
  unfold fullRegs
  exact Std.ExtDHashMap.get?_ofFintype _ _

/-- A runnable initial Sail state: every register initialized, PC pinned to `pc`, machine mode, and the
SP1 PMA region configured (the one non-default the strengthened `SailConfigured` requires). -/
def configuredState (pc : BitVec 64) : SailState :=
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
         misa_c_disabled := by rw [cfgState_misa pc _]; decide
         pma_regions := cfgState_pma pc _ }

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

end SP1Clean.Soundness.Target
