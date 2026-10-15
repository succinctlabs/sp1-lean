import SP1Clean.Model.Machine.ConfiguredState

/-! # Initial-state non-vacuity examples

These concrete examples exhibit the loader relation over an empty program and a program with
real instruction and data bytes. The reusable register initializer lives in
`Model/Machine/ConfiguredState.lean`; the checked finite-image loader builds on the same state.
-/

open LeanRV64D.Defs
namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions SP1Clean.SailMem

/-- A minimal guest program (empty ROM/data, entry pc 0). Enough to exhibit that `IsInitialState` is
satisfiable; a richer program (real ROM bytes) reuses `configuredState` + adds `mem` content. -/
def emptyProgram : GuestProgram := ⟨[], 0, [], by simp, by simp, by simp, by simp⟩

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
          misa_c_disabled := (cfgState_configured 65536#64).misa_c_disabled
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
