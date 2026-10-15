import SP1Clean.Model.Core.ExecutionSnapshot
import SP1Clean.Model.Core.SourceSnapshot

/-! # Checking a complete local source state

The source is finite data. Its platform configuration, initialized register file, committed ROM,
and endpoint ranges are checked before grounding. The check permits a stopped host state so an
empty terminal segment remains an identity. The enclosing local verifier separately requires equal
clock endpoints for stopped sources; strict State progress then excludes active AIR rows.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs LeanRV64D.Functions SP1Clean.Soundness.Target

private instance (state : SailState) : Decidable state.isInitialized :=
  inferInstanceAs (Decidable (∀ reg : Register, reg ∈ state.regs))

private instance (state : SailState) : Decidable (SailConfigured state) :=
  if init : state.isInitialized then
    decidable_of_iff
      (state.regs.get? Register.cur_privilege == some Privilege.Machine ∧
       state.regs.get? Register.hart_state == some (HartState.HART_ACTIVE ()) ∧
       _get_Mstatus_MIE (state.regs.get Register.mstatus (init _)) = 0#1 ∧
       state.regs.get Register.mideleg (init _) = zeros ∧
       state.regs.get? Register.elp ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED) ∧
       BitVec.ofNat 1 ((state.regs.get Register.mstatus (init _)).toNat >>> 17) = 0#1 ∧
       BitVec.ofNat 1 ((state.regs.get Register.mseccfg (init _)).toNat >>> 10) = 0#1 ∧
       BitVec.ofNat 2 ((state.regs.get Register.mseccfg (init _)).toNat >>> 32) = 0#2 ∧
       state.regs.get Register.htif_tohost_base (init _) = none ∧
       state.regs.get Register.pmpcfg_n (init _) = Vector.replicate 64 0#8 ∧
       _get_Misa_M (state.regs.get Register.misa (init _)) = 1#1 ∧
       _get_Misa_C (state.regs.get Register.misa (init _)) = 0#1 ∧
       state.regs.get Register.pma_regions (init _) == [SP1Clean.SailMem.SP1_PMA_Region]) (by
      simp only [beq_iff_eq]
      constructor
      · rintro ⟨priv, active, mie, delegation, landing, mprv, security, masking, htif, pmp, misa, compressed, pma⟩
        exact ⟨init, priv, active, mie, delegation, landing, mprv, security, masking, htif, pmp, misa, compressed, pma⟩
      · intro configured
        exact ⟨configured.priv, configured.active, configured.mie, configured.mideleg,
          configured.no_landing_pad, configured.mprv_disabled, configured.mseccfg_disabled,
          configured.mseccfg_pmm, configured.htif_disabled, configured.pmp_off,
          configured.misa_m, configured.misa_c_disabled, configured.pma_regions⟩)
  else isFalse (fun configured => init configured.init)

/-- The finite carrier suffices for every platform check; the memory map is never materialized. -/
def SailSnapshot.checkConfigured (snapshot : SailSnapshot) : Bool :=
  decide (SailConfigured snapshot.skeleton)

theorem SailSnapshot.checkConfigured_iff (snapshot : SailSnapshot) :
    snapshot.checkConfigured = true ↔ SailConfigured snapshot.realize := by
  rw [checkConfigured, decide_eq_true_eq]
  constructor
  · exact fun configured => configured_with_memory configured _
  · intro configured
    exact configured_with_memory configured ∅

/-- The finite PC observation; successful source validation proves the key is present. -/
def ExecutionSnapshot.pc (source : ExecutionSnapshot) : BitVec 64 :=
  (source.sail.registers.get? Register.PC).getD 0

/-- Static source conditions shared by the local verifier and its execution interpretation.
Host state and Sail bookkeeping remain the supplied values, without a per-shard reset. -/
def ExecutionSourceValid (image : ProgramImage) (source : ExecutionSnapshot) : Prop :=
  SourceValid image source.sail.memorySnapshot ∧ SailConfigured source.sail.skeleton ∧
    source.clock < 2 ^ 48 ∧ source.pc.toNat < 2 ^ 48

def checkExecutionSource (image : ProgramImage) (source : ExecutionSnapshot) : Bool :=
  checkSource image source.sail.memorySnapshot && source.sail.checkConfigured &&
    decide (source.clock < 2 ^ 48) && decide (source.pc.toNat < 2 ^ 48)

theorem checkExecutionSource_iff (image : ProgramImage) (source : ExecutionSnapshot) :
    checkExecutionSource image source = true ↔ ExecutionSourceValid image source := by
  simp only [checkExecutionSource, ExecutionSourceValid, Bool.and_eq_true,
    checkSource_iff, SailSnapshot.checkConfigured, decide_eq_true_eq, and_assoc]

theorem ExecutionSourceValid.configured {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : ExecutionSourceValid image source) : SailConfigured source.sail.realize :=
  configured_with_memory valid.2.1 _

theorem ExecutionSourceValid.memory {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : ExecutionSourceValid image source) :
    source.sail.memorySnapshot.Realizes source.sail.realize :=
  source.sail.memorySnapshot_realizes valid.2.1.init

theorem ExecutionSourceValid.pc {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : ExecutionSourceValid image source) :
    source.sail.realize.regs.get? Register.PC = some source.pc := by
  have present := Std.ExtDHashMap.get?_eq_some_get (valid.2.1.init Register.PC)
  change source.sail.registers.get? Register.PC = some ((source.sail.registers.get? Register.PC).getD 0)
  change source.sail.registers.get? Register.PC = _ at present
  rw [present]
  rfl

theorem ExecutionSourceValid.romLoaded {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : ExecutionSourceValid image source) :
    RomLoaded (image.toGuestProgram valid.1.1) source.sail.realize :=
  valid.1.romLoaded valid.memory

end SP1Clean.Model.Core
