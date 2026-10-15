import SP1Clean.Soundness.SyscallWiring

/-! # Ordinary replay guards from committed decoding

An instruction-chip Program row is a supported official Sail decode. It therefore fetches code
outside the reserved HALT address and cannot decode ECALL. These state-local facts discharge the
ordinary replay guard without assuming an execution step or inspecting instruction cases.
-/

namespace SP1Clean.Soundness

open Target SP1Clean.Semantics LeanRV64D LeanRV64D.Defs LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- The instruction-chip projection cannot be the officially decoded ECALL word. -/
theorem Target.decodedInROM.notEcall {program : GuestProgram} {row : ProgramChip.ProgramRow (ZMod p)}
    (decoded : decodedInROM program row) {state : SailState}
    (configured : SailConfigured state)
    (atPc : state.regs.get? Register.PC = some (pcBitsOfRow row)) :
    ¬ Machine.AboutToExecuteEcall program state := by
  rintro ⟨pc, pcEq, fetch⟩
  have same : pc = pcBitsOfRow row := Option.some.inj (pcEq.symm.trans atPc)
  rw [same] at fetch
  obtain ⟨word, instruction, fetched, decode, projected⟩ := decoded
  have wordEq : word = ECALL_ENC := Option.some.inj (fetched.symm.trans fetch)
  have actual : (ext_decode ECALL_ENC).run state = .ok (.ECALL ()) state := by
    simpa [ECALL_ENC] using SailDecode.decode_ECALL state configured.init configured.priv configured.mseccfg_disabled
  have decodedAt := decode state configured
  rw [wordEq, actual] at decodedAt
  have instructionEq : instruction = .ECALL () := by
    injection decodedAt with same
    exact same.symm
  rw [instructionEq] at projected
  simp [instrToProgramRow', instrToProgramRow] at projected

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- State and Program messages use the same incoming PC in the shared row view. -/
theorem program_pc_eq_statePull (view : Trace.RowView (ZMod p)) :
    pcBitsOfRow (programAccess view).toRow = StateMsg.pcBits (statePullOfView view) := by
  rfl

end SP1Clean.Soundness
