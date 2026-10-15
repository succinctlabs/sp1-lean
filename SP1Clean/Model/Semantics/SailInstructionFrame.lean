import SP1Clean.Model.Semantics.SailArithmeticFrame
import SP1Clean.Model.Semantics.SailControlFrame
import SP1Clean.Model.Semantics.SailLoadFrame
import SP1Clean.Model.Semantics.SailStoreFrame

/-! # Supported ordinary instructions preserve the platform and protected memory

This is the circuit-independent one-step frame for the existing decoded write policy. It uses
the authoritative instruction routing projection to dispatch to arithmetic, control, load and
store proofs, without defining another supported-instruction profile.
-/

namespace SP1Clean.Advance
open LeanRV64D.Defs SP1Clean.Soundness.Target

/-- A permitted supported ordinary retirement preserves configuration and every protected byte.
The outgoing PC need not fetch unless a subsequent step executes. -/
theorem ordinary_normal_memory_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : Model.Core.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      (∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address) ∧
      ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, checked⟩ := permission
  have permitted : Model.Core.InstructionWrite.PermittedAt readOnly program source :=
    ⟨pc, word, decoded, atPc, fetched, decode, checked⟩
  have supported := (Model.Core.InstructionWrite.check_supported readOnly source.get_reg? decoded checked).2
  have liftFrame : SailConfigured target ∧ target.mem = source.mem →
      SailConfigured target ∧ (∀ address, readOnly address = true →
        target.mem.get? address = source.mem.get? address) ∧
        ∀ address, (source.mem.get? address).isSome → (target.mem.get? address).isSome := by
    rintro ⟨cfg, memory⟩
    exact ⟨cfg, fun _ _ => by rw [memory], fun _ present => by simpa only [memory] using present⟩
  unfold instructionRouteId at supported
  cases routed : instructionRouteKey decoded with
  | none => simp [routed] at supported
  | some key =>
    simp only [instructionRouteKey] at routed
    split at routed
    all_goals try first
      | exact liftFrame (arithmetic_normal_frame configured loaded atPc fetched decode trivial normal)
      | exact liftFrame (control_normal_frame configured loaded atPc fetched decode trivial normal)
      | contradiction
    · rename_i imm rs1 rd unsigned width
      rcases rs1 with ⟨rs1⟩
      rcases rd with ⟨rd⟩
      exact liftFrame (load_normal_frame configured loaded atPc fetched decode normal)
    · rename_i imm rs2 rs1 width
      rcases rs2 with ⟨rs2⟩
      rcases rs1 with ⟨rs1⟩
      exact store_normal_memory_frame configured loaded atPc fetched decode permitted normal

/-- A permitted supported ordinary retirement preserves configuration and every protected byte.
The outgoing PC need not fetch unless a subsequent step executes. -/
theorem ordinary_normal_frame {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : Model.Core.InstructionWrite.PermittedAt readOnly program source)
    (normal : SailRetiresNormally source target) :
    SailConfigured target ∧
      ∀ address, readOnly address = true → target.mem.get? address = source.mem.get? address := by
  have frame := ordinary_normal_memory_frame configured loaded permission normal
  exact ⟨frame.1, frame.2.1⟩

end SP1Clean.Advance
