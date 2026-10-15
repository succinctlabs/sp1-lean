import SP1Clean.Model.Semantics.SailInstructionFrame
import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Proofs.Sail.Advance
import SP1Clean.Proofs.Sail.InstructionDecode

/-! # Independent memory preservation regressions

Finite checked sources and official execute lemmas construct actual normal retirements. The
common independent frame theorem then preserves protected bytes without a circuit row. Separate
split anchors exercise the real misaligned splitter; policy anchors reject a protected last byte
and same-value ROM stores. Native evaluation is confined to finite source data and permissions.
-/

namespace SP1CleanTest.Core.MemoryFrame
open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target
open Sail LeanRV64D.Defs LeanRV64D.Functions

private def image (word : BitVec 32) : ProgramImage := ⟨[(65536, word)], 65536, []⟩

private def source (word : BitVec 32) (base data : BitVec 64) : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x2 base).insert .x3 data
            memory := (image word).initialMemory }
  host := {}
  clock := 17

private theorem source_base (word : BitVec 32) (base data : BitVec 64) :
    (source word base data).sail.realize.get_reg? 2 = some base := by
  change (((configuredState 65536).regs.insert .x2 base).insert .x3 data).get? .x2 = some base
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte, cast_eq]

private theorem source_data (word : BitVec 32) (base data : BitVec 64) :
    (source word base data).sail.realize.get_reg? 3 = some data := by
  change (((configuredState 65536).regs.insert .x2 base).insert .x3 data).get? .x3 = some data
  exact Std.ExtDHashMap.get?_insert_self

private def RetiresWithFrame (word : BitVec 32) (base data : BitVec 64) (readOnly : ℕ → Bool) : Prop :=
  ∃ target, SailRetiresNormally (source word base data).sail.realize target ∧ SailConfigured target ∧
    ∀ address, readOnly address = true →
      target.mem.get? address = (source word base data).sail.realize.mem.get? address

private theorem check_of_registers (left right : SailState) (equal : left.regs = right.regs)
    (readOnly : ℕ → Bool) (decoded : instruction)
    (checked : InstructionWrite.check readOnly left.get_reg? decoded = true) :
    InstructionWrite.check readOnly right.get_reg? decoded = true := by
  have registers : left.get_reg? = right.get_reg? := by
    funext index
    simp only [SailState.get_reg?, equal]
  rw [← registers]
  exact checked

private theorem retires_from_state (initial : SailState) (program : GuestProgram)
    (word : BitVec 32) (base data : BitVec 64) (readOnly : ℕ → Bool) (decoded : instruction)
    (configured : SailConfigured initial) (loaded : RomLoaded program initial)
    (atPc : initial.regs.get? Register.PC = some 65536)
    (fetched : program.fetchWord 65536 = some word)
    (decode : ConfiguredDecode word decoded)
    (allowed : InstructionWrite.check readOnly initial.get_reg? decoded = true)
    (baseValue : initial.get_reg? 2 = some base) (dataValue : initial.get_reg? 3 = some data)
    (executeFrame : ∀ state, SailConfigured state → state.get_reg? 2 = some base →
      state.get_reg? 3 = some data →
      (∀ index : Fin 4, state.mem.get? (65536 + index) = some (word.extractLsb' (8 * index) 8)) →
      ∃ next, (execute decoded).run state = .ok (.Retire_Success ()) next ∧ SailConfigured next) :
    ∃ target, SailRetiresNormally initial target ∧ SailConfigured target ∧
      ∀ address, readOnly address = true → target.mem.get? address = initial.mem.get? address := by
  have permission : InstructionWrite.PermittedAt readOnly program initial :=
    ⟨65536, word, decoded, atPc, fetched, decode, allowed⟩
  obtain ⟨target, normal, _⟩ := Advance.retire_memory_of_observed_execute
    configured loaded atPc fetched decode (fun _ => True) (by
      intro state cfg registers memory _ _
      obtain ⟨next, ran, nextCfg⟩ := executeFrame state cfg
        ((registers 2).trans baseValue) ((registers 3).trans dataValue) (by
          intro index
          rw [memory]
          exact loaded _ _ fetched index)
      exact ⟨next, ran, nextCfg, trivial⟩)
  exact ⟨target, normal, Advance.ordinary_normal_frame configured loaded permission normal⟩

private theorem retires (word : BitVec 32) (base data : BitVec 64) (readOnly : ℕ → Bool)
    (decoded : instruction) (checked : checkExecutionSource (image word) (source word base data) = true)
    (parsed : InstructionDecode.decode word = some decoded)
    (allowed : InstructionWrite.check readOnly (source word base data).sail.skeleton.get_reg? decoded = true)
    (executeFrame : ∀ state, SailConfigured state → state.get_reg? 2 = some base →
      state.get_reg? 3 = some data →
      (∀ index : Fin 4, state.mem.get? (65536 + index) = some (word.extractLsb' (8 * index) 8)) →
      ∃ next, (execute decoded).run state = .ok (.Retire_Success ()) next ∧ SailConfigured next) :
    RetiresWithFrame word base data readOnly := by
  have valid := (checkExecutionSource_iff _ _).mp checked
  have atPc : (source word base data).sail.realize.regs.get? Register.PC = some 65536 := by
    change (((configuredState 65536).regs.insert .x2 base).insert .x3 data).get? .PC = some 65536
    simp only [configuredState, Std.ExtDHashMap.get?_insert, beq_iff_eq,
      reduceCtorEq, ↓reduceDIte, cast_eq]
  have fetched : ((image word).toGuestProgram valid.1.1).fetchWord 65536 = some word := rfl
  exact retires_from_state _ _ word base data readOnly decoded valid.configured valid.romLoaded atPc
    fetched (SailDecode.instructionDecode_agrees word decoded parsed)
    (check_of_registers (source word base data).sail.skeleton (source word base data).sail.realize
      rfl _ _ allowed) (source_base word base data) (source_data word base data) executeFrame

/-- A signed LB may read the protected code byte and preserves every byte. -/
theorem signedByteLoad : RetiresWithFrame 0x00010083 65536 0 (fun _ => true) := by
  apply retires _ _ _ _ (.LOAD (0, .Regidx 2, .Regidx 1, false, 1)) (by native_decide) rfl (by native_decide)
  intro state cfg base _ bytes
  have ran := Advance.execute_LOAD_reaches_width1 0 2 1 false 65536 0x83 state cfg.init
    cfg.toValidMemConfig base (by decide) (by decide) (bytes 0)
  exact ⟨_, ran, (Advance.load_execute_frame state cfg _ _ _ _ _ _ _ ran).2.1⟩

/-- LW to x0 still executes the memory read and preserves every byte. -/
theorem loadToZero : RetiresWithFrame 0x00012003 65536 0 (fun _ => true) := by
  apply retires _ _ _ _ (.LOAD (0, .Regidx 2, .Regidx 0, false, 4)) (by native_decide) rfl (by native_decide)
  intro state cfg base _ bytes
  have ran := Advance.execute_LOAD_reaches_width4 0 2 0 false 65536 3 0x20 1 0 state cfg.init
    cfg.toValidMemConfig base (by decide) (by decide) (by decide)
    (bytes 0) (bytes 1) (bytes 2) (bytes 3)
  exact ⟨_, ran, (Advance.load_execute_frame state cfg _ _ _ _ _ _ _ ran).2.1⟩

/-- SB beside ROM may write a different byte in the same eight-byte cell. -/
theorem byteStoreBesideRom : RetiresWithFrame 0x00310023 65540 42 (image 0x00310023).readOnly := by
  apply retires _ _ _ _ (.STORE (0, .Regidx 3, .Regidx 2, 1)) (by native_decide) rfl (by native_decide)
  intro state cfg base data _
  have ran := Advance.execute_STORE_reaches 0 2 3 65540 42 state cfg.init cfg.toValidMemConfig
    base data (by decide) (by decide)
  exact ⟨_, ran, configured_with_memory cfg _⟩

/-- SH preserves the protected half of a partially writable eight-byte cell. -/
theorem halfStoreBesideRom : RetiresWithFrame 0x00311023 65540 0xabcd (image 0x00311023).readOnly := by
  apply retires _ _ _ _ (.STORE (0, .Regidx 3, .Regidx 2, 2)) (by native_decide) rfl (by native_decide)
  intro state cfg base data _
  have ran := Advance.execute_STORE_reaches_width2 0 2 3 65540 0xabcd state cfg.init cfg.toValidMemConfig
    base data (by decide) (by decide)
  exact ⟨_, ran, configured_with_memory cfg _⟩

/-- SW uses the signed immediate when checking and preserving the protected interval. -/
theorem wordStoreNegativeOffset :
    RetiresWithFrame 0xfe312e23 65544 0x12345678 (image 0xfe312e23).readOnly := by
  apply retires _ _ _ _ (.STORE (0xffc, .Regidx 3, .Regidx 2, 4)) (by native_decide) rfl (by native_decide)
  intro state cfg base data _
  have ran := Advance.execute_STORE_reaches_width4 0xffc 2 3 65544 0x12345678 state cfg.init cfg.toValidMemConfig
    base data (by decide) (by decide)
  exact ⟨_, ran, configured_with_memory cfg _⟩

/-- SD preserves ROM while writing all eight bytes of its permitted interval. -/
theorem doubleStore : RetiresWithFrame 0x00313023 65544 0x123456789abcdef0 (image 0x00313023).readOnly := by
  apply retires _ _ _ _ (.STORE (0, .Regidx 3, .Regidx 2, 8)) (by native_decide) rfl (by native_decide)
  intro state cfg base data _
  have ran := Advance.execute_STORE_reaches_width8 0 2 3 65544 0x123456789abcdef0 state cfg.init cfg.toValidMemConfig
    base data (by decide) (by decide)
  exact ⟨_, ran, configured_with_memory cfg _⟩

private theorem split_eight (state : SailState) (address : BitVec 64) (alignment : ℕ)
    (addressZeros : address.countTrailingZeros = alignment)
    (remainder : (address.toNatInt.tmod (8 : ℕ) == (0 : ℤ)) = false)
    (checked : (8 : ℕ) = ((8 : ℤ).tdiv (2 ^ min (alignment : ℤ) 3) * 2 ^ min (alignment : ℤ) 3).toNat) :
    (split_misaligned (.Physaddr address) 8 0 .CanSplit).run state =
      .ok ((8 : ℤ).tdiv (2 ^ min (alignment : ℤ) 3), 2 ^ min (alignment : ℤ) 3) state := by
  have widthZeros : (to_bits (l := 13) 8).countTrailingZeros = 3 := by decide +kernel
  change (if ((address.toNatInt.tmod (8 : ℕ) == (0 : ℤ)) || false) then
    pure (1, 8) else split_access address 8).run state = _
  rw [remainder]
  change (split_access address 8).run state = _
  simp only [split_access, addressZeros, widthZeros, Nat.cast_ofNat]
  rw [← checked]
  rfl

/-- Real misaligned accesses split into eight bytes, four halfwords or two words as appropriate. -/
theorem actualMisalignedSplits (state : SailState) :
    (split_misaligned (.Physaddr 65541) 8 0 .CanSplit).run state = .ok (8, 1) state ∧
    (split_misaligned (.Physaddr 65542) 8 0 .CanSplit).run state = .ok (4, 2) state ∧
    (split_misaligned (.Physaddr 65540) 8 0 .CanSplit).run state = .ok (2, 4) state ∧
    (split_misaligned (.Physaddr 69631) 8 0 .CanSplit).run state = .ok (8, 1) state := by
  exact ⟨split_eight state _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    split_eight state _ 1 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    split_eight state _ 2 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    split_eight state _ 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- The protected last byte of a misaligned store cannot escape its permission check. -/
theorem rejectsMisalignedOverlap :
    InstructionWrite.check (fun address => address == 65548)
      (source 0x00313023 65541 0).sail.skeleton.get_reg? (.STORE (0, .Regidx 3, .Regidx 2, 8)) = false := by
  native_decide

/-- Storing the existing instruction byte still needs write permission. -/
theorem rejectsSameValueRomStore :
    (source 0x00310023 65536 0x23).sail.memory.read 65536 = 0x23 ∧
    InstructionWrite.check (image 0x00310023).readOnly
      (source 0x00310023 65536 0x23).sail.skeleton.get_reg? (.STORE (0, .Regidx 3, .Regidx 2, 1)) = false := by
  native_decide

end SP1CleanTest.Core.MemoryFrame
