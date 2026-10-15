import SP1Clean.Model.Core.ExecutionSnapshot

/-! # Finite checks of invariant Sail fields at the outgoing boundary

The existing snapshots remain the complete state representation. This check compares the
register-map entries that supported ordinary instructions and host calls preserve, including
key presence, and checks the supplied target is initialized. Mutable GPR values are bound by
the complete Memory check. PC/clock and dynamic nextPC/retirement observations have separate
native bindings; this check alone does not assert complete outgoing state equality.
-/

namespace SP1Clean.Model.Core.SailSnapshot

open LeanRV64D.Defs

/-- The registers whose values can change along a supported native execution. -/
def executionRegister (reg : Register) : Bool :=
  decide (reg = .PC ∨ reg = .nextPC ∨ reg = .minstret ∨ reg = .minstret_increment ∨
    ∃ index : BitVec 5, index ≠ 0 ∧ reg = reg_idx_to_Register index)

/-- Retain exactly the register-map entries preserved by the supported execution semantics. -/
def frameRegisters (snapshot : SailSnapshot) : SailRegisterFile.Map :=
  snapshot.registers.filter (fun reg _ => !executionRegister reg)

private instance (snapshot : SailSnapshot) : Decidable snapshot.skeleton.isInitialized :=
  inferInstanceAs (Decidable (∀ reg : Register, reg ∈ snapshot.registers))

/-- Check target presence and every invariant register/runtime field without evaluating Sail. -/
def checkFrame (source target : SailSnapshot) : Bool :=
  decide target.skeleton.isInitialized &&
    SailRegisterFile.equivalent source.frameRegisters target.frameRegisters &&
    decide (source.cycleCount = target.cycleCount) && decide (source.output = target.output)

/-- Lookup in the invariant projection keeps absence as well as values. -/
theorem frameRegisters_get? (snapshot : SailSnapshot) (reg : Register) :
    snapshot.frameRegisters.get? reg =
      if executionRegister reg then none else snapshot.registers.get? reg := by
  rw [frameRegisters, Std.ExtDHashMap.get?_filter]
  cases executionRegister reg <;> cases snapshot.registers.get? reg <;> simp

/-- The projected maps compare every preserved register extensionally. -/
theorem frameRegisters_eq_iff (source target : SailSnapshot) :
    source.frameRegisters = target.frameRegisters ↔
      ∀ reg, executionRegister reg = false → source.registers.get? reg = target.registers.get? reg := by
  constructor
  · intro same reg fixed
    have observed := congrArg (fun registers => registers.get? reg) same
    simpa only [frameRegisters_get?, fixed, Bool.false_eq_true, ↓reduceIte] using observed
  · intro same
    apply Std.ExtDHashMap.ext_get?
    intro reg
    rw [frameRegisters_get?, frameRegisters_get?]
    cases flag : executionRegister reg with
    | true => rfl
    | false => exact same reg flag

/-- Exact finite meaning of the native frame check, including absence of keys. -/
theorem checkFrame_iff (source target : SailSnapshot) :
    checkFrame source target = true ↔
      target.skeleton.isInitialized ∧
      (∀ reg, executionRegister reg = false → source.registers.get? reg = target.registers.get? reg) ∧
      source.cycleCount = target.cycleCount ∧ source.output = target.output := by
  simp only [checkFrame, Bool.and_eq_true, decide_eq_true_eq, SailRegisterFile.equivalent_iff,
    frameRegisters_eq_iff, and_assoc]

private theorem option_transport_injective {α β : Type} (equal : α = β) {left right : Option α}
    (same : (equal ▸ left : Option β) = (equal ▸ right : Option β)) : left = right := by
  cases equal
  exact same

/-- The finite frame check plus authenticated mutable observations identifies literal Sail state.
The enclosing execution proof must derive these observations; they are not capstone premises. -/
theorem realize_eq_of_observations {source target : SailSnapshot} {actual : SailState}
    (checked : source.checkFrame target = true)
    (memory : actual.mem = target.memory.toSailMemory (2 ^ 48))
    (gprs : ∀ index, actual.get_reg? index = some (target.memorySnapshot.read (.reg index)))
    (pc : actual.regs.get? .PC = target.registers.get? .PC)
    (nextPC : actual.regs.get? .nextPC = target.registers.get? .nextPC)
    (retirement : actual.regs.get? .minstret = target.registers.get? .minstret)
    (increment : actual.regs.get? .minstret_increment = target.registers.get? .minstret_increment)
    (preserved : ∀ reg, executionRegister reg = false → actual.regs.get? reg = source.registers.get? reg)
    (runtime : actual.cycleCount = source.cycleCount ∧ actual.sailOutput = source.output) :
    actual = target.realize := by
  have frame := (checkFrame_iff source target).mp checked
  have observes := target.memorySnapshot_realizes frame.1
  have registers : actual.regs = target.registers := by
    apply Std.ExtDHashMap.ext_get?
    intro reg
    by_cases mutable : executionRegister reg = true
    · simp only [executionRegister, decide_eq_true_eq] at mutable
      rcases mutable with rfl | rfl | rfl | rfl | ⟨index, nonzero, rfl⟩
      · exact pc
      · exact nextPC
      · exact retirement
      · exact increment
      · have same := (gprs index).trans (observes.1 index).symm
        simp only [SailState.get_reg?, if_neg nonzero, realize, skeleton] at same
        exact option_transport_injective (reg_idx_must_64 index) same
    · have fixed : executionRegister reg = false := Bool.eq_false_of_not_eq_true mutable
      exact (preserved reg fixed).trans (frame.2.1 reg fixed)
  have snapshots : (capture actual target.memory).realize = target.realize :=
    (realize_eq_iff _ _).mpr ⟨registers, fun _ _ => rfl,
      runtime.1.trans frame.2.2.1, runtime.2.trans frame.2.2.2⟩
  exact (realize_capture actual target.memory memory.symm).symm.trans snapshots

end SP1Clean.Model.Core.SailSnapshot
