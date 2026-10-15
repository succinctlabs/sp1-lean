import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Model.Machine.ConfiguredState

/-! # Canonical memory access and refresh regressions

These finite projection fixtures exercise aliases and `x0` across a refresh boundary. They test
the extractor/scheduler, not a second execution relation; the existing active Sail/JAL anchor
separately consumes the universal compiler-totality theorem.
-/

namespace SP1CleanTest.Core.SemanticAccess
open SP1Clean SP1Clean.Semantics SP1Clean.Soundness.Target SP1Clean.TraceGen LeanRV64D.Defs

private def source : SailState :=
  { configuredState 65536 with
    regs := (configuredState 65536).regs.insert Register.x1 70000
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      [(70000, 7), (70001, 0), (70002, 0), (70003, 0),
        (70004, 0), (70005, 0), (70006, 0), (70007, 0)] }

private def compiled (decoded : instruction) (target : SailState) : Option CompiledInstructionEvent := do
  let key ← instructionRouteKey decoded
  let id ← instructionRouteId decoded
  compileInstructionEvent?
    ⟨65536, 0, decoded, key, id, instructionAccessPlan? decoded source target⟩
    AccessFrontier.initial (2 ^ 24 + 1)

private def summary (result : Option CompiledInstructionEvent) :
    Option (InstructionChipId × List ℕ × List (ℕ × ℕ) × List ℕ) := do
  let result ← result
  pure (result.routed.id, result.stamped.map StampedTouch.previous,
    result.memoryBumps.map (fun event => (event.addr, event.currTs)),
    result.plan.map (fun touch => touch.pushed.toNat))

/-- An aliased load refreshes its base only once; A cites B's fresh timestamp and posts the target value. -/
theorem loadAlias : summary (compiled (.LOAD (0, .Regidx 1, .Regidx 1, false, 8))
    { source with regs := source.regs.insert Register.x1 7 }) =
      some (.loadDouble, [0, 2 ^ 24 + 2, 2 ^ 24 + 4], [(1, 2 ^ 24 + 2)], [7, 70000, 7]) := by
  native_decide

/-- Aliased store operands share the same refresh and remain read-backs, while RAM posts the new word. -/
theorem storeAlias : summary (compiled (.STORE (0, .Regidx 1, .Regidx 1, 1))
    { source with mem := source.mem.insert 70000 112 }) =
      some (.storeByte, [0, 2 ^ 24 + 2, 2 ^ 24 + 4], [(1, 2 ^ 24 + 2)], [112, 70000, 70000]) := by
  native_decide

/-- LOAD-to-x0 retains the RAM read and immutable zero destination, with two distinct register refreshes. -/
theorem loadX0 : summary (compiled (.LOAD (0, .Regidx 1, .Regidx 0, false, 8)) source) =
    some (.loadX0, [0, 2 ^ 24 + 2, 2 ^ 24 + 2], [(1, 2 ^ 24 + 2), (0, 2 ^ 24 + 2)],
      [7, 70000, 0]) := by
  native_decide

/-- Missing any enclosing-cell byte rejects projection, even when the requested byte is present. -/
theorem missingCellByte : (instructionAccessPlan? (.LOAD (0, .Regidx 1, .Regidx 0, false, 1))
    { source with mem := source.mem.erase 70007 } source).isNone := by
  native_decide

private def addProgram : GuestProgram where
  rom := [(65536, 0x003100B3)]
  pc_start := 65536
  memImage := []
  rom_nodup := by decide
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def addState : SailState := configuredState 65536

private def addView : SP1TransitionView :=
  ⟨65536, 0x003100B3, .RTYPE (.Regidx 3, .Regidx 2, .Regidx 1, .ADD),
    ⟨.ADD, false⟩, .add,
    instructionAccessPlan? (.RTYPE (.Regidx 3, .Regidx 2, .Regidx 1, .ADD)) addState addState⟩

private theorem addProjected :
    projectSP1Transition? addProgram ⟨addState, ⟨.ordinary, addState⟩⟩ = some addView := by
  have cfg := cfgState_configured 65536
  have atPc : addState.regs.get? Register.PC = some (65536#64) := cfgState_pc _
  have fetched : addProgram.fetchWord 65536 = some (0x003100B3#32) := rfl
  have decoded := SailDecode.decode_ADD addState cfg.init cfg.priv cfg.mseccfg_disabled
  have observed := decodeLocated?_eq_some_of (located := ⟨addState, ⟨.ordinary, addState⟩⟩)
    atPc fetched decoded
  unfold projectSP1Transition?
  simp only [atPc, Option.bind_eq_bind, Option.bind_some, observed]
  rfl

/-- A real committed word is decoded by official Sail and compiled at a refresh boundary.
The event's validity is obtained from the universal theorem, with no manually supplied event
well-formedness. This tests decode/projection/compilation, not a complete execution segment. -/
theorem decodedAdd_compiles_valid :
    ∃ result, compileInstructionEvent? addView AccessFrontier.initial (2 ^ 24 + 1) = some result ∧
      result.routed.id.Valid result.routed.event := by
  obtain ⟨plan, accesses⟩ := Option.isSome_iff_exists.mp
    (by native_decide : addView.accessPlan?.isSome)
  obtain ⟨result, generated⟩ := instructionEventReady_iff.mp
    (instructionEventReady_of_projection addProjected accesses AccessFrontier.initial (2 ^ 24 + 1))
  refine ⟨result, generated, compileInstructionEvent?_rtype_valid addProjected generated
    (by decide) (by decide) ?_⟩
  intro loc
  simp [AccessFrontier.initial]

/-- Three aliased arithmetic roles refresh once and then consume the immediately preceding
role's timestamp; the destination value remains the actual target-state projection. -/
theorem rtypeAlias : summary (compiled (.RTYPE (.Regidx 1, .Regidx 1, .Regidx 1, .ADD))
    { source with regs := source.regs.insert Register.x1 140000 }) =
      some (.add, [2 ^ 24 + 2, 2 ^ 24 + 3, 2 ^ 24 + 4], [(1, 2 ^ 24 + 2)],
        [70000, 70000, 140000]) := by
  native_decide

private def divOperands (word unsigned remainder : Bool) (left right : BitVec 64) :
    Option (ℕ × ℕ × ℕ) := do
  let state := { configuredState 65536 with
    regs := ((configuredState 65536).regs.insert Register.x2 left).insert Register.x3 right }
  let decoded := if remainder then
      if word then instruction.REMW (.Regidx 3, .Regidx 2, .Regidx 1, unsigned)
      else .REM (.Regidx 3, .Regidx 2, .Regidx 1, unsigned)
    else if word then .DIVW (.Regidx 3, .Regidx 2, .Regidx 1, unsigned)
    else .DIV (.Regidx 3, .Regidx 2, .Regidx 1, unsigned)
  let key ← instructionRouteKey decoded
  let id ← instructionRouteId decoded
  let result ← compileInstructionEvent?
    ⟨65536, 0, decoded, key, id, instructionAccessPlan? decoded state state⟩ AccessFrontier.initial 1
  let event ← result.routed.forId? .divRem
  pure (event.b, event.c, event.opcode)

/-- Zero divisors are valid RISC-V operands, not a compiler-readiness restriction. All eight
signed/unsigned word/full-width divide/remainder opcodes preserve them. -/
theorem divZeroOperands :
    ([(false, false, false), (false, true, false), (false, false, true), (false, true, true),
      (true, false, false), (true, true, false), (true, false, true), (true, true, true)].map
        fun (word, unsigned, remainder) => divOperands word unsigned remainder 123 0) =
      [some (123, 0, 15), some (123, 0, 16), some (123, 0, 17), some (123, 0, 18),
        some (123, 0, 25), some (123, 0, 26), some (123, 0, 27), some (123, 0, 28)] := by
  native_decide

/-- The signed overflow operands survive event compilation exactly at both integer widths. -/
theorem divSignedOverflowOperands :
    (divOperands false false false (BitVec.ofNat 64 (2 ^ 63)) (-1),
      divOperands true false false (BitVec.ofNat 64 (2 ^ 31)) (-1)) =
      (some (2 ^ 63, 2 ^ 64 - 1, 15), some (2 ^ 31, 2 ^ 64 - 1, 25)) := by
  native_decide

private def branchImmediate (immediate : BitVec 13) : Option (ℕ × ℕ) := do
  let result ← compiled (.BTYPE (immediate, .Regidx 0, .Regidx 0, .BEQ)) source
  let event ← result.routed.forId? .branch
  pure (event.imm, event.branchTarget)

/-- Branches retain their thirteenth immediate bit before sign extension. This positive offset
used to be truncated to twelve bits and miscompiled as -4. -/
theorem branchPositiveHigh : branchImmediate 4092 = some (4092, 69628) := by
  native_decide

/-- The most negative branch offset used to be truncated to zero. -/
theorem branchNegativeLimit : branchImmediate 4096 = some (2 ^ 64 - 4096, 61440) := by
  native_decide

/-- Both sides of the twelve-bit sign boundary remain positive thirteen-bit immediates. -/
theorem branchPositiveSignBoundary :
    (branchImmediate 2044, branchImmediate 2048) =
      (some (2044, 67580), some (2048, 67584)) := by
  native_decide

/-- Negative offsets retain their full thirteen-bit signed meaning at both limits. -/
theorem branchNegativeSignBoundary :
    (branchImmediate 6144, branchImmediate 8188) =
      (some (2 ^ 64 - 2048, 63488), some (2 ^ 64 - 4, 65532)) := by
  native_decide

/-- A zero branch offset remains unchanged. -/
theorem branchZero : branchImmediate 0 = some (0, 65536) := by
  native_decide

end SP1CleanTest.Core.SemanticAccess
