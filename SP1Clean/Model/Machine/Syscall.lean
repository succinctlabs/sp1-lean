import SP1Clean.Model.Machine.Schedule
import SP1Clean.Model.Semantics.GuestProgram

/-! # Raw SP1 syscall events

The SP1 AIR does not decode register `x5` through Rust's `SyscallCode::from_u32`.  It decomposes the
whole 64-bit word, uses byte zero as the syscall id, and constrains byte one to the Boolean
"send to a handler table" bit.  Consequently, exact Rust enum membership is not a consequence of the
instruction AIR.  This module records that fact in the semantic boundary instead of hiding it behind
an enumerated syscall type.

An event contains the instruction-row observations.  `SyscallTransition` combines the laws enforced
by that row with an explicit handler relation, which owns effects that are not determined by the
instruction AIR (hint data, precompile memory effects, host I/O, and so on). -/

open LeanRV64D.Defs

namespace SP1Clean.Machine

open LeanRV64D
open SP1Clean.Soundness.Target

/-- A real syscall instruction row, before interpreting its raw id as a Rust enum value. -/
structure CoreSyscallEvent where
  clock : ℕ
  pc : BitVec 64
  nextPc : BitVec 64
  rawCode : BitVec 64
  arg1 : BitVec 64
  arg2 : BitVec 64
  result : BitVec 64
deriving DecidableEq, Repr

/-- Byte zero of `x5`, which is all the instruction AIR uses as the syscall id. -/
def CoreSyscallEvent.syscallId (event : CoreSyscallEvent) : ℕ :=
  event.rawCode.toNat % 256

/-- Byte one of `x5`, constrained by the instruction AIR to be Boolean. -/
def CoreSyscallEvent.tableByte (event : CoreSyscallEvent) : ℕ :=
  event.rawCode.toNat / 256 % 256

/-- The exact 64-bit syscall-register value.  Rust converts its low 32 bits with
`SyscallCode::from_u32`, then writes the canonical enum value back to `x5`; the instruction AIR does
not establish that exact-enum fact from `syscallId` and `tableByte` alone. -/
def CoreSyscallEvent.IsCanonicalCode (event : CoreSyscallEvent) (code : ℕ) : Prop :=
  event.rawCode = BitVec.ofNat 64 code

/-- Whether the AIR sends a syscall interaction to a handler table. -/
def CoreSyscallEvent.hasTable (event : CoreSyscallEvent) : Prop :=
  event.tableByte = 1

/-- The AIR-level routing condition.  A byte other than zero or one cannot be a real syscall row. -/
def CoreSyscallEvent.WellRouted (event : CoreSyscallEvent) : Prop :=
  event.tableByte = 0 ∨ event.tableByte = 1

/-- Low-byte syscall ids singled out by `SyscallInstrsChip`. -/
def haltSyscallId : ℕ := 0x00
def enterUnconstrainedSyscallId : ℕ := 0x03
def commitSyscallId : ℕ := 0x10
def commitDeferredSyscallId : ℕ := 0x1a
def hintLenSyscallId : ℕ := 0xf0

/-- SP1's executor-specific terminal pc. -/
def haltPc : BitVec 64 := BitVec.ofNat 64 1

/-- The `x5` result behavior constrained by the baseline trusted instruction AIR.

`HINT_LEN` is intentionally nondeterministic here: the instruction table only range-checks the
result.  Its value must be grounded by the hint/host semantics, not guessed by this row contract. -/
def CoreSyscallEvent.ResultLaw (event : CoreSyscallEvent) : Prop :=
  if event.syscallId = enterUnconstrainedSyscallId then
    event.result = 0
  else if event.syscallId = hintLenSyscallId then
    True
  else
    event.result = event.rawCode

/-- The pc behavior constrained by the baseline trusted instruction AIR. -/
def CoreSyscallEvent.PcLaw (event : CoreSyscallEvent) : Prop :=
  if event.syscallId = haltSyscallId then
    event.nextPc = haltPc
  else
    event.nextPc = event.pc + 4

/-- Address arguments sent to a handler table are 48-bit values in the baseline AIR. -/
def CoreSyscallEvent.HandlerAddressesFit (event : CoreSyscallEvent) : Prop :=
  event.hasTable → event.arg1.toNat < 2 ^ 48 ∧ event.arg2.toNat < 2 ^ 48

/-- Architecture-independent laws contributed by the syscall instruction row itself. -/
def CoreSyscallEvent.RowLaw (event : CoreSyscallEvent) : Prop :=
  event.WellRouted ∧ event.ResultLaw ∧ event.PcLaw ∧ event.HandlerAddressesFit

/-! ## The thirteen inline codes -/

/-- The thirteen canonical inline codes selected by SP1's executor enum. Each is `< 256`, so its
table byte is zero. The raw instruction AIR checks routing bytes, not enum membership; absence
of a `syscallChannel` provider alone does not restrict a shard to this list. -/
def inlineSyscallIds : List ℕ :=
  [ haltSyscallId,               --   0  HALT
    2,                                   --   2  WRITE
    enterUnconstrainedSyscallId, --   3  ENTER_UNCONSTRAINED
    4,                                   --   4  EXIT_UNCONSTRAINED  (never appears in a trace)
    commitSyscallId,             --  16  COMMIT
    commitDeferredSyscallId,     --  26  COMMIT_DEFERRED_PROOFS
    27,                                  --  27  VERIFY_SP1_PROOF
    53,                                  --  53  HINT_MPROTECT_FLUSH
    64,                                  --  64  DUMP_ELF
    65,                                  --  65  INSERT_PROFILER_SYMBOLS
    66,                                  --  66  DELETE_PROFILER_SYMBOLS
    hintLenSyscallId,            -- 240  HINT_LEN
    241 ]                                -- 241  HINT_READ

theorem inlineSyscallIds_length : inlineSyscallIds.length = 13 := rfl

theorem inlineSyscallIds_lt_256 : ∀ c ∈ inlineSyscallIds, c < 256 := by decide

/-- The supported profile requires the whole syscall register to hold an inline code exactly.
This is stronger than successful Rust dispatch: the executor applies `SyscallCode::from_u32` after
casting `x5` to `u32`, so dispatch alone does not constrain its upper 32 bits. It is also stronger
than the AIR's low-byte selector tests. The full-word restriction is an explicit premise. -/
def CoreSyscallEvent.IsInlineCanonical (event : CoreSyscallEvent) : Prop :=
  event.rawCode.toNat ∈ inlineSyscallIds

/-- A canonical inline code is its own low byte, so the AIR's byte-0 view is the whole code. -/
theorem CoreSyscallEvent.syscallId_of_inlineCanonical {event : CoreSyscallEvent}
    (h : event.IsInlineCanonical) : event.syscallId = event.rawCode.toNat :=
  Nat.mod_eq_of_lt (inlineSyscallIds_lt_256 _ h)

/-- A canonical inline code routes nowhere: its table byte is zero. -/
theorem CoreSyscallEvent.tableByte_of_inlineCanonical {event : CoreSyscallEvent}
    (h : event.IsInlineCanonical) : event.tableByte = 0 := by
  rw [CoreSyscallEvent.tableByte, Nat.div_eq_of_lt (inlineSyscallIds_lt_256 _ h)]

/-- The terminal event has the full-word HALT code required by the current `SP1Halted` predicate.
This is stronger than the executor's `u32` dispatch and the AIR's byte-zero HALT selector. -/
def CoreSyscallEvent.IsCanonicalHalt (event : CoreSyscallEvent) : Prop :=
  event.IsCanonicalCode 0

/-- Canonicity plus a zero id is the *exact* Rust `SyscallCode::HALT` — which is what `SP1Halted`
and `HaltsWith` need and what the row alone cannot supply. -/
theorem CoreSyscallEvent.isCanonicalHalt_of_inlineCanonical {event : CoreSyscallEvent}
    (hc : event.IsInlineCanonical) (hid : event.syscallId = haltSyscallId) :
    event.IsCanonicalHalt := by
  have hzero : event.rawCode.toNat = 0 := by
    rw [← CoreSyscallEvent.syscallId_of_inlineCanonical hc]; exact hid
  have : event.rawCode = 0#64 := by
    apply BitVec.eq_of_toNat_eq; simpa using hzero
  simpa [CoreSyscallEvent.IsCanonicalHalt, CoreSyscallEvent.IsCanonicalCode] using this

/-- The event fields agree with the architectural observations at the two State-bus endpoints.
This is not a frame rule: complete register/memory effects belong to the explicit handler relation. -/
def CoreSyscallEvent.MatchesStates (event : CoreSyscallEvent)
    (source target : SailState) : Prop :=
  source.regs.get? Register.PC = some event.pc ∧
    source.get_reg? 5#5 = some event.rawCode ∧
    source.get_reg? 10#5 = some event.arg1 ∧
    source.get_reg? 11#5 = some event.arg2 ∧
    target.regs.get? Register.PC = some event.nextPc ∧
    target.get_reg? 5#5 = some event.result

/-- Effects supplied outside the syscall instruction row.  A concrete full-machine target provides
one named relation and separately proves it agrees with the supported SP1 handler tables/oracles. -/
abbrev SyscallHandler :=
  GuestProgram → CoreSyscallEvent → SailState → SailState → Prop

/-- Complete syscall-step boundary: local AIR laws, endpoint observations, and the chosen handler. -/
def SyscallTransition (handler : SyscallHandler) (program : GuestProgram)
    (event : CoreSyscallEvent) (source target : SailState) : Prop :=
  event.RowLaw ∧ event.MatchesStates source target ∧ handler program event source target

/-- The current instruction at `source` is the RV64 `ECALL` word in the committed program. -/
def AboutToExecuteEcall (program : GuestProgram) (source : SailState) : Prop :=
  ∃ pc : BitVec 64,
    source.regs.get? Register.PC = some pc ∧ program.fetchWord pc = some ECALL_ENC

end SP1Clean.Machine
