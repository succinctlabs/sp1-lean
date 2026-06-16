import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Model.Register
import LeanRV64D

/-! # Guest programs + the Sail execution model — the 5th-pillar audit surface

The "general trace arguments and guest programs" the auditor reads to know *what is being executed*: a
`GuestProgram` (encoded instruction ROM + entry point + initial memory image), what it means for a Sail
state to *load* it (`IsInitialState`), the real multi-step chain over the **official** LeanRV64D
interpreter (`SailStep`/`SailChain` on `try_step`), and the halting condition (`SP1Halted`). These
statements depend only on the Sail `SailState` model (`Model/`), so they sit on the audit surface
*below* the proofs (between `Model` and `Soundness`).

The trace **arguments** that consume them — `TargetObligations`, `WalkOf`, `RefinesAt`, `RowEffect`, and
the target theorem `sp1_target_execution` — reference `ChipRow`/`StateAccess` (the Soundness-layer trace
machinery), so they cannot move below `Soundness` and stay in `Soundness/TargetVm.lean`. (Namespace is
kept `SP1Clean.Soundness.Target` so `TargetVm` resolves these unchanged after importing this file.) -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ}

/-! ## The guest program

The Lean shadow of SP1's `Program` (`../sp1 crates/core/executor/src/program.rs`), prover-only fields
dropped: an encoded instruction ROM (pc ↦ 32-bit instruction word), the entry point, and the initial
byte-granular memory image. The *encoding* is primary — the Sail machine fetches encodings, the chips
consume decoded operands, so "the decode is correct" (W3) is a theorem target, not a definition. -/
structure GuestProgram where
  /-- pc ↦ encoded instruction word. -/
  rom : List (BitVec 64 × BitVec 32)
  /-- The entry point (`pc_start`). -/
  pc_start : BitVec 64
  /-- The initial data image, byte-granular (address ↦ byte). -/
  memImage : List (BitVec 64 × BitVec 8)
  rom_nodup : (rom.map Prod.fst).Nodup
  rom_aligned : ∀ a ∈ rom.map Prod.fst, a.toNat % 4 = 0

/-- The instruction word at `a`, if `a` is a ROM address. -/
def GuestProgram.fetchWord (prog : GuestProgram) (a : BitVec 64) : Option (BitVec 32) :=
  (prog.rom.find? (·.1 == a)).map Prod.snd

/-- The ROM's bytes are present in Sail memory, little-endian — the layout `fetch`/`mem_read` reads. -/
def RomLoaded (prog : GuestProgram) (s : SailState) : Prop :=
  ∀ a w, prog.fetchWord a = some w →
    ∀ i : Fin 4, s.mem.get? (a.toNat + i) = some (w.extractLsb' (8 * i) 8)

/-- **[W7 seam]** The platform-configuration residue of a runnable initial state — machine mode, no
enabled interrupts, bare address translation, hart active, RVC off, … Populated incrementally as the
`try_step` reduction (W7) discovers exactly which Sail registers it needs pinned; currently the empty
conjunction, so the obligation it represents lives entirely in `TargetObligations.lift`. -/
def SailConfigured (_s : SailState) : Prop := True

/-- A Sail state that "loads" the guest program: a *relation*, not a constructed state, so everything
the execution doesn't touch stays quantified. ELF ingestion (W6b) produces a `GuestProgram` and a
concrete witness state. -/
structure IsInitialState (prog : GuestProgram) (s : SailState) : Prop where
  initialized : s.isInitialized
  pc : s.regs.get? Register.PC = some prog.pc_start
  romLoaded : RomLoaded prog s
  imageLoaded : ∀ av ∈ prog.memImage, s.mem.get? av.1.toNat = some av.2
  configured : SailConfigured s

/-! ## The real Sail multi-step chain

`SailM = EStateM …` over `SequentialState` (memory lives *inside* the state, the choice source is
trivial), so `try_step` is deterministic: the chain below is relational, but each state has at most one
successor. `try_step` is the topmost upstream entry point — interrupt dispatch, fetch, decode, execute,
PC commit — so nothing of the interpreter is bypassed. -/

/-- One real interpreter step: `try_step` runs to completion (no trap-out of the model). -/
def SailStep (s s' : SailState) : Prop :=
  ∃ b : Bool, (try_step 0 false).run s = .ok b s'

/-- An `n`-step Sail execution chain. -/
inductive SailChain : ℕ → SailState → SailState → Prop
  | refl (s : SailState) : SailChain 0 s s
  | step {n : ℕ} {s s' s'' : SailState} :
      SailStep s s' → SailChain n s' s'' → SailChain (n + 1) s s''

theorem SailChain.snoc : ∀ {n : ℕ} {a b : SailState}, SailChain n a b →
    ∀ {c : SailState}, SailStep b c → SailChain (n + 1) a c := by
  intro n a b h
  induction h with
  | refl s => exact fun hs => .step hs (.refl _)
  | step h1 _ ih => exact fun hs => .step h1 (ih hs)

/-! ## Halting (SP1 execution-environment semantics, observed not simulated)

SP1's `ECALL` is not RISC-V privileged `ECALL`: Sail's `execute_ECALL` traps to an M-mode handler,
SP1's reads the syscall id from `t0`/x5 (HALT = 0), the exit code from `a0`/x10, and stops with
`next_pc = [HALT_PC, 0, 0]`. The honest claim against the *unmodified* Sail model is therefore: the
chain stops one step **before** the halting `ECALL`, in a state about to execute it with the committed
exit code in `a0`. The walk still carries the halt row's transition to the committed final key. -/

/-- The RV64 `ECALL` encoding. -/
def ECALL_ENC : BitVec 32 := 0x00000073#32

/-- `SyscallCode::HALT` (read from `t0`/x5). -/
def HALT_SYSCALL : BitVec 64 := 0

/-- The committed exit code as the 64-bit value SP1 reads from `a0`/x10. -/
def exitOf (exit_code : ZMod p) : BitVec 64 := BitVec.ofNat 64 exit_code.val

/-- "About to execute the halting ECALL": the PC points at an `ECALL` encoding in the program ROM,
`t0` holds `HALT`, and `a0` holds the exit code. -/
def SP1Halted (prog : GuestProgram) (exit : BitVec 64) (s : SailState) : Prop :=
  ∃ pc : BitVec 64,
    s.regs.get? Register.PC = some pc ∧
    prog.fetchWord pc = some ECALL_ENC ∧
    s.get_reg? 5#5 = some HALT_SYSCALL ∧
    s.get_reg? 10#5 = some exit

end SP1Clean.Soundness.Target
