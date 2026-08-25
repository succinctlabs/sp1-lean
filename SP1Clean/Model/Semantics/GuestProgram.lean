import SP1Clean.Model.SailMemory
import SP1Clean.Model.SailWrap
import SP1Clean.Model.Register
import LeanRV64D

/-! # Guest programs + the Sail execution model — the semantic-execution substrate (`Model/Semantics/`)

The "general trace arguments and guest programs" the auditor reads to know *what is being executed*: a
`GuestProgram` (encoded instruction ROM + entry point + initial memory image), what it means for a Sail
state to *load* it (`IsInitialState`), the real multi-step chain over the **official** LeanRV64D
interpreter (`SailStep`/`SailChain` on `try_step`), and the halting condition (`SP1Halted`). These
statements depend only on the Sail `SailState` model (`Model/`), so they live in the `Model/Semantics/`
substrate. `LocalStateTruth`/`ProgTruth` are built atop them in `Model/Semantics/Truth.lean` as conclusions of
the global grounding engine; they are deliberately not row-local channel guarantees.

The trace **arguments** that consume them — `RefinesAt`, `RowEffect`, and the per-chip `ChipKind.advance`
obligations — reference the Soundness-layer trace machinery (`Trace.RowView`), so they cannot move below
`Soundness` and live in `Soundness/RowEffectDefs.lean`. (Namespace is kept `SP1Clean.Soundness.Target`
so those consumers resolve these unchanged after importing this file.) -/

open LeanRV64D.Defs
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
  /-- Every ROM word sits in the SP1 code window `[2^16, 2^48)` — the fetch's `range_subset` precondition
  (`range_subset_sp1_pma`, `Model/SailMemory.lean`). SP1 reserves the low 64 KiB, so code never lives there;
  a real ELF loads into this window. Feeds `FetchReady.in_range` at each fetched row. -/
  rom_in_window : ∀ aw ∈ rom, 2 ^ 16 ≤ aw.1.toNat ∧ aw.1.toNat + 4 ≤ 2 ^ 48
  /-- Every ROM word is a **full 32-bit (non-compressed) instruction** — its low two bits are `0b11`. SP1
  emits no RVC, and `isRVC` (upstream of decode) tests exactly this, so `FetchReady.not_rvc` needs it as a
  program invariant (it is not recoverable from a successful decode). -/
  rom_full_width : ∀ aw ∈ rom, aw.2.extractLsb' 0 2 = 0b11#2

/-- The instruction word at `a`, if `a` is a ROM address. -/
def GuestProgram.fetchWord (prog : GuestProgram) (a : BitVec 64) : Option (BitVec 32) :=
  (prog.rom.find? (·.1 == a)).map Prod.snd

/-- The ROM's bytes are present in Sail memory, little-endian — the layout `fetch`/`mem_read` reads. -/
def RomLoaded (prog : GuestProgram) (s : SailState) : Prop :=
  ∀ a w, prog.fetchWord a = some w →
    ∀ i : Fin 4, s.mem.get? (a.toNat + i) = some (w.extractLsb' (8 * i) 8)

/-- **[W7]** The **persist-able, PC-independent** platform-configuration residue of a runnable SP1
execution state — the *global* half of the `try_step` reduction's precondition (its PC-dependent *local*
half — fetch alignment + the ROM word in memory — is derived at use-site from `RomLoaded` + the guest
program's alignment, and is **not** stored here since it is about *this* pc, not a state invariant).

The first two fields (`init`/`priv`) are exactly what the decode reduction (`Model/SailDecode.lean`)
consumes — `isInitialized` (the Zicfilp/forward-CFI decode branch reads privilege-dependent CSRs, which
must be present) and `cur_privilege = Machine` (so the `match cur_privilege` in that branch resolves); the
decode consumers (`DecodeOperandsBound`/`decodedInROM`) only touch these two, so this strengthening keeps
them monotone (`.1`/`.2` = `init`/`priv` still project positionally). The remaining fields are the
quiescent machine-mode facts the interrupt/fetch reductions need (`run_dispatchInterrupt_machine_none` /
`run_fetch_eq_F_Base_of_isInitialized`), bundled here so `RefinesAt.cfg` carries them and
`SailConfigured.toStraightLineReady` can assemble `StraightLineReady` (see `Proofs/Sail/Advance.lean`).
Producers must establish all of it: the `IsInitialState` loader (initial state) and `RowEffect.cfg`
(persistence across each chip's step). -/
structure SailConfigured (s : SailState) : Prop where
  /-- Every register is initialized (present in the register map). -/
  init : s.isInitialized
  /-- Machine privilege. -/
  priv : s.regs.get? Register.cur_privilege = some Privilege.Machine
  /-- The hart is active (not waiting/halted). -/
  active : s.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  /-- Machine interrupts disabled (`mstatus.MIE = 0`) — the interrupt-dispatch short-circuit. -/
  mie : _get_Mstatus_MIE (s.regs.get Register.mstatus (init _)) = 0#1
  /-- No machine-interrupt delegation (`mideleg = 0`) — clears the delegation assert. -/
  mideleg : s.regs.get Register.mideleg (init _) = zeros
  /-- No landing pad expected (`elp ≠ LP_EXPECTED`) — the forward-CFI trap arm is dead. -/
  no_landing_pad :
    s.regs.get? Register.elp ≠ some (landing_pad_bits_backwards landing_pad_expectation.LP_EXPECTED)
  /-- `mstatus.MPRV = 0` (bit 17) — no privilege-modified loads/stores (the fetch/load config). -/
  mprv_disabled : BitVec.ofNat 1 ((s.regs.get Register.mstatus (init _)).toNat >>> 17) = 0#1
  /-- `mseccfg` MML/MMWP off (bit 10) — no memory-security override. -/
  mseccfg_disabled : BitVec.ofNat 1 ((s.regs.get Register.mseccfg (init _)).toNat >>> 10) = 0#1
  /-- `mseccfg` PMM off (bits 33:32 = 0) — pointer masking disabled (identity address transform). -/
  mseccfg_pmm : BitVec.ofNat 2 ((s.regs.get Register.mseccfg (init _)).toNat >>> 32) = 0#2
  /-- No HTIF tohost device. -/
  htif_disabled : s.regs.get Register.htif_tohost_base (init _) = none
  /-- Every PMP entry is OFF — SP1 implements no CSR instructions, so none can ever be installed. -/
  pmp_off : s.regs.get Register.pmpcfg_n (init _) = Vector.replicate 64 0#8
  /-- `misa.M = 1` — the M extension is enabled at boot (and `misa` is boot-stable: SP1 implements
  no CSR writes). The generated decoder's MUL/DIV arms guard on `currentlyEnabled Ext_M`, which
  tests exactly this bit, so without the pin `decodedInROM` is unsatisfiable for every M-family
  row — the silent-vacuity hazard the external PR110 report's Finding 3 warns about, found real
  for this family and closed by this field (2026-08-20). -/
  misa_m : _get_Misa_M (s.regs.get Register.misa (init _)) = 1#1
  /-- The single fixed SP1 PMA region (bare translation) — the fetch/load address decode. -/
  pma_regions : s.regs.get Register.pma_regions (init _) = [SailMem.SP1_PMA_Region]

/-- One decoded instruction, stable across the entire SP1 platform-configuration class.

This is the shared decode currency for committed Program rows and semantic shard transitions.  It
is intentionally about one word/instruction pair; execution-wide quantification belongs to the
relation that owns the transition list, not to a second aggregate decode predicate. -/
def ConfiguredDecode (word : BitVec 32) (decoded : instruction) : Prop :=
  ∀ state, SailConfigured state →
    (ext_decode word).run state = .ok decoded state

/-- The SP1 memory configuration (`isValidMemConfig`) the low-level fetch/load/store lemmas consume,
reconstructed from the flattened `SailConfigured` fields (`h_cur_privilege` derives from `priv`; the
other five are the inlined memory-config fields — the flatten deduped the `cur_privilege` fact). -/
theorem SailConfigured.toValidMemConfig {s : SailState} (cfg : SailConfigured s) :
    SailMem.SailState.isValidMemConfig s cfg.init where
  h_cur_privilege := by
    have h := cfg.priv; rwa [Std.ExtDHashMap.get?_eq_some_get (cfg.init _), Option.some_inj] at h
  h_mprv_disabled := cfg.mprv_disabled
  h_mseccfg_disabled := cfg.mseccfg_disabled
  h_mseccfg_pmm := cfg.mseccfg_pmm
  h_htif_disabled := cfg.htif_disabled
  h_pma_regions := cfg.pma_regions
  h_pmp_off := cfg.pmp_off

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

/-- One real interpreter step whose active-hart branch executed an instruction to
`Retire_Success`, rather than taking one of `run_hart_active`'s trap, illegal-instruction,
wait, or extension-failure exits.

The `should_inc_minstret` equation pins `b` to the value actually selected by `try_step`; the
`run_hart_active` equation then observes the corresponding post-`minstret_increment` state.  The
final equation retains the actual `try_step` target, including its PC/minstret tail.  Keeping this
predicate below the row model lets both the semantic shard relation and `RowEffect` use the same
official-Sail notion of normal retirement. -/
def SailRetiresNormally (s s' : SailState) : Prop :=
  ∃ minstretIncrement : Bool, ∃ instructionBits : instbits, ∃ postExecute : SailState,
    (should_inc_minstret Privilege.Machine).run s = .ok minstretIncrement s ∧
    (run_hart_active 0).run
        ({s with regs := s.regs.insert Register.minstret_increment minstretIncrement}) =
      .ok (Step.Step_Execute (ExecutionResult.Retire_Success (), instructionBits)) postExecute ∧
    (try_step 0 false).run s = .ok false s'

/-- Normal retirement is, in particular, a real Sail step. -/
theorem SailRetiresNormally.sailStep {s s' : SailState}
    (normal : SailRetiresNormally s s') : SailStep s s' := by
  obtain ⟨_, _, _, _, _, step⟩ := normal
  exact ⟨false, step⟩

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

/-- Compatibility contract between SP1's immutable trusted-program fetch and the official Sail
interpreter's unified instruction/data memory.

In SP1 v6.4.0, trusted instruction fetch reads `Program.instructions`, while ordinary loads and
stores read and write the separate Memory state. The ELF loader initially places executable bytes
in that Memory image too, but a later data store does not change the instruction selected by the
Program table. Unmodified Sail instead fetches from the same mutable byte map used by data accesses.

Consequently, a direct multi-step Sail refinement additionally needs the pinned program to preserve
its instruction bytes along the execution under consideration. This is a program-correctness
contract, not an AIR fact and not an unconditional field of `GuestProgram`. It is deliberately
stated over reachable prefixes from the selected shard-local initial state, so callers may prove a
normal inductive code/data-separation invariant rather than the unrealistically strong claim that
every possible store address is outside ROM. -/
def SailCodeMemoryCompatible (prog : GuestProgram) (initial : SailState) : Prop :=
  ∀ {n : ℕ} {state next : SailState},
    SailChain n initial state →
      SailStep state next →
        RomLoaded prog state →
          RomLoaded prog next

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
