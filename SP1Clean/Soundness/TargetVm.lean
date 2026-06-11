import SP1Clean.Soundness.SP1GatedVm

/-! # The target machine-level theorem — a real Sail execution chain from a loaded guest program

**What this file is.** The *formal target* the whole-machine effort closes toward, stated and proved
today as a skeleton: from a verifying Clean ensemble over the committed public boundary, the **official
LeanRV64D Sail interpreter** (`try_step`), run from *any* state that loads the guest program, reaches
the halting `ECALL` with the committed exit code. The walk induction (Eulerian trail → Sail chain) is
**proved here, `sorry`-free**; everything not yet derivable is a *named hypothesis* — one per roadmap
item — so each future work item discharges exactly one named obligation and the meaningfulness boundary
is the visible list of seams below, not prose.

**The named seams** (consumed by `sp1_target_execution`, discharged by the roadmap):

* `OperandsBound` (a *parameter*, constructed by **W2 operand binding + W3 decode/fetch chips**): the
  row's committed operand columns are honoured by the Sail state at its walk position. The skeleton
  never inspects it — it only threads `TargetObligations.bound` into `TargetObligations.lift` — so the
  W2/W3 work is free to shape it (decode indices from the program bus, values from the memory bus).
* `TargetObligations.lift` (**W7 Sail step-lift**): in a refining state whose operands are bound, one
  `try_step` fires and produces the row's committed effect (`RowEffect`: the PC write, a register-file
  frame at `op_a`, ROM/configuration preservation). This is where each chip's conditional `sailEquiv`
  (the existing per-chip bridges) is upgraded to an actual interpreter step.
* `TargetObligations.halt` + `halt_nonempty` (**W5 ECALL/HALT chip**): the walk's final row is a HALT
  `SyscallInstrs` row, and any state refining the pre-halt prefix satisfies `SP1Halted` with the
  committed `exit_code`. (Note: SP1's syscall rows advance the clock by 256, not 8 —
  `StateAccess`/`sndKey` already carry the per-row `clk_inc` for this (generalized 2026-06-10,
  projected at 8 until the chip lands); the chip itself remains.)
* `SailConfigured` (**W7**): the platform-configuration residue of the initial state (machine mode, no
  enabled interrupts, bare translation, …) — populated incrementally as the `try_step` reduction
  discovers what it needs; currently the empty conjunction.
* `RomLoaded` preservation inside `RowEffect` (**W2b/W4a**): today the memory clause tracks only that
  the program ROM stays intact (stores don't overwrite code); the store-replay strengthening lands with
  the load/store address work and the memory-init slice.

The earlier per-row Sail statement (`GatedExecution.step_sound`) is *evidence* for discharging `lift`,
not a hypothesis here: the skeleton consumes only the **trail** half of `GatedExecution`.

`sp1_target_execution` is axiom-clean (the walk induction is pure logic); the corollary
`sp1_target_soundness` additionally routes through `sp1_machine_soundness` and therefore inherits the
capstone's `sorryAx` (the `sp1_witness_decode` decode-seam premise) until §B5 closes. -/

namespace SP1Clean.Soundness.Target

open SP1Clean
open SP1Clean.LookupAccessList
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

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

/-! ## The extended public IO: `exit_code`

SP1 commits ~30 `PublicValues` fields; the legacy `SP1PublicIO` models the ten state-boundary fields,
and the target adds `exit_code` (`../sp1 crates/hypercube/src/air/public_values.rs`). Kept flat with a
`toLegacy` projection so `sp1GatedVm`/`sp1Verifier` need not fork yet; the eventual W5 landing replaces
`SP1PublicIO` outright. -/
structure SP1TargetPublicIO (F : Type) where
  init_clk_high : F
  init_clk_low : F
  init_pc0 : F
  init_pc1 : F
  init_pc2 : F
  final_clk_high : F
  final_clk_low : F
  final_pc0 : F
  final_pc1 : F
  final_pc2 : F
  exit_code : F
deriving ProvableStruct

/-- Forget `exit_code` — the boundary the current ensemble commits. -/
def SP1TargetPublicIO.toLegacy {F : Type} (pi : SP1TargetPublicIO F) : SP1PublicIO F :=
  { init_clk_high := pi.init_clk_high, init_clk_low := pi.init_clk_low,
    init_pc0 := pi.init_pc0, init_pc1 := pi.init_pc1, init_pc2 := pi.init_pc2,
    final_clk_high := pi.final_clk_high, final_clk_low := pi.final_clk_low,
    final_pc0 := pi.final_pc0, final_pc1 := pi.final_pc1, final_pc2 := pi.final_pc2 }

/-! ## PC limbs ↔ the Sail 64-bit PC -/

/-- Reassemble three 16-bit PC limb values into the Sail 64-bit PC. -/
def pcBitsOfVals (a b c : ℕ) : BitVec 64 := BitVec.ofNat 64 (a + b * 2 ^ 16 + c * 2 ^ 32)

/-- The 64-bit PC a row's state-bus **receive** key carries (its current pc). -/
def rcvPcOf (sa : StateAccess (ZMod p)) : BitVec 64 :=
  pcBitsOfVals sa.pc[0].val sa.pc[1].val sa.pc[2].val

/-- The 64-bit PC a row's state-bus **send** key carries (its committed next pc). -/
def sndPcOf (sa : StateAccess (ZMod p)) : BitVec 64 :=
  pcBitsOfVals sa.next_pc[0].val sa.next_pc[1].val sa.next_pc[2].val

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private lemma sndPc_eq_rcvPc {sa sb : StateAccess (ZMod p)} (h : sndKey sa = rcvKey sb) :
    sndPcOf sa = rcvPcOf sb := by
  have h3 := congrArg (fun k : LookupKey => k.2.2) h
  simp only [sndKey, rcvKey, List.cons.injEq, and_true] at h3
  obtain ⟨-, -, h0, h1, h2⟩ := h3
  simp [sndPcOf, rcvPcOf, h0, h1, h2]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private lemma rcvPc_of_initKey {sa : StateAccess (ZMod p)} {pi : SP1PublicIO (ZMod p)}
    (h : rcvKey sa = (InteractionKind.State, "SP1State", initEntryOf pi)) :
    rcvPcOf sa = pcBitsOfVals pi.init_pc0.val pi.init_pc1.val pi.init_pc2.val := by
  have h3 := congrArg (fun k : LookupKey => k.2.2) h
  simp only [rcvKey, initEntryOf, List.cons.injEq, and_true] at h3
  obtain ⟨-, -, h0, h1, h2⟩ := h3
  simp [rcvPcOf, h0, h1, h2]

/-! ## Generic walk lemmas -/

private lemma isWalk_head {α V : Type} {edge : α → V × V} {src snk : V} {path : List α}
    (hw : GatedVm.IsWalk edge src snk path) (h : 0 < path.length) :
    (edge (path[0]'h)).1 = src := by
  cases path with
  | nil => simp at h
  | cons x rest => exact hw.1

private lemma isWalk_chain {α V : Type} {edge : α → V × V} :
    ∀ {path : List α} {src snk : V}, GatedVm.IsWalk edge src snk path →
      ∀ i (h : i + 1 < path.length), (edge (path[i]'(by omega))).2 = (edge (path[i + 1]'h)).1 := by
  intro path
  induction path with
  | nil => intro src snk _ i h; simp at h
  | cons x rest ih =>
    intro src snk hw i h
    obtain ⟨hx, hrest⟩ := hw
    cases i with
    | zero =>
      cases rest with
      | nil => simp at h
      | cons y rest' => simpa using hrest.1.symm
    | succ j =>
      have h' : j + 1 < rest.length := by simpa using h
      simpa using ih hrest j h'

/-! ## The refinement invariant and the per-row effect -/

/-- The simulation invariant at walk position `i`: the state's PC is the next row's committed pc, the
program ROM is intact, the platform configuration persists, and every register either still holds its
initial value or was written (`op_a`) by an earlier walk row. The register clause is a *frame*, not a
replay — the exact-value strengthening arrives with W2's operand binding. -/
structure RefinesAt (prog : GuestProgram) (s0 : SailState)
    (path : List (Trace.RowView (ZMod p))) (i : ℕ) (s : SailState) : Prop where
  pc : ∀ (h : i < path.length),
    s.regs.get? Register.PC = some (rcvPcOf (stateAccess (path[i]'h)))
  rom : RomLoaded prog s
  init : s.isInitialized
  cfg : SailConfigured s
  frame : ∀ idx : BitVec 5, s.get_reg? idx = s0.get_reg? idx ∨
    ∃ j, ∃ (_ : j < i) (hj : j < path.length),
      (idx.toNat : ZMod p) = (path[j]'hj).adapter.op_a

/-- The committed effect of one row, as a relation between the pre- and post-states of its interpreter
step: the PC moves to the row's committed `next_pc`; the register file changes at most at the row's
`op_a` destination (and there holds the committed write value); ROM, initialization, and configuration
persist. Deliberately *relational* — `try_step` also touches bookkeeping registers (`minstret`,
`hart_state`, …) the trace doesn't commit. -/
structure RowEffect (prog : GuestProgram) (r : Trace.RowView (ZMod p))
    (s s' : SailState) : Prop where
  pc : s'.regs.get? Register.PC = some (sndPcOf (stateAccess r))
  regs : ∀ idx : BitVec 5, s'.get_reg? idx = s.get_reg? idx ∨
    ((idx.toNat : ZMod p) = r.adapter.op_a ∧
      s'.get_reg? idx = some (Word.toBitVec64 r.rdWrite))
  rom : RomLoaded prog s → RomLoaded prog s'
  init : s.isInitialized → s'.isInitialized
  cfg : SailConfigured s → SailConfigured s'

/-- The walk the capstone's trail produces: an `IsWalk` between the committed boundary keys whose rows
are (a sub-multiset of) the trace's real rows. -/
def WalkOf (pi : SP1PublicIO (ZMod p)) (rows : List (ChipRow p))
    (path : List (Trace.RowView (ZMod p))) : Prop :=
  GatedVm.IsWalk (fun r => stateEdge (stateAccess r))
      (InteractionKind.State, "SP1State", initEntryOf pi)
      (InteractionKind.State, "SP1State", finalEntryOf pi) path
    ∧ (↑path : Multiset (Trace.RowView (ZMod p))) ≤ realRowEdges (rows.map ChipRow.view)

/-! ## The named obligations -/

/-- **The open-gap bundle** — every hypothesis of the target theorem that is not yet derived, one named
field per roadmap item (see the module docstring for the W-item mapping). `OperandsBound` is abstract
here; W2/W3 construct the real predicate, prove `bound` for it, and W7 proves `lift` for the same. -/
structure TargetObligations (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (OperandsBound : Trace.RowView (ZMod p) → SailState → Prop) : Prop where
  /-- **[W2 + W3]** At every walk position, a refining state binds the row's operand columns. -/
  bound : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
    ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s → OperandsBound (path[i]'hi) s
  /-- **[W7]** The step-lift: a refining, operand-bound state takes one real `try_step` to the row's
  committed effect. (Positions before the last only — the halting `ECALL` is never executed.) -/
  lift : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
    ∀ i (hi : i + 1 < path.length) s,
      RefinesAt prog s0 path i s → OperandsBound (path[i]'(by omega)) s →
      ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s'
  /-- **[W5]** A committed execution is nonempty (the boundary clk strictly advances). -/
  halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ []
  /-- **[W5]** The walk ends at the halting ECALL: any state refining the pre-halt prefix (with the
  halt row's operands bound) is `SP1Halted` with the committed exit code. -/
  halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
    ∀ (hne : path ≠ []) s,
      RefinesAt prog s0 path (path.length - 1) s →
      OperandsBound (path[path.length - 1]'(by
        have := List.length_pos_of_ne_nil hne; omega)) s →
      SP1Halted prog (exitOf pi.exit_code) s

/-! ## The walk induction (proved) -/

private theorem chain_to_refines
    {prog : GuestProgram} {pi : SP1TargetPublicIO (ZMod p)} {rows : List (ChipRow p)}
    {OperandsBound : Trace.RowView (ZMod p) → SailState → Prop}
    (ob : TargetObligations prog pi rows OperandsBound)
    {s0 : SailState} (h0 : IsInitialState prog s0)
    {path : List (Trace.RowView (ZMod p))} (hw : WalkOf pi.toLegacy rows path)
    (h_entry : pcBitsOfVals pi.init_pc0.val pi.init_pc1.val pi.init_pc2.val = prog.pc_start) :
    ∀ i, i < path.length → ∃ s, SailChain i s0 s ∧ RefinesAt prog s0 path i s := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨s0, .refl s0, ?_, h0.romLoaded, h0.initialized, h0.configured, fun idx => Or.inl rfl⟩
    intro h
    have hhead := isWalk_head hw.1 h
    have hpc : rcvPcOf (stateAccess (path[0]'h))
        = pcBitsOfVals pi.init_pc0.val pi.init_pc1.val pi.init_pc2.val :=
      rcvPc_of_initKey (sa := stateAccess (path[0]'h)) hhead
    rw [hpc, h_entry]
    exact h0.pc
  | succ i ih =>
    intro hi
    have hi' : i < path.length := by omega
    obtain ⟨s, hchain, href⟩ := ih hi'
    have hob := ob.bound s0 path h0 hw i hi' s href
    obtain ⟨s', hstep, heff⟩ := ob.lift s0 path h0 hw i hi s href hob
    refine ⟨s', hchain.snoc hstep, ?_, heff.rom href.rom, heff.init href.init,
      heff.cfg href.cfg, ?_⟩
    · intro h
      rw [heff.pc]
      congr 1
      exact sndPc_eq_rcvPc (isWalk_chain hw.1 i hi)
    · intro idx
      rcases heff.regs idx with he | ⟨ha, _⟩
      · rcases href.frame idx with h0' | ⟨j, hj, hj', hja⟩
        · exact Or.inl (he.trans h0')
        · exact Or.inr ⟨j, by omega, hj', hja⟩
      · exact Or.inr ⟨i, by omega, hi', ha⟩

/-- **The target machine-level theorem (skeleton form).** Given the gated execution certificate over
the committed boundary, the entry-point tie, and the named obligations, the official Sail interpreter,
run from **any** state that loads the guest program, reaches the halting `ECALL` with the committed
exit code. The walk induction is proved here; the obligations are the named open gaps. -/
theorem sp1_target_execution
    (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p)) (rows : List (ChipRow p))
    (OperandsBound : Trace.RowView (ZMod p) → SailState → Prop)
    (h_exec : GatedExecution rows (initEntryOf pi.toLegacy) (finalEntryOf pi.toLegacy))
    (ob : TargetObligations prog pi rows OperandsBound)
    (h_entry : pcBitsOfVals pi.init_pc0.val pi.init_pc1.val pi.init_pc2.val = prog.pc_start) :
    ∀ s0, IsInitialState prog s0 →
      ∃ (n : ℕ) (s_f : SailState),
        SailChain n s0 s_f ∧ SP1Halted prog (exitOf pi.exit_code) s_f := by
  intro s0 h0
  obtain ⟨path, hwalk, hsub⟩ := h_exec.trail
  have hw : WalkOf pi.toLegacy rows path := ⟨hwalk, hsub⟩
  have hne := ob.halt_nonempty path hw
  have hlen : path.length - 1 < path.length := by
    have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨s_f, hchain, href⟩ := chain_to_refines ob h0 hw h_entry (path.length - 1) hlen
  have hob := ob.bound s0 path h0 hw (path.length - 1) hlen s_f href
  exact ⟨path.length - 1, s_f, hchain, ob.halt s0 path h0 hw hne s_f href hob⟩

/-- **The end-to-end corollary**: the same conclusion from a verifying Clean ensemble `Statement`,
routed through `sp1_machine_soundness`. Inherits the capstone's single `sorryAx` (the decode seam
`sp1_witness_decode`) until §B5 closes — the skeleton theorem above is axiom-clean. -/
theorem sp1_target_soundness
    (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (OperandsBound : Trace.RowView (ZMod p) → SailState → Prop)
    (ob : ∀ rows : List (ChipRow p), TargetObligations prog pi rows OperandsBound)
    (h_entry : pcBitsOfVals pi.init_pc0.val pi.init_pc1.val pi.init_pc2.val = prog.pc_start)
    (h_stmt : (sp1GatedVm (p := p)).toEnsemble.Statement pi.toLegacy) :
    ∀ s0, IsInitialState prog s0 →
      ∃ (n : ℕ) (s_f : SailState),
        SailChain n s0 s_f ∧ SP1Halted prog (exitOf pi.exit_code) s_f := by
  obtain ⟨rows, h_exec⟩ := sp1_machine_soundness pi.toLegacy trivial h_stmt
  exact sp1_target_execution prog pi rows OperandsBound h_exec (ob rows) h_entry

/-- The named-seam census the audit doc cites: one entry per open obligation of
`sp1_target_execution`, with its roadmap item. -/
def targetSeams : List String :=
  [ "OperandsBound — construct the real predicate (W2 operand binding + W3 decode/fetch chips)",
    "TargetObligations.bound — derive binding from the memory/program-bus balance (W2 + W3)",
    "TargetObligations.lift — the try_step step-lift per chip kind (W7)",
    "TargetObligations.halt/halt_nonempty — the ECALL/HALT chip (W5; its clk_inc prerequisite landed 2026-06-10)",
    "SailConfigured — populate the platform residue as W7 discovers it (W7)",
    "RowEffect.rom strengthening to store-replay memory (W2b + W4a)",
    "GatedExecution from Statement without sorry — close the sp1_witness_decode decode seam (W1b+W1c/§B5; the W1a balance translation is proven)" ]

end SP1Clean.Soundness.Target
