import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Model.Semantics.GuestProgram
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Soundness.RowEffectDefs

/-! # The target machine-level theorem — a real Sail execution chain from a loaded guest program

> **FROZEN (consolidation step 0, 2026-07-09).** Legacy soundness path — scheduled for deletion at the cutover (proposal §5.6). Do NOT add new lemmas against this module; new soundness work targets the timed-grounding engine (proposal §3.2).

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

The earlier per-row Sail statement (the retired `GatedExecution.step_sound` conjunct) is not consumed here:
the skeleton discharges `lift` from the per-chip `ChipKind.advance` path and uses only the **trail** half
of `GatedExecution`.

`sp1_target_execution` is axiom-clean (the walk induction is pure logic); the corollary
`sp1_target_soundness` additionally routes through `sp1_machine_soundness` and therefore inherits the
capstone's `sorryAx` (the `sp1_witness_decode` decode-seam premise) until §B5 closes. -/

namespace SP1Clean.Soundness.Target

open SP1Clean
open SP1Clean.LookupAccessList
open Sail LeanRV64D LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩


/-! ## The extended public IO: `exit_code`

SP1 commits ~30 `PublicValues` fields; the legacy `SP1PublicIO` models the ten state-boundary fields,
and the target adds `exit_code` (`../sp1 crates/hypercube/src/air/public_values.rs`). Kept flat with a
`toLegacy` projection so `sp1Ensemble`/`sp1StateVerifier` need not fork yet; the eventual W5 landing replaces
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

/-! ## PC limbs ↔ the Sail 64-bit PC — `rcvPcOf`/`sndPcOf` relocated to `Soundness/RowEffectDefs.lean`
(below `ChipRow`), alongside `RefinesAt`/`RowEffect`/`replayVal`, so the `ChipKind.advance` field can
reference them. -/

omit [Fact (2 ^ 24 < p)] in
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

lemma isWalk_chain {α V : Type} {edge : α → V × V} :
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

/-! ## The refinement invariant and the per-row effect — `replayVal`/`RefinesAt`/`RowEffect` relocated to
`Soundness/RowEffectDefs.lean` (below `ChipRow`, so the `ChipKind.advance` field can reference `RowEffect`).
The `WalkOf`/`TargetObligations`/`chain_to_refines` machinery below references `ChipRow`, so it stays here. -/

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
    refine ⟨s0, .refl s0, ?_, h0.romLoaded, h0.initialized, h0.configured, fun idx => rfl,
      fun a => rfl⟩
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
      heff.cfg href.cfg, ?_, ?_⟩
    · intro h
      rw [heff.pc]
      congr 1
      exact sndPc_eq_rcvPc (isWalk_chain hw.1 i hi)
    · intro idx
      have hregs := heff.regs
      by_cases hwr : (path[i]'hi').commit.writesReg = true
      · -- a register-writing row: `heff.regs` is the op_a write + frame pair
        rw [if_pos hwr] at hregs
        by_cases hcond : (idx.toNat : ZMod p) = (path[i]'hi').adapter.op_a
        · rw [hregs.1 idx hcond, replayVal, dif_pos hi', if_pos ⟨hwr, hcond⟩]
        · rw [hregs.2 idx hcond, href.frame idx, replayVal, dif_pos hi', if_neg (fun h => hcond h.2)]
      · -- a non-writing row (Branch / AluX0 / LoadX0): `heff.regs` is a pure register frame, and
        -- `replayVal` skips it (its `writesReg` guard is false)
        rw [Bool.not_eq_true] at hwr
        rw [if_neg (by rw [hwr]; decide)] at hregs
        rw [hregs idx, href.frame idx, replayVal, dif_pos hi',
          if_neg (fun h => by rw [hwr] at h; exact absurd h.1 (by decide))]
    · -- the memory arm: `RowEffect.mem` (store byte-range write / frame) matched against `memReplayVal`
      intro a
      rw [memReplayVal, dif_pos hi']
      split
      · -- a store row (`memWrite = some mw`): the covered bytes are written, the rest framed
        rename_i mw heq
        obtain ⟨hcov, hfr⟩ := heff.mem.2 mw heq
        by_cases hc : mw.covers a
        · rw [if_pos hc]; exact hcov a hc
        · rw [if_neg hc, hfr a hc, href.mem a]
      · -- a non-store row (`memWrite = none`): `s'.mem = s.mem`, `memReplayVal` recurses
        rename_i heq; rw [heff.mem.1 heq a, href.mem a]

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
    (h_stmt : (sp1Ensemble (p := p)).Statement pi.toLegacy) :
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
