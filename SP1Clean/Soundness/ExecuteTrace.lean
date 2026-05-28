import SP1Clean.Soundness.TraceSoundness
import SP1Clean.Chips.ALU.AddChip.SailBridge
import SP1Clean.Chips.ALU.AddiChip.SailBridge
import SP1Clean.Chips.ALU.SubChip.SailBridge

/-! # Trace-level reference generator + Sail executor (Track 3, greenfield)

This file lands the three greenfield artifacts of the SP1Clean
soundness-end-to-end track:

1. **`InstrContext` + `genRow`** — a Lean *reference generator*. An
   `InstrContext` is a "valid context" carrier: it bundles a chip's
   `Cols` struct together with the proof obligations a verifier supplies
   for that row (`assertion.Spec` + chip `Assumptions`). `genRow` is the
   thin 1:1 classifier into `ChipRow`; `genTrace = List.map genRow`. This
   discharges the per-row `h_specs` hypothesis of the conditional
   aggregation theorems *constructively*.

2. **`execute_trace`** — a recursive `SailM` executor over a list of
   contexts, threading the per-instruction Sail program (`spec_*` +
   `tick_pc`) through a running `SailState`.

3. **`trace_liveness`** — the end-to-end statement: the aggregation
   conclusion (offline-memory consistency + PC chain + is_real-binary +
   boundary) *and* `∃ s_final, execute_trace s₀ ctxs = some s_final`.

## Scope of this scaffold

`InstrContext` covers the three chips that are both (a) backed by a real
`SailBridge.sail_correct_of_formalSpec` and (b) free of combinatorial
witnesses (Add/Addi/Sub) — so it carries no witness-generation `h_join`
field. Extending it to the combinatorial chips (Mul/Shift/DivRem/Bitwise/Lt)
would add, per chip, a named `h_join` standing in for the Track-1
boundary-A operation lemma; that extension is left as follow-up.

**On `sorry` / axioms.** This file's own proofs are `sorry`-free
(`execute_trace_terminates` is fully axiom-clean:
`propext / Classical.choice / Quot.sound`). The trace-level statements
quantify over `ChipRow.Spec`, whose *definition* references every chip's
`assertion` — including the still-open `Mul`/`DivRem` completeness
(Track 1). So `genRow_spec` / `trace_liveness` inherit `sorryAx`
transitively, with **exactly the footprint of the pre-existing
`trace_soundness_with_boundary`** they build on — i.e. no *new* sorry is
introduced here; the residue is the documented Track-1 chip-completeness
frontier.

The inter-row trace-shape facts (`TraceClkLink`, `TraceStateLink`,
`TraceStateBoundary`) and the per-trace liveness precondition
(`ValidChain`) remain hypotheses — intrinsically verifier-supplied
schedule/handoff data (the `h_link` inputs the existing
`traceClkValid_of_chip_specs` / `traceStateValid_of_chip_specs`
dispatchers already expose), plus the no-trap chain whose constructive
discharge is documented on `ValidChain` (R1 follow-up). -/

namespace SP1Clean.Soundness

open SP1Clean LeanRV64D.Functions

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Phase 1a — `InstrContext` + `genRow` -/

/-- A validated per-row context. Carries the chip's column struct plus
the proof obligations a verifier supplies for that row: the chip's
`assertion.Spec` (the full structural+semantic contract) and the chip
`Assumptions` (`is_trusted = is_real ∧ is_real = 1`). State-dependent
preconditions (`addInitialState_cols`) are *not* fields here — the running
`SailState` varies along the trace, so those are threaded separately by
`ValidStateChain`. -/
inductive InstrContext (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  | add  (cols : Add.AddCols (ZMod p))
         (h_spec : Add.assertion.Spec cols)
         (h_as : Add.Assertion.Assumptions cols)
  | addi (cols : Addi.AddiCols (ZMod p))
         (h_spec : Addi.assertion.Spec cols)
         (h_as : Addi.Assertion.Assumptions cols)
  | sub  (cols : Sub.SubCols (ZMod p))
         (h_spec : Sub.assertion.Spec cols)
         (h_as : Sub.Assertion.Assumptions cols)

/-- The reference generator: classify a validated context into the
heterogenous `ChipRow`, discarding the carried proof fields. -/
def genRow : InstrContext p → ChipRow p
  | .add cols _ _  => .add cols
  | .addi cols _ _ => .addi cols
  | .sub cols _ _  => .sub cols

/-- Generate a trace of `ChipRow`s from a list of validated contexts. -/
def genTrace (ctxs : List (InstrContext p)) : List (ChipRow p) :=
  ctxs.map genRow

/-- Each generated row satisfies its `ChipRow.Spec` — the carried
`h_spec` *is* the per-row spec. This discharges the `h_specs` hypothesis
of the conditional aggregation theorems constructively. -/
theorem genRow_spec [Fact (2 ^ 24 < p)] (ctx : InstrContext p) :
    ChipRow.Spec (genRow ctx) := by
  cases ctx with
  | add cols h_spec _  => exact h_spec
  | addi cols h_spec _ => exact h_spec
  | sub cols h_spec _  => exact h_spec

/-- Trace-level: every generated row satisfies its `Spec`. -/
theorem genTrace_specs [Fact (2 ^ 24 < p)] (ctxs : List (InstrContext p)) :
    ∀ row ∈ genTrace ctxs, ChipRow.Spec row := by
  intro row h_mem
  simp only [genTrace, List.mem_map] at h_mem
  obtain ⟨ctx, _, rfl⟩ := h_mem
  exact genRow_spec ctx

/-! ## Phase 1b — aggregation-half wiring

From the constructively-generated per-row specs plus the intrinsic
inter-row trace-shape links, the full constraint-level aggregation
conclusion holds. This is the existing proven
`trace_soundness_with_boundary` with its `h_specs` discharged by
`genTrace_specs` and its trace-shape bundles discharged by the existing
`_of_chip_specs` dispatchers from the supplied links. -/

theorem trace_liveness_aggregate [Fact (2 ^ 24 < p)]
    (ctxs : List (InstrContext p))
    (initial_pc final_pc : Vector (ZMod p) 3)
    (h_clkLink : TraceClkLink (genTrace ctxs) 8)
    (h_stateLink : TraceStateLink (genTrace ctxs) 8)
    (h_boundary : TraceStateBoundary (genTrace ctxs) initial_pc final_pc)
    (h_online :
      MemoryAccessList.isConsistentOnline (aggregateMemoryAccesses (genTrace ctxs))
        (aggregateMemoryAccesses_isTimestampSorted (genTrace ctxs)
          (traceClkValid_of_chip_specs (genTrace ctxs) (genTrace_specs ctxs) h_clkLink))) :
    (∃ permuted : AddressSortedMemoryAccessList,
        permuted.val.Perm (aggregateMemoryAccesses (genTrace ctxs)) ∧
        MemoryAccessList.isConsistentOffline permuted.val permuted.property)
      ∧ pcChainProp 8 (aggregateStateAccesses (genTrace ctxs))
      ∧ TraceIsRealBinary (genTrace ctxs)
      ∧ TraceStateBoundary (genTrace ctxs) initial_pc final_pc := by
  have h_specs := genTrace_specs ctxs
  have h_clk := traceClkValid_of_chip_specs (genTrace ctxs) h_specs h_clkLink
  have h_state := traceStateValid_of_chip_specs (genTrace ctxs) 8 h_specs h_stateLink
  exact trace_soundness_with_boundary (genTrace ctxs) 8 initial_pc final_pc
    h_specs h_clk h_state h_boundary h_online

/-! ## Phase 1c — Sail executor + termination

`execStep` runs one row's RISC-V semantics: the chip's Sail `spec_*`
program (the faithful per-instruction RISC-V step from `SP1Chips/*`)
followed by `tick_pc` (the inter-instruction `PC ← nextPC` handoff that
`spec_*` omits). `execute_trace` threads these through a running
`SailState`, returning `none` on a Sail error. -/

/-- One row's Sail step: the chip's RISC-V `spec_*` semantics + the
inter-instruction PC tick. The operand projections mirror each chip's
`SailBridge.sail_correct_of_formalSpec` invocation exactly. -/
noncomputable def execStep : InstrContext p → SailM Unit
  | .add cols _ _ => do
      _root_.Add.spec_add (.Regidx (Add.sp1_op_c_cols cols))
        (.Regidx (Add.sp1_op_b_cols cols)) (.Regidx (Add.sp1_op_a_cols cols))
      tick_pc ()
  | .addi cols _ _ => do
      _root_.Addi.spec_addi (Addi.sp1_op_c_cols cols)
        (.Regidx (Addi.sp1_op_b_cols cols)) (.Regidx (Addi.sp1_op_a_cols cols))
      tick_pc ()
  | .sub cols _ _ => do
      _root_.Sub.spec_sub (.Regidx (Sub.sp1_op_c_cols cols))
        (.Regidx (Sub.sp1_op_b_cols cols)) (.Regidx (Sub.sp1_op_a_cols cols))
      tick_pc ()

/-- Recursive Sail executor over a context trace. Threads the running
`SailState`; `none` marks a Sail error (an instruction that traps). -/
noncomputable def execute_trace (s₀ : SailState) :
    List (InstrContext p) → Option SailState
  | [] => some s₀
  | c :: rest =>
      match (execStep c).run s₀ with
      | .ok _ s₁ => execute_trace s₁ rest
      | .error _ _ => none

/-- The trace executes error-free from `s₀`: a recursive predicate
threading the *deterministic* Sail execution (each step's `.run` result
feeds the next). This is the per-trace liveness precondition consumed by
`execute_trace_terminates`.

**Constructive discharge (R1 follow-up — the documented Track-1 join).**
For Add/Sub each step is provably error-free *from the chip `Spec` + the
row's state precondition* (`addInitialState_cols`), so `ValidChain` need
not be assumed. The recipe, per RTypeReader chip:
1. `Add.sail_correct_of_formalSpec` rewrites `(spec_add …).run s` to the
   chip's `(sp1_add_cols cols).run s` (two register writes);
2. `RTypeReader.Gated.Assertion.Spec_iff_sp1` then `rtypeReaderSpec_iff_sp1`
   (under `is_real = is_trusted = 1`, from `Assumptions`) extract from the
   reader spec the facts `op_a_0 = 1 ↔ op_a = 0`, `op_a < 32`, and
   `op_a_0 ≠ 0 → op_a_write_value = 0`;
3. hence the destination-register write never traps (`write_reg` is `.ok`
   on `idx = 0` exactly when the value is `0`), and the trailing `tick_pc`
   reads succeed because `spec_*` wrote `nextPC`.
Addi takes the same shape through `ITypeReader`'s `itypeReaderSpec`.
Carrying `ValidChain` is the planned scaffold stance (CLEAN_PARALLEL_TRACKS
§Track 3, R1); the constructive `step_ok` + `validStateChain` discharge is
the bounded follow-up. -/
def ValidChain : SailState → List (InstrContext p) → Prop
  | _, [] => True
  | s, c :: rest =>
      match (execStep c).run s with
      | .ok _ s₁ => ValidChain s₁ rest
      | .error _ _ => False

/-- An error-free chain executes to a final state. -/
theorem execute_trace_terminates (s₀ : SailState) (ctxs : List (InstrContext p))
    (h : ValidChain s₀ ctxs) : ∃ sf, execute_trace s₀ ctxs = some sf := by
  induction ctxs generalizing s₀ with
  | nil => exact ⟨s₀, rfl⟩
  | cons c rest ih =>
      rw [ValidChain] at h
      cases hrun : (execStep c).run s₀ with
      | ok _ s₁ =>
          rw [hrun] at h
          rw [execute_trace, hrun]
          exact ih s₁ h
      | error _ _ =>
          rw [hrun] at h
          exact absurd h not_false

/-! ## Phase 1d — end-to-end trace liveness

Combines the constraint-level aggregation conclusion (Phase 1b, with
`h_specs` discharged constructively by `genTrace_specs`) with the Sail
executor reaching a final state (Phase 1c). The result: a
constraint-satisfying, error-free trace certifies *both* a consistent
memory/PC bus history *and* a concrete `s₀ → s_final` Sail execution. -/

theorem trace_liveness [Fact (2 ^ 24 < p)]
    (ctxs : List (InstrContext p)) (s₀ : SailState)
    (initial_pc final_pc : Vector (ZMod p) 3)
    (h_clkLink : TraceClkLink (genTrace ctxs) 8)
    (h_stateLink : TraceStateLink (genTrace ctxs) 8)
    (h_boundary : TraceStateBoundary (genTrace ctxs) initial_pc final_pc)
    (h_online :
      MemoryAccessList.isConsistentOnline (aggregateMemoryAccesses (genTrace ctxs))
        (aggregateMemoryAccesses_isTimestampSorted (genTrace ctxs)
          (traceClkValid_of_chip_specs (genTrace ctxs) (genTrace_specs ctxs) h_clkLink)))
    (h_run : ValidChain s₀ ctxs) :
    ((∃ permuted : AddressSortedMemoryAccessList,
          permuted.val.Perm (aggregateMemoryAccesses (genTrace ctxs)) ∧
          MemoryAccessList.isConsistentOffline permuted.val permuted.property)
        ∧ pcChainProp 8 (aggregateStateAccesses (genTrace ctxs))
        ∧ TraceIsRealBinary (genTrace ctxs)
        ∧ TraceStateBoundary (genTrace ctxs) initial_pc final_pc)
      ∧ (∃ sf, execute_trace s₀ ctxs = some sf) :=
  ⟨trace_liveness_aggregate ctxs initial_pc final_pc
      h_clkLink h_stateLink h_boundary h_online,
   execute_trace_terminates s₀ ctxs h_run⟩

end SP1Clean.Soundness
