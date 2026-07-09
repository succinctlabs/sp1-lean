import SP1Clean.Soundness.Decode
import SP1Clean.Soundness.AdvanceDispatch

/-! # W2 — the value half of `OperandsBound`, and the concrete decode∧value bundle

The decode half of `OperandsBound` (`Soundness/Decode.lean`) ties each row's committed operand *index*
columns to the decode of its instruction word. This file adds the **value half**: each row's committed
operand *value* columns (`op_b`/`op_c` `prev_value` — the register reads the chip computed on) equal the
**live Sail register values** at the row's walk position, and assembles the concrete
`OperandsBound = decode ∧ value` with its `bound` field discharged.

The proof rides the **exact-replay invariant** the W2+W7 keystone installed (`RefinesAt.frame`:
`s.get_reg? idx = replayVal s0 path idx i`). The remaining content — that the committed read-value columns
*are* the exact replay value — is isolated as one named residual, `TraceValueBinding` (the value analog of
how decode threaded `TraceProgramValid` before discharging it from balance). `TraceValueBinding` is the
**cross-bus** statement: it is discharged from the Memory-bus value chain (`memEvent_prevValue_eq_writer` /
W4a's `traceMemoryValid_of_genesis_and_balance`) plus the **walk-order = clk-order bridge** — the `WalkOf`
trail is clk-monotonic (each `stateEdge` advances clk), so the walk-position order `replayVal` ranges over
equals the memory clk order the value chain ranges over. That discharge is the remaining W2 step. -/

namespace SP1Clean.Soundness.Target

open SP1Clean
open SP1Clean.ProgramChip (ProgramRow)
open SP1Clean.LookupAccessList (isConsistentBalanced aggregateChipRows)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

-- `ValueOperandsBound` relocated to `Soundness/RowEffectDefs.lean` (below `ChipRow`, so `Proofs/Sail/Advance`
-- and the chip `advance` proofs can drop below `ChipRegistry` for the `ChipKind.advance` field). Available
-- here unchanged via the transitive import of `RowEffectDefs`.

/-- **The cross-bus residual.** Each row's committed read-value columns are the exact-replay value
(`replayVal`) at the operand register — i.e. the value the most-recent earlier `op_a` write left there.
Discharged from the Memory-bus value chain (`memEvent_prevValue_eq_writer`) + the walk-order = clk-order
bridge; threaded here as the one named link the value half rides (the value twin of `TraceProgramValid`). -/
def TraceValueBinding (s0 : SailState) (path : List (Trace.RowView (ZMod p))) : Prop :=
  ∀ i (hi : i < path.length),
    (∀ idx : BitVec 5, (path[i]'hi).adapter.imm_b = 0 →
        (idx.toNat : ZMod p) = (path[i]'hi).adapter.op_b[0] →
        replayVal s0 path idx i = some (Word.toBitVec64 (path[i]'hi).adapter.op_b_memory.prev_value)) ∧
    (∀ idx : BitVec 5, (path[i]'hi).adapter.imm_c = 0 →
        (idx.toNat : ZMod p) = (path[i]'hi).adapter.op_c[0] →
        replayVal s0 path idx i = some (Word.toBitVec64 (path[i]'hi).adapter.op_c_memory.prev_value))

/-- **The value half of `bound`.** Compose the exact-replay invariant (`RefinesAt.frame`:
`s.get_reg? idx = replayVal …`) with the cross-bus value link (`replayVal … = committed prev_value`): the
live registers equal the committed read-value columns. -/
theorem value_targetBound {prog : GuestProgram} {s0 : SailState}
    {path : List (Trace.RowView (ZMod p))} (h_link : TraceValueBinding s0 path)
    {i : ℕ} (hi : i < path.length) {s : SailState} (href : RefinesAt prog s0 path i s) :
    ValueOperandsBound (path[i]'hi) s := by
  obtain ⟨hb, hc⟩ := h_link i hi
  exact ⟨fun idx himmb hidx => (href.frame idx).trans (hb idx himmb hidx),
         fun idx himmc hidx => (href.frame idx).trans (hc idx himmc hidx)⟩

/-! ## Toward discharging `TraceValueBinding`: the walk-order = clk-order bridge

`TraceValueBinding` reconciles two buses: `replayVal` ranges over the **walk position** order (State bus),
while the Memory-bus value chain (`memEvent_prevValue_eq_writer`) ranges over the **clk** order. The bridge
is that the `WalkOf` trail is **clk-monotonic** — `walk_clk_monotone` below: each consecutive pair advances
the state-bus clock by the leading row's `clk_inc` (`sndKey`'s clk slot = the next row's `rcvKey` clk slot).
The remaining discharge of `TraceValueBinding` composes this with (i) the memory event timestamps being the
row clocks (`rowClkLow`), (ii) the Memory-bus value chain (`traceMemoryValid_of_genesis_and_balance` +
`memEvent_prevValue_eq_writer`: a read returns the most-recent earlier write, read-backs preserving it), and
(iii) the genesis alignment (`s0`'s initial registers = 0 = the init chip's genesis value). -/

/-- The clk a state-bus **receive** key carries (the row's current clock). -/
def rcvClkOf (sa : StateAccess (ZMod p)) : ℕ := sa.clk_low.val

/-- The clk a state-bus **send** key carries (the row's committed next clock, `clk + clk_inc`). -/
def sndClkOf (sa : StateAccess (ZMod p)) : ℕ := (sa.clk_low + sa.clk_inc).val

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- A state-bus send/receive handoff (`sndKey sa = rcvKey sb`) advances the clock: `sb`'s receive clock is
`sa`'s send clock `clk + clk_inc` — the clk twin of `sndPc_eq_rcvPc`. -/
lemma sndClk_eq_rcvClk {sa sb : StateAccess (ZMod p)} (h : sndKey sa = rcvKey sb) :
    sndClkOf sa = rcvClkOf sb := by
  have h2 := congrArg (fun k => k.2.2) h
  simp only [sndKey, rcvKey, List.cons.injEq, and_true] at h2
  exact h2.2.1

/-- **The walk is clk-monotonic.** Consecutive rows of the `WalkOf` trail advance the state-bus clock:
position `i`'s committed next clock (`sndClkOf = clk + clk_inc`) is position `i+1`'s current clock
(`rcvClkOf = clk`). This is the walk-order = clk-order fact the `TraceValueBinding` discharge rides — the
walk visits rows in increasing clock order, matching the order the Memory-bus value chain reads them. -/
lemma walk_clk_monotone {pi : SP1PublicIO (ZMod p)} {rows : List (ChipRow p)}
    {path : List (Trace.RowView (ZMod p))} (hw : WalkOf pi rows path)
    (i : ℕ) (hi : i + 1 < path.length) :
    sndClkOf (stateAccess (path[i]'(by omega))) = rcvClkOf (stateAccess (path[i + 1]'hi)) := by
  exact sndClk_eq_rcvClk (by simpa only [stateEdge] using isWalk_chain hw.1 i hi)

/-! ## The concrete decode∧value `OperandsBound` -/

/-- **The concrete `OperandsBound`**: decode (W3, indices = decode of the fetched word) ∧ value (W2,
register reads = live Sail registers). -/
def OperandsBound_full (prog : GuestProgram) (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  DecodeOperandsBound prog r s ∧ ValueOperandsBound r s

/-- **The full `bound` field, both halves discharged.** Decode half from the threaded Program-bus link
(`decode_targetBound`), value half from the threaded cross-bus value link (`value_targetBound`). -/
theorem operandsBound_full_targetBound (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_decode_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s →
        OperandsBound_full prog (path[i]'hi) s := by
  intro s0 path h0 hw i hi s href
  exact ⟨decode_targetBound prog pi rows h_decode_link s0 path h0 hw i hi s href,
         value_targetBound (h_value_link s0 path h0 hw) hi href⟩

/-- **The full `TargetObligations` at the concrete decode∧value `OperandsBound`.** The `bound` field is
discharged (decode + value); `lift`/`halt`/`halt_nonempty` remain the W7/W5 seams. Feeding this into
`Target.sp1_target_execution` yields the machine-level theorem with the *concrete* `OperandsBound`, with
exactly the W7/W5 obligations (and the two threaded links — Program-bus + cross-bus value) open. -/
def targetObligations_full (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_decode_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path)
    (h_lift : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i + 1 < path.length) s,
        RefinesAt prog s0 path i s → OperandsBound_full prog (path[i]'(by omega)) s →
        ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s')
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        OperandsBound_full prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (OperandsBound_full prog) where
  bound := operandsBound_full_targetBound prog pi rows h_decode_link h_value_link
  lift := h_lift
  halt_nonempty := h_halt_nonempty
  halt := h_halt

/-! ## P4 — the Program-bus link **retired**: decode half from the finished-channel balance

The `TraceProgramValid` Program-bus link `targetObligations_full` threads is now replaced by the
balance-level decode discharge (`decode_targetBound_of_balance` = constructed provider
`programProvider_of_valid` + `programConsistent_of_balance`). The committed program ROM (`rom`, each row
the decode of the guest ROM) and the balanced Program bus suffice — no standalone Program link. The bus
balance (`isConsistentBalanced`) is the lone LogUp/GKR residual, the same shape every other bus carries
until the full `VmTables` capstone; that residual is discharged by the timed-channel grounding engine
(Phase 5) — SC Phase 2a flipped `programChannel` to a semantic `VmChannel` (`Guarantees := ProgTruth`), so
it is no longer *finished* against a provider (`ProgramProviderChip` still pushes each `RowSpec`-valid row,
owing `RowSpec`). The cross-bus **value** link (`h_value_link`) is a *different* bus and stays threaded —
retiring it is the value-half (W2) task. -/

/-- **The full `bound` field with the Program-bus link retired.** Decode half from
`decode_targetBound_of_balance` (decoded ROM + balance), value half from the threaded cross-bus value
link. The Program-bus `TraceProgramValid` link is gone. -/
theorem operandsBound_full_targetBound_of_balance (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_decoded : ∀ row ∈ rom, decodedInROM prog row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows (rows.map ChipRow.view) programLookups ++ romContributions rom mult))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s →
        OperandsBound_full prog (path[i]'hi) s := by
  intro s0 path h0 hw i hi s href
  exact ⟨decode_bound_of_balance prog rom mult h_decoded h_bal hw hi s,
         value_targetBound (h_value_link s0 path h0 hw) hi href⟩

/-- **The full `TargetObligations` with the Program-bus link retired** (decode half discharged from
Program-bus balance). The only Program-bus residual is the `isConsistentBalanced` fact — grounded by the
timed-channel engine (Phase 5) now that SC Phase 2a flipped `programChannel` to a semantic `VmChannel`
(no longer *finished* against a provider). The cross-bus value link and the W7/W5 lift/halt seams remain. -/
def targetObligations_full_of_balance (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_decoded : ∀ row ∈ rom, decodedInROM prog row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows (rows.map ChipRow.view) programLookups ++ romContributions rom mult))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path)
    (h_lift : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i + 1 < path.length) s,
        RefinesAt prog s0 path i s → OperandsBound_full prog (path[i]'(by omega)) s →
        ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s')
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        OperandsBound_full prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (OperandsBound_full prog) where
  bound := operandsBound_full_targetBound_of_balance prog pi rows rom mult h_decoded h_bal h_value_link
  lift := h_lift
  halt_nonempty := h_halt_nonempty
  halt := h_halt

/-! ## P5 — the W7 `lift` seam discharged per-chip: `chipRows_advance_sound` wired in

SC Phase 4 collapses the 25 bespoke `sailEquiv`/`reaches_sail` predicates into ONE uniform
`ChipKind.advance` obligation (one real Sail `try_step` produces the row's `RowEffect`), and
`chipRows_advance_sound` (`Soundness/AdvanceDispatch.lean`) assembles the per-chip `advance`s into the
whole-trace `lift` generically (no per-chip `cases`). These two defs replace the monolithic black-box
`h_lift` hypothesis of `targetObligations_full`/`_of_balance` with that dispatcher — so `lift` is no
longer a seam but `advance` (proved per chip, axiom-clean) composed with three clearly-named residuals:

* `h_migrated` — **coverage**: every real row's chip populates `advance` (`isSome`). True today for all
  chips **except** the four width-8/non-injective decoder-seam chips (Mul, LoadDouble, LoadX0,
  StoreDouble), whose `advance` stays `none` pending the intractable `encdec_backwards` trace.
* `h_decode` — the **Program-bus fetch truth** (`decodedInROM`), the `ProgTruth` seam.
* `h_ready` — **trace well-formedness + routing** (`advanceReady`), from `InstructionTrace` + the opcode table.

`OperandsBound_full = DecodeOperandsBound ∧ ValueOperandsBound`, so the dispatcher's `ValueOperandsBound`
premise is met by `hob.2`. -/

/-- **The full `TargetObligations` with `lift` discharged via `chipRows_advance_sound`** (Program-bus link
still threaded). The monolithic W7 `lift` black box is the per-chip `advance` dispatcher ∘
{`h_migrated`, `h_decode`, `h_ready`}. -/
def targetObligations_full_via_advance (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p)) (data : ProverData (ZMod p))
    (h_decode_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path)
    (h_bin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1)
    (h_spec : ∀ r ∈ rows, r.chipSpec data)
    (h_migrated : ∀ r ∈ rows, r.is_real = 1 → (r.kind.advance).isSome = true)
    (h_decode : ∀ r ∈ rows, r.is_real = 1 →
      decodedInROM prog (programAccess r.view).toRow)
    (h_ready : ∀ r ∈ rows, ∀ s : SailState, r.is_real = 1 →
      r.kind.advanceReady r.inputs r.cols prog s)
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        OperandsBound_full prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (OperandsBound_full prog) where
  bound := operandsBound_full_targetBound prog pi rows h_decode_link h_value_link
  lift := fun s0 path h0 hw i hi s href hob =>
    chipRows_advance_sound rows data h_bin h_spec h_migrated h_decode h_ready s0 path h0 hw i hi s href hob.2
  halt_nonempty := h_halt_nonempty
  halt := h_halt

/-- **The full `TargetObligations` with the Program-bus link retired AND `lift` discharged via
`chipRows_advance_sound`** — the furthest capstone: `bound`'s decode half comes from the Program-bus
balance, and `lift` is the per-chip `advance` dispatcher ∘ {`h_migrated`, `h_decode`, `h_ready`}. The
only W7 residual left is coverage (`h_migrated`): true for every chip except the four decoder-seam chips
(Mul/LoadDouble/LoadX0/StoreDouble). -/
def targetObligations_full_of_balance_via_advance (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p)) (data : ProverData (ZMod p))
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_decoded : ∀ row ∈ rom, decodedInROM prog row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows (rows.map ChipRow.view) programLookups ++ romContributions rom mult))
    (h_value_link : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
        TraceValueBinding s0 path)
    (h_bin : ∀ r ∈ rows, r.is_real = 0 ∨ r.is_real = 1)
    (h_spec : ∀ r ∈ rows, r.chipSpec data)
    (h_migrated : ∀ r ∈ rows, r.is_real = 1 → (r.kind.advance).isSome = true)
    (h_decode : ∀ r ∈ rows, r.is_real = 1 →
      decodedInROM prog (programAccess r.view).toRow)
    (h_ready : ∀ r ∈ rows, ∀ s : SailState, r.is_real = 1 →
      r.kind.advanceReady r.inputs r.cols prog s)
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        OperandsBound_full prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (OperandsBound_full prog) where
  bound := operandsBound_full_targetBound_of_balance prog pi rows rom mult h_decoded h_bal h_value_link
  lift := fun s0 path h0 hw i hi s href hob =>
    chipRows_advance_sound rows data h_bin h_spec h_migrated h_decode h_ready s0 path h0 hw i hi s href hob.2
  halt_nonempty := h_halt_nonempty
  halt := h_halt

end SP1Clean.Soundness.Target
