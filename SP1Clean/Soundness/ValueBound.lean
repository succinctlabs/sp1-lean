import SP1Clean.Soundness.Decode

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

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **The value half of `OperandsBound`.** For each register source operand (`imm = 0`), the live Sail
register value equals the row's committed read-value column (`op_b`/`op_c` `prev_value`). This is what
W7's `try_step` reduction consumes: the interpreter's `rs1`/`rs2` reads agree with the chip's columns, so
the executed result matches the committed `rdWrite`. -/
def ValueOperandsBound (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  (∀ idx : BitVec 5, r.adapter.imm_b = 0 → (idx.toNat : ZMod p) = r.adapter.op_b[0] →
      s.get_reg? idx = some (Word.toBitVec64 r.adapter.op_b_memory.prev_value)) ∧
  (∀ idx : BitVec 5, r.adapter.imm_c = 0 → (idx.toNat : ZMod p) = r.adapter.op_c[0] →
      s.get_reg? idx = some (Word.toBitVec64 r.adapter.op_c_memory.prev_value))

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

end SP1Clean.Soundness.Target
