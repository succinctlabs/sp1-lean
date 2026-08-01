import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels
import SP1Clean.Extracted.RTypeReader
import SP1Clean.Native.Readers.RegisterAccessTimestamp
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native register-access reader — one operand's columns as composed Clean `FormalCircuit`s

The per-operand register-access block that `Readers/RTypeReader.lean` composes **three times** (rs1
read / rs2 read / rd write). Factoring it out is the idiomatic fix for the `circuit_proof_start`
blow-up: witnessing all 22 adapter columns inline forces soundness/completeness `circuit_norm` to
normalize the whole nested struct in one shot (minutes, then a `whnf` timeout even at 4M heartbeats).
Composing small sub-circuits instead lets `circuit_norm` treat each as a black box — exactly how
`Clean/Gadgets/Keccak/KeccakRound.lean` proves a 1288-column state with plain `circuit_proof_start`.

The block is SP1's nested `RegisterAccessCols` (`Extracted/RTypeReader.lean`): a `prev_value : Word`
plus an `access_timestamp : RegisterAccessTimestamp` of `{prev_low, diff_low_limb}`. The **nesting** is
what defeated a single inline witness, so we mirror the nesting with **two composed sub-circuits**:

- `Readers.RegisterAccessTimestamp.circuit` (`Readers/RegisterAccessTimestamp.lean`) — the genuinely
  tiny (2-column) inner block that carries SP1's two byte-bus timestamp checks
  (`crates/core/machine/src/air/memory.rs`) as **inline `ByteTable` lookups** (SP1's `send_byte` into
  the preprocessed `ByteChip`), both gated by `is_real`.
- `RegisterAccessCols.circuit` (here) — witnesses the 4 `prev_value` columns and composes the
  timestamp sub-circuit, returning the assembled `Extracted.RegisterAccessCols`. Because the timestamp
  is a sub-circuit *output* (an opaque `varFromOffset`), no nested struct literal is ever witnessed, so
  `circuit_norm` stays cheap.

`clk_target` is the operand's access clock (`clk_low + 4/3/2` for op_a/op_b/op_c) — a cross-block
input, like `RTypeReader`'s `clk_low`. The witnessed timestamp columns are computed from it
(`prev_low := clk_target - 1`, `diff := 0`, so the scaled numerator is `0`), which is what makes
completeness hold for every `clk_target`. The `.memory` interactions themselves are off-chip
membership (their meaning is the trace-level memory bus, `Soundness/MemoryConsistency.lean`), so these
sub-circuits emit no lookup for them. -/

namespace SP1Clean.Readers

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace RegisterAccessCols

/-- Witness the 4 `prev_value` columns (`0`) and compose the timestamp sub-circuit, returning the
assembled `Extracted.RegisterAccessCols`. **SP1's register-access read range-checks no `prev_value`**
(`crates/core/machine/src/air/memory.rs:122-166`: it only sends/receives the Memory interactions and the
timestamp check) — the operand's `isU64` is a *received* fact from the writer (the offline-memory balance),
not a local check here, so this reader imposes none. The only byte-bus checks are the two timestamp checks
inside the composed `RegisterAccessTimestamp` sub-circuit. The timestamp comes from a sub-circuit (an opaque
output), so no nested struct literal is witnessed and `circuit_norm` stays cheap. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- `cols` (the `prev_value` + nested timestamp block) is an **input**; this reader witnesses nothing,
  -- it just composes the timestamp sub-assertion on the input's nested `access_timestamp` block.
  assertion RegisterAccessTimestamp.circuit
    ⟨input.cols.access_timestamp, input.is_real, input.clk_target⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- the composed timestamp sub-assertion's two checks are gated receives (mult `-is_real`): their
  -- `byteChannel` *guarantee* propagates up here (the *requirement* is discharged inside the sub — W11
  -- Phase 0c — so `byteChannel` is dropped from `channelsWithRequirements` below).
  channelsWithGuarantees := [byteChannel.toRaw]

-- Expose the declared channel list + `localLength` as `@[circuit_norm]` rfl-lemmas so the composing
-- `RTypeReader`'s `channelsLawful` / `circuit_proof_start` is discharged automatically.
-- (`channelsWithRequirements` now lives on `circuit` below; Clean's generic def-lemma reduces it.)
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees
      : List (RawChannel (ZMod p))) = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the genuinely `is_real`-gated byte receives (and threaded
down to the composed `RegisterAccessTimestamp`). Discharged by the chip's gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  -- `Spec` = the composed timestamp sub-assertion's `Spec` (the two byte bounds); the sub gives it from
  -- `h_holds`, and the requirement tail is the sub's `is_real`-binary `Assumptions`.
  circuit_proof_start
  exact ⟨h_holds h_assumptions, Or.inr h_assumptions⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  -- provide the sub-assertion's ⟨Assumptions, Spec⟩: its `is_real`-binary `Assumptions` and its `Spec`
  -- (this reader's `Spec`, supplied as `h_spec`).
  circuit_proof_start
  exact ⟨h_assumptions, h_spec⟩

/-- The outer register-access reader as a Clean `FormalAssertion`: takes the chip-owned `cols` block plus
`is_real`/`clk_target`, composes the timestamp sub-assertion, with `Spec` the propagated byte bounds. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  -- `byteChannel` dropped (W11 Phase 0c): the composed `RegisterAccessTimestamp` sub-assertion now
  -- discharges its own off-gate byte-pull `Requirements` (inline `is_real` gate), so it contributes no
  -- `byteChannel` requirement here; only its `byteChannel` *guarantee* still propagates up.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end RegisterAccessCols

end SP1Clean.Readers
