import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.MemoryAccess
import SP1Clean.MemoryBusTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Clean.SP1Lookup

/-! # `RegisterAccess.assertion` — one register-access subcircuit per operand

Mirrors SP1's `eval_register_access_read` / `eval_register_access_write`
from `crates/core/machine/src/air/memory.rs` (called per operand by
`r_type.rs` / `i_type.rs` / `alu_type.rs`). Each call emits:

1. The byte-bus content (3 byte lookups) via `OperandAccess.assertionGated`
   — `diff_low_limb < 65536`, scaled timestamp < 256, `Word.isU64 prev_value`.
2. One **memory-bus send** at `(clk_high, prev_low, op_idx, 0, 0, prev_value)`
   via `lookupGated MemoryBusTable … mult` — records the row's "read the
   previous value" contribution to the multiplicity-weighted bus.
3. One **memory-bus receive** at `(clk_high, clk_low + offset, op_idx, 0,
   0, write_value)` via `lookupGated MemoryBusTable … mult` — records the
   "write the new value" contribution.

The MemoryBusTable's `Contains` is `True` (per-row table-membership is
trivial); per-key multiplicity balance is enforced at the trace level by
`LookupAccessList.isConsistentBalanced` from `SP1Lookup.lean`. So
row-level `Spec` here matches `OperandAccess.AssertionGated.Spec`
exactly — the memory-bus calls add no row-level facts.

For read-only operands (op_b, op_c in R-type), `write_value = prev_value`
(the read passes through unchanged); for written operands (op_a in
R-type), `write_value` is the chip's computed result. -/

namespace SP1Clean.RegisterAccess

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

-- Derive `Fact (p > 512)` from `Fact (2 ^ 17 < p)` for byteOpcodeGated.
instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Inputs for the per-operand register-access assertion. Extends
`OperandAccess.AssertionGated.Inputs` with the memory-bus address
(`clk_high`, `op_idx`) and the `write_value` that the row writes back. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  offset : F
  op_idx : F
  prev_value : Vector F 4
  write_value : Vector F 4
  prev_low : F
  diff_low_limb : F
  mult : F
deriving ProvableStruct

/-- Emit the byte-bus byte lookups (via `OperandAccess.assertionGated`)
plus the two memory-bus interactions (via `SP1Lookup.memoryBusGated`):
a send of `prev_value` at the `prev_low` timestamp and a receive of
`write_value` at the `clk_low + offset` timestamp. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Byte-bus content (diff_low_limb range, scaled-timestamp range, prev_value U64).
  SP1Clean.OperandAccess.assertionGated
    (⟨input.clk_low, input.offset, input.prev_low,
       input.diff_low_limb, input.prev_value, input.mult⟩ :
      Var SP1Clean.OperandAccess.AssertionGated.Inputs (ZMod p))
  -- Memory-bus send: "row reads prev_value at prev_low timestamp".
  SP1Lookup.memoryBusGated
    (⟨#v[input.clk_high, input.prev_low, input.op_idx, 0, 0,
         input.prev_value[0], input.prev_value[1],
         input.prev_value[2], input.prev_value[3]],
      input.mult⟩ : Var SP1Lookup.MemoryBusGated.Inputs (ZMod p))
  -- Memory-bus receive: "row writes write_value at clk_low + offset timestamp".
  SP1Lookup.memoryBusGated
    (⟨#v[input.clk_high, input.clk_low + input.offset, input.op_idx, 0, 0,
         input.write_value[0], input.write_value[1],
         input.write_value[2], input.write_value[3]],
      input.mult⟩ : Var SP1Lookup.MemoryBusGated.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.RegisterAccess"
  main := main
  -- Computed from main: 1 byteOpcodeGated subcircuit (24) + 2 lookupGated
  -- on MemoryBusTable (each witnesses `size (fields 9) = 9`) = 24 + 18 = 42.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Row-level `Spec`: matches `OperandAccess.AssertionGated.Spec` — the
memory-bus emissions add no row-level facts (MemoryBus.Contains = True;
per-key balance is trace-level). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.OperandAccess.AssertionGated.Spec
    ⟨input.clk_low, input.offset, input.prev_low, input.diff_low_limb,
     input.prev_value, input.mult⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_oa_sub, _h_send_sub, _h_recv_sub⟩ := h_holds
  -- The byte-bus subcircuit's Spec IS our row-level Spec (the memory-bus
  -- subcircuits contribute trivial True).
  exact h_oa_sub trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  -- Three subcircuits to satisfy: OperandAccess (gets h_spec) and 2
  -- memoryBusGated calls (whose Spec is `Or.inr trivial` since
  -- MemoryBusTable accepts any entry).
  refine ⟨⟨trivial, h_spec⟩, ⟨trivial, Or.inr trivial⟩,
          ⟨trivial, Or.inr trivial⟩⟩

end Assertion

/-- The full Clean `FormalAssertion` for one per-operand register access.
Composes `OperandAccess.assertionGated` (byte bus) plus 2 `lookupGated`
calls on `MemoryBusTable` (memory bus send + receive). -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.RegisterAccess
