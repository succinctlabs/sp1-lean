import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Proofs.Operations.LtOperationSigned.Formal
import SP1Clean.Native.Operations.LtOperationSigned.Populate
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ALUTypeReader
import SP1Clean.Native.Readers.RegisterWrite
import SP1Clean.Model.Channels
import SP1Clean.Extracted.LtChip
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The unified `Lt` chip row (SLT + SLTU) as a `GeneralFormalCircuit`

Keyed on SP1's unified `Extracted.LtCols` (`is_slt`/`is_sltu` selectors), composing the signed gadget
`LtOperationSigned` (unsigned core + two `U16MSBOperation` sign columns) and the immediate-capable
`ALUTypeReader`. Soundness and completeness are proven and axiom-clean (flag-dispatched through
`LtOperationSigned.Spec`, mapping the compare `bit` to RV64 `slt`/`sltu`). -/

namespace SP1Clean.LtChip

open Circuit
open Extracted (LtCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `is_real` selector and the threaded committed reader column blocks `state`/`adapter` (the latter
an immediate-capable `ALUTypeReader`). The `rs1`/`rs2` operands are projected from the adapter (the
Memory-bus values) — see `Inputs.op_b_val` below — rather than carried as separate committed columns. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ALUTypeReader F
deriving ProvableStruct

/-- `rs1` operand = the `op_b` register read (`op_b_memory.prev_value`); `rs2` operand = the ALU operand
word `adapter.op_c` (the `op_c` register read, or the immediate). -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c

/-- **Assertion half** — the literal meaning of SP1's `LtCols.asserts` *own* (inline) assertZero tail
(everything past the composed `LtOperationSigned`/`CPUState`/`ALUTypeReader` sub-lists), in extracted
order (`Extracted/LtChip.lean`: `E2, E4, E6, op_a_0`): the two variant-flag booleans (`is_slt`,
`is_sltu`), the sum-bound boolean on `E0 = is_slt + is_sltu`, and the `op_a_0` zeroing flag. The
signed/unsigned compare arithmetic is *not* here — it is the composed `LtOperationSigned` sub-list. -/
def AssertSpec (cols : LtCols (ZMod p)) : Prop :=
  let s := cols.is_slt; let u := cols.is_sltu
  let sum := s + u
  s * (s - 1) = 0 ∧
  u * (u - 1) = 0 ∧
  sum * (sum - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

/-- **Interaction half** — SP1's `LtCols.interactions` *own* tail is **empty** (`Extracted/LtChip.lean`
ends `… ++ [ ]`): every byte-range pull for the compare lives inside the composed `LtOperationSigned`
sub-list (the unsigned-core limb checks, the `U16MSB` sign-bit ranges), anchored at the operation level.
So the chip's own interaction meaning is trivial. -/
def InteractSpec (_cols : LtCols (ZMod p)) : Prop := True

/-- The set-less-than result word the reader writes for `rd`: the compare bit (from the gadget's unsigned
core) in the low limb, zeros above. -/
def resultWord (cols : LtCols (ZMod p)) : Word (ZMod p) :=
  #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]

/-- The two honest variant flags (`is_slt`, `is_sltu`) the prover supplies via the `"lt_flags"`
hint key (one-hot for the active variant, all-zero on padding). -/
def hintFlags (h : ProverHint (ZMod p)) : Vector (ZMod p) 2 :=
  ((h "lt_flags" 2)[0]?).getD #v[0, 0]

/-- Compose `Readers.CPUState.circuit` (forms `next_pc = [pc[0]+4, …]`, `clk_inc = 8`), **witness** the
two variant flags `is_slt`/`is_sltu`, compose the witnessed `LtOperationSigned` gadget (`subcircuit`, the
`is_signed := is_slt` mode selector), and `Readers.ALUTypeReader.circuit` (opcode `is_slt·9 + is_sltu·10`;
the `rd` write value is `[bit, 0, 0, 0]` from the gadget's compare bit), gate `is_real`, emit the two flag
booleans + their sum-bound (`AssertSpec`, needed by soundness to force `is_slt = 0` in the `SLTU` branch),
and assemble the extracted `LtCols` struct. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var LtCols (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let flags ← witnessVectorNative 2 (fun env => hintFlags env.hint)
  let is_slt := flags[0]; let is_sltu := flags[1]
  -- The chip witnesses the `LtOperationSigned` column struct (the unsigned compare block + the two
  -- sign-bit columns) via `populate`, then composes `LtOperationSigned.circuit` as a Clean `assertion`
  -- (it is a `FormalAssertion`, witnessing nothing of its own; `is_signed := is_slt`).
  let lt_cols ← witnessNative (var := Var Extracted.LtOperationSigned) (fun env =>
    LtOperationSigned.populate
      #v[env input.op_b_val[0], env input.op_b_val[1], env input.op_b_val[2], env input.op_b_val[3]]
      #v[env input.op_c_val[0], env input.op_c_val[1], env input.op_c_val[2], env input.op_c_val[3]]
      (env is_slt) (env input.is_real))
  assertion LtOperationSigned.circuit ⟨input.op_b_val, input.op_c_val, lt_cols, is_slt, input.is_real⟩
  -- `ALUTypeReader` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ALUTypeReader.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
     input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
     is_slt * 9 + is_sltu * 10,
     lt_cols.result.u16_compare_operation.bit, 0, 0, 0⟩
  -- Option B: the op_a (`rd`) write Memory **push** is composed here (factored OUT of the reader), *after*
  -- `LtOperationSigned`, so `isU64 (resultWord)` discharges its requirement. The Lt result is the single
  -- compare bit in the low limb (zeros above): `#v[bit, 0, 0, 0]`; the write access clock is `recombined + 4`.
  assertion Readers.RegisterWrite.circuit
    ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
     input.adapter.op_a, #v[lt_cols.result.u16_compare_operation.bit, 0, 0, 0], input.is_real⟩
  -- Inline `assertZero` (not `=== 0`) so the `is_real` booleanity is visible to
  -- `ConstraintsHold.Shallow` — required for the chip to be a `VmTables` table (A2).
  assertZero (input.is_real * (input.is_real - 1))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * ((is_slt + is_sltu) - 1) === 0
  return ⟨input.state, input.adapter, is_slt, is_sltu, lt_cols⟩

set_option maxHeartbeats 1000000 in
instance elaborated : ElaboratedCircuit (ZMod p) Inputs LtCols main where
  channelsLawful := by simp [circuit_norm, main, LtOperationSigned.circuit, Readers.ALUTypeReader.circuit, Readers.CPUState.circuit, Readers.RegisterWrite.circuit]
  -- witnesses the two flags (2) + the `LtOperationSigned` block (1 + 1 + 8 = 10); the readers/write are
  -- `assertion`s (`localLength 0`) over the threaded `state`/`adapter` inputs. 2 + 10 = 12.
  localLength _ := 12
  -- `programChannel` joins the byte guarantee propagated up from `ALUTypeReader`'s program **pull** (W11 flip);
  -- `memoryChannel` joins from `ALUTypeReader`'s memory read **pulls** (W11 memory flip). The `RegisterWrite`
  -- op_a write push owes a memory requirement (declared in `circuit.channelsWithRequirements`), not a guarantee.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.LtChip
