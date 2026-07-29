import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Native.Operations.AddressOperation
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.ITypeReaderImmutable
import SP1Clean.Native.Readers.MemoryAccess
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `StoreDouble` chip row as a `GeneralFormalCircuit`

SP1's `StoreDouble` (SD): `mem[rs1 + signExtend(imm)] ← rs2`, 8-byte aligned, full 64-bit word. The
**write** counterpart of `LoadDouble`. Composes — as Clean sub-circuits — the `CPUState` reader
(pc+4 / clk+8), the `AddressOperation` gadget (address `= rs1 + imm` truncated to 48 bits, offset bits
`0`), the `MemoryAccess` primitive (a memory **write**: `new_value = rs2`, at the computed 48-bit
address), and the `ITypeReaderImmutable` adapter (op_a = rs2 **read**, op_b = rs1 read, op_c the
immediate). Output is the native `Columns` struct.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven `is_real`-binary fact;
the store *meaning* (the new memory word pushed at the address is the rs2 word
`adapter.op_a_memory.prev_value`) is carried by `MemoryAccess`'s `new_value` input being the rs2 read
value, with the bus's cross-row offline-memory meaning living at the trace level
(`Soundness/MemoryConsistency.lean`). Unlike LoadDouble there is **no** chip-level `op_a_0 = 0` gate —
op_a is a source read, and the `op_a_0` zeroing of the *read* `x0` value lives inside the immutable
reader's `Spec`. -/

namespace SP1Clean.StoreDoubleChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native StoreDouble-chip row (Rust field order). The reader and memory blocks reuse the project
substrate (`Extracted.AddressOperation` is still a standalone generated module — the other loads and
stores compose the same gadget; `Extracted.MemoryAccessCols` lives in the generated `MemoryAccess`
struct carrier). `Faithful.StoreDoubleChip.storeDoubleChipReconfigure` is the sole bridge to Rust's
separately generated whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  is_real : F
deriving ProvableStruct

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value (the
`op_b` register read), `op_c_imm` the sign-extended immediate; `state`/`adapter`/`memory_access` are the
committed CPUState / I-type-adapter / memory-access columns. The stored word is the rs2 read value
`adapter.op_a_memory.prev_value`. The `address_operation` block is the `AddressOperation` sub-circuit's
witnessed output, not an input. -/
structure Inputs (F : Type) where
  is_real : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

/-- The exact argument tuple passed to SP1's gated address operation. -/
@[reducible] def addressInput {F : Type} [OfNat F 0] (input : Inputs F) :
    AddressOperation.Inputs F :=
  ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_addressInput {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env (addressInput input) = addressInput (Eval.eval env input) := by
  simp only [addressInput, Inputs.op_b_val, Inputs.op_c_imm, eval_inputs]
  rw [ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.structEvalLiteralProc]
  rw [Readers.evalITypeColumns]
  repeat' rw [Readers.evalRegisterAccessColumns]
  simp only [Expression.eval]
  congr
  all_goals simp
  rw [← ProvableStruct.eval_eq_eval, eval_inputs]

/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- Compose the four column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (offset bits `0` — SD is
8-byte aligned); `MemoryAccess` is a write (`new_value = adapter.op_a_memory.prev_value`, the rs2 word) at
the 48-bit address; `ITypeReaderImmutable` reads op_a (rs2) / op_b (rs1) (opcode `39 = SD`). The `is_real`
binary gate is imposed directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩
  let addr_op ← AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
  let address := AddressOperation.alignedValue
    ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩ addr_op
  -- `MemoryAccess` and `ITypeReaderImmutable` are now `GeneralFormalCircuit`s (SC Phase 2pre) — composed
  -- via the GFC `CoeFun` (`let _ ←` discards the `unit` output). Their `Spec`s (Contracts) are unchanged.
  let _ ← Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      address[0], address[1], address[2],
      input.adapter.op_a_memory.prev_value, input.is_real⟩
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 39⟩
  assertZero (input.is_real * (input.is_real - 1))
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.is_real⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main where
  channelsLawful := by
    simp only [circuit_norm, main, AddressOperation.circuit, Readers.CPUState.circuit,
      Readers.ITypeReaderImmutable.circuit, Readers.MemoryAccess.circuit]
  -- only the `AddressOperation` subcircuit witnesses (its 65 columns); the other blocks are threaded
  -- inputs and the gate witnesses nothing.
  localLength _ := 3 + 1
  output input i0 :=
    ⟨input.state, input.adapter,
      ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩,
      input.memory_access, input.is_real⟩
  -- `programChannel` joins the byte guarantee propagated up from `ITypeReaderImmutable`'s program **pull** (W11 flip).
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw]

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨varFromOffset Extracted.AddrAddOperation offset, var ⟨offset + 3⟩⟩,
        input.memory_access, input.is_real⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of a completed StoreDouble row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         address_operation := Eval.eval env cols.address_operation
         memory_access := Eval.eval env cols.memory_access
         is_real := Eval.eval env cols.is_real } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity,
the `MemoryAccess` timestamp monotonicity (whose `new_value` is the rs2 word — the store meaning), the
`ITypeReaderImmutable` adapter facts (op_a/op_b reads + the `op_a_0` read-zeroing), and the
`is_real`-binary fact. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.RowSpec (addressInput input) cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      (AddressOperation.alignedValue (addressInput input) cols.address_operation)[0],
      (AddressOperation.alignedValue (addressInput input) cols.address_operation)[1],
      (AddressOperation.alignedValue (addressInput input) cols.address_operation)[2],
      input.adapter.op_a_memory.prev_value, input.is_real⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
      input.state.pc, 39⟩ ∧
  (input.is_real = 0 ∨ input.is_real = 1)

end SP1Clean.StoreDoubleChip
