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

/-! # The `LoadX0` chip row as a `GeneralFormalCircuit`

SP1's `LoadX0` is the fast path for **loads whose destination register is `x0`** (the hardwired-zero
register). One chip bundles all seven load opcodes (`LB, LBU, LH, LHU, LW, LWU, LD`) behind seven
mutually-exclusive selectors. The memory read still happens (for side effects / fault checking), but the
loaded value is **discarded** (`wX 0 _` is a no-op), so the only observable effect is `nextPC = pc + 4`.

Composes — as Clean sub-circuits — the `CPUState` reader (pc+4 / clk+8), the `AddressOperation` gadget
(address `= rs1 + imm` truncated to 48 bits, with the three real offset bits), the `MemoryAccess`
primitive (a memory **read**: `new_value = prev_value`, at the computed 48-bit address), and the
`ITypeReaderImmutable` adapter (op_a a source **read**, no write value — the loaded word is never
written). The opcode fed to the reader is the weighted selector sum
`29·is_lb + 32·is_lbu + 30·is_lh + 33·is_lhu + 31·is_lw + 34·is_lwu + 35·is_ld`.

The chip `Spec` is the composition of the sub-circuits' own `Spec`s + the proven selector binaries / the
`is_real`-binary fact + the three per-width alignment equations + the two `op_a_0` forcing gates (which
pin `op_a_0 = is_real`, i.e. `op_a = x0` on real rows). Output is the extracted `Columns`. -/

namespace SP1Clean.LoadX0Chip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native LoadX0-chip row (Rust field order). A bespoke reader-only row: the `ITypeReader` block is
read through both `ITypeReader` and `ITypeReaderImmutable` assertion families, there is no value
logic, and the seven per-width selectors replace a single `is_real`. The reader and memory blocks
reuse the project substrate (`Extracted.AddressOperation` is still a standalone generated module;
`Extracted.MemoryAccessCols` lives in the generated `MemoryAccess` struct carrier).
`Faithful.LoadX0Chip.loadX0ChipReconfigure` is the sole bridge to Rust's separately generated
whole-chip row. -/
structure Columns (F : Type) where
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  address_operation : Extracted.AddressOperation F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : Vector F 3
  is_lb : F
  is_lbu : F
  is_lh : F
  is_lhu : F
  is_lw : F
  is_lwu : F
  is_ld : F
deriving ProvableStruct

/-- The operand reads + threaded reader column blocks. `op_b_val` is the rs1 base-address value (the
`op_b` register read), `op_c_imm` the sign-extended immediate; the seven selectors flag the active load
opcode; `state`/`adapter`/`memory_access` are the committed CPUState / I-type-adapter / memory-access
columns, `offset_bit` the low 3 bits of the address. The `address_operation` block is the
`AddressOperation` sub-circuit's witnessed output, not an input. -/
structure Inputs (F : Type) where
  is_lb : F
  is_lbu : F
  is_lh : F
  is_lhu : F
  is_lw : F
  is_lwu : F
  is_ld : F
  state : Extracted.CPUState F
  adapter : Extracted.ITypeReader F
  memory_access : Extracted.MemoryAccessCols F
  offset_bit : fields 3 F
deriving ProvableStruct

@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
@[reducible] def Inputs.op_c_imm {F} (i : Inputs F) : Word F := i.adapter.op_c_imm

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_lb := Eval.eval env input.is_lb
         is_lbu := Eval.eval env input.is_lbu
         is_lh := Eval.eval env input.is_lh
         is_lhu := Eval.eval env input.is_lhu
         is_lw := Eval.eval env input.is_lw
         is_lwu := Eval.eval env input.is_lwu
         is_ld := Eval.eval env input.is_ld
         state := Eval.eval env input.state
         adapter := Eval.eval env input.adapter
         memory_access := Eval.eval env input.memory_access
         offset_bit := Eval.eval env input.offset_bit } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl


/-- The recombined low clock `clk_0_16 + clk_16_24 · 2^16` (matching SP1's `clk_low`). -/
@[reducible] def clkLow (state : Extracted.CPUState (ZMod p)) : ZMod p :=
  state.clk_0_16 + state.clk_16_24 * 65536

/-- The umbrella `is_real` selector — the sum of the seven mutually-exclusive opcode flags. -/
@[reducible] def isReal (input : Inputs (ZMod p)) : ZMod p :=
  input.is_lb + input.is_lbu + input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld

/-- The weighted opcode value fed to the reader's Program bus. -/
@[reducible] def opcodeVal (input : Inputs (ZMod p)) : ZMod p :=
  29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu
    + 31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld

/-- Compose the four column blocks as Clean sub-circuits and assemble the extracted `Columns`.
`CPUState` advances pc by 4 / clk by 8; `AddressOperation` computes `rs1 + imm` (with the three real
offset bits); `MemoryAccess` is a read (`new_value = prev_value`) at the 48-bit address;
`ITypeReaderImmutable` reads op_a / op_b (opcode the weighted selector sum). The seven selector binaries,
the `is_real` binary, the three per-width alignment gates, and the two `op_a_0` forcing gates are imposed
directly. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Columns (ZMod p)) := do
  let is_real := input.is_lb + input.is_lbu + input.is_lh + input.is_lhu
    + input.is_lw + input.is_lwu + input.is_ld
  let opcode := 29 * input.is_lb + 32 * input.is_lbu + 30 * input.is_lh + 33 * input.is_lhu
    + 31 * input.is_lw + 34 * input.is_lwu + 35 * input.is_ld
  let _ ← Readers.CPUState.circuit
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, is_real⟩
  let addr_op ← AddressOperation.circuit
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
  let address := AddressOperation.alignedValue
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], is_real⟩
    addr_op
  -- `MemoryAccess` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`
  -- (`subcircuitWithAssertion`), discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.MemoryAccess.circuit
    ⟨input.memory_access, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      address[0], address[1], address[2],
      input.memory_access.prev_value, is_real⟩
  -- `ITypeReaderImmutable` is now a `GeneralFormalCircuit` (SC Phase 2pre) — composed via the GFC `CoeFun`,
  -- discarding its `unit` output. Its `Spec` (Contracts) is unchanged.
  let _ ← Readers.ITypeReaderImmutable.circuit
    ⟨input.adapter, is_real, is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, opcode⟩
  input.is_lb * (input.is_lb - 1) === 0
  input.is_lbu * (input.is_lbu - 1) === 0
  input.is_lh * (input.is_lh - 1) === 0
  input.is_lhu * (input.is_lhu - 1) === 0
  input.is_lw * (input.is_lw - 1) === 0
  input.is_lwu * (input.is_lwu - 1) === 0
  input.is_ld * (input.is_ld - 1) === 0
  assertZero (is_real * (is_real - 1))
  input.is_ld * input.offset_bit[2] === 0
  (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1] === 0
  (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[0] === 0
  is_real * (input.adapter.op_a_0 - 1) === 0
  (is_real - 1) * input.adapter.op_a_0 === 0
  return ⟨input.state, input.adapter, addr_op, input.memory_access, input.offset_bit,
    input.is_lb, input.is_lbu, input.is_lh, input.is_lhu, input.is_lw, input.is_lwu, input.is_ld⟩

/-- Derive the four address witness cells and the complete four-channel interface from `main`. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs Columns main := by
  elaborate_circuit

/-- Folded completed-row layout used by the whole-chip Rust AIR codec. -/
@[circuit_norm] lemma directOutput_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    (elaborated (p := p)).output input offset =
      (⟨input.state, input.adapter,
        ⟨varFromOffset Extracted.AddrAddOperation offset, var ⟨offset + 3⟩⟩,
        input.memory_access, input.offset_bit, input.is_lb, input.is_lbu,
        input.is_lh, input.is_lhu, input.is_lw, input.is_lwu, input.is_ld⟩ :
        Var Columns (ZMod p)) := rfl

/-- Component-wise evaluation of a completed LoadX0 row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         address_operation := Eval.eval env cols.address_operation
         memory_access := Eval.eval env cols.memory_access
         offset_bit := Eval.eval env cols.offset_bit
         is_lb := Eval.eval env cols.is_lb
         is_lbu := Eval.eval env cols.is_lbu
         is_lh := Eval.eval env cols.is_lh
         is_lhu := Eval.eval env cols.is_lhu
         is_lw := Eval.eval env cols.is_lw
         is_lwu := Eval.eval env cols.is_lwu
         is_ld := Eval.eval env cols.is_ld } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Semantic contract, composed from the sub-circuits' `Spec`s. The `AddressOperation` address identity,
the `MemoryAccess` timestamp monotonicity (a read), the `ITypeReaderImmutable` adapter facts (op_a/op_b
reads + the `op_a_0` read-zeroing — the loaded word is discarded), the seven selector binaries, the
`is_real`-binary fact, the three per-width alignment equations, and the two `op_a_0` forcing gates. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  AddressOperation.RowSpec
    ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
      input.offset_bit[2], isReal input⟩
    cols.address_operation ∧
  Readers.MemoryAccess.Spec
    ⟨input.memory_access, input.state.clk_high, clkLow input.state,
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[0],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[1],
      (AddressOperation.alignedValue
        ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0], input.offset_bit[1],
          input.offset_bit[2], isReal input⟩
        cols.address_operation)[2],
      input.memory_access.prev_value, isReal input⟩ ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
      input.state.pc, opcodeVal input⟩ ∧
  (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
  (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
  (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
  (input.is_ld = 0 ∨ input.is_ld = 1) ∧
  (isReal input = 0 ∨ isReal input = 1) ∧
  input.is_ld * input.offset_bit[2] = 0 ∧
  (input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[1] = 0 ∧
  (input.is_lh + input.is_lhu + input.is_lw + input.is_lwu + input.is_ld) * input.offset_bit[0] = 0 ∧
  isReal input * (input.adapter.op_a_0 - 1) = 0 ∧
  (isReal input - 1) * input.adapter.op_a_0 = 0

end SP1Clean.LoadX0Chip
