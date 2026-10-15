import SP1Clean.Proofs.Chips.SyscallInstrsChip.Arms
import SP1Clean.Native.Readers.CPUState
import SP1Clean.Native.Readers.RegisterAccessCols
import SP1Clean.Circuits.Gadgets.IsZero
import SP1Clean.Circuits.Gadgets.U16Compare
import SP1Clean.Circuits.Gadgets.U16toU8Safe
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The `SyscallInstrs` row as a native circuit

SP1's ECALL table (contract: `FormalModel/Contracts/SyscallInstrsChip.lean`), written against the
complete extracted assertion and interaction lists of `Extracted/SystemOracle/SyscallInstrs.lean`
rather than against one arm of it.

**Shape.** A `Readers.CPUState` block at the syscall edge (`clk_inc = 264`, to the row's own
`next_pc`), three `Readers.RegisterAccessCols` timestamp sub-assertions at access clocks
`+4`/`+3`/`+2`, the committed `ECALL` Program fetch, and three register Memory pairs — of which
`t0`'s is a genuine **write** (read-prior carries the syscall identifier, read-back carries
`op_a_value`) while `a0` and `a1` are pure reads.

**Dispatch.** The identifier's byte split (`U16toU8OperationSafe`) yields byte 0, the identifier
proper, and byte 1, SP1's "this handler has its own table" flag. Five `IsZeroOperation` selectors
test byte 0 against the canonical codes, and byte 1 is the multiplicity of the send on
`syscallChannel`. With no provider for that channel, balance forces the routing byte to zero.
This does not prove enum membership: `CoreSyscallChip` separately checks the full-word native profile.

**Public values.** SP1 states five of its conjuncts against `public_values` directly. Clean's flat
AIR reserves the public input to the verifier row, so each becomes one message built from columns
this row already has (`docs/assurance.md`, the native-only-bus disclosure): the exit binding on
`exitChannel`, and the two commit digests and two commit flags on `publicValuesChannel`. No witness
cell is added, so the row keeps its upstream width.

Deliberately *not* here: the exit hand-off's padding push. `HaltChip` pushes a zero code on padding
rows because its table is exactly one row, which is what balanced the verifier's ungated pull. A
syscall table has many rows, so that accounting is redesigned when this chip joins the ensemble;
this file emits only the faithful `is_halt`-gated push. -/

namespace SP1Clean.SyscallInstrsChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  syscallChannel publicValuesChannel ProgramMsg MemoryMsg ExitMsg SyscallMsg PublicValueMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- A natural-number constant as a circuit expression. The arm codes and the field-limb bound are
`ℕ` in the contract, where they are compared against `ZMod.val`s; this lifts them for use in
constraints. -/
@[circuit_norm] def natConst (n : ℕ) : Expression (ZMod p) := Expression.const (n : ZMod p)

/-- The row's recombined 24-bit low clock. -/
@[circuit_norm] def clkLowVar (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.state.clk_0_16 + input.state.clk_16_24 * 65536

/-- Byte 0 of the syscall identifier — the code the five selectors test. -/
@[circuit_norm] def syscallIdVar (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.syscall_id_bytes.low_bytes[0]

/-- Byte 1 of the syscall identifier — SP1's "the handler of this system call has its own table"
flag, and the multiplicity of the `syscallChannel` send. -/
@[circuit_norm] def tableByteVar (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  (input.op_a_memory.prev_value[0] - input.syscall_id_bytes.low_bytes[0]) * (256 : ZMod p)⁻¹

/-- A four-limb word's field reduction, `w0 + w1·2^16 + w2·2^32 + w3·2^48` — SP1's `b().reduce()`,
with the upstream coefficients written as products so the expression matches limb-wise. -/
@[circuit_norm] def reduceWord (w : Var Word (ZMod p)) : Expression (ZMod p) :=
  w[0] + (w[1] + (w[2] + w[3] * 65536) * 65536) * 65536

/-- The committed `ECALL` fetch at the row's pc: opcode `50`, the three register operands, and the
`op_a_0` flag the x0 rule reads. -/
@[circuit_norm] def programMsg (input : Var Inputs (ZMod p)) : ProgramMsg (Expression (ZMod p)) :=
  ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 50,
   input.op_a, #v[input.op_b, 0, 0, 0], #v[input.op_c, 0, 0, 0], input.op_a_0, 0, 0⟩

/-- A register access's **read-prior** Memory pull, at the record's pulled timestamp. -/
@[circuit_norm] def memPullMsg (input : Var Inputs (ZMod p))
    (block : Circuits.Types.RegisterAccessCols (Expression (ZMod p)))
    (idx : Expression (ZMod p)) : MemoryMsg (Expression (ZMod p)) :=
  ⟨input.state.clk_high, block.access_timestamp.prev_low, idx, 0, 0, block.prev_value⟩

/-- A register access's **read-back** Memory push, at this row's access clock, carrying `value` —
the prior word for a pure read, the written word for `t0`. -/
@[circuit_norm] def memPushMsg (input : Var Inputs (ZMod p))
    (idx off : Expression (ZMod p)) (value : Var Word (ZMod p)) :
    MemoryMsg (Expression (ZMod p)) :=
  ⟨input.state.clk_high, clkLowVar input + off, idx, 0, 0, value⟩

/-- The generic-syscall hand-off, sent at multiplicity `tableByteVar`. Its payload is the shared
`SyscallMsg`, the same carrier the exact v6.4.0 lists project: the clock pair, the identifier, and
the low three limbs of each operand. -/
@[circuit_norm] def syscallMsg (input : Var Inputs (ZMod p)) : SyscallMsg (Expression (ZMod p)) :=
  ⟨input.state.clk_high, clkLowVar input, syscallIdVar input,
   #v[input.op_b_memory.prev_value[0], input.op_b_memory.prev_value[1],
      input.op_b_memory.prev_value[2]],
   #v[input.op_c_memory.prev_value[0], input.op_c_memory.prev_value[1],
      input.op_c_memory.prev_value[2]]⟩

/-- The exit-bus payload: the reduced `a0` word. With the gated upper-limb pins and the
`fieldLimbBound` compare below, its value is at most the modulus less one, so the single committed
cell decodes back to `a0`. -/
@[circuit_norm] def exitMsg (input : Var Inputs (ZMod p)) : ExitMsg (Expression (ZMod p)) :=
  ⟨reduceWord input.op_b_memory.prev_value⟩

/-- The commit index bitmap's sum, `Σ bitᵢ` — one on a commit arm, zero otherwise. -/
@[circuit_norm] def bitSum (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.digest_index_bits[0] + input.digest_index_bits[1] + input.digest_index_bits[2] +
    input.digest_index_bits[3] + input.digest_index_bits[4] + input.digest_index_bits[5] +
    input.digest_index_bits[6] + input.digest_index_bits[7]

/-- The one-hot selected base index into a public-values block: `Σ bitᵢ · (base + strideᵢ)`. -/
@[circuit_norm] def selectedIndex (input : Var Inputs (ZMod p)) (base stride : ℕ) :
    Expression (ZMod p) :=
  (List.finRange 8).foldl
    (fun acc i => acc + input.digest_index_bits[i] * natConst (base + stride * i.val)) 0

/-- The syscall row. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Shallow booleanity gates, so every off-gate pull discharges its `Requirements`.
  assertZero (input.is_real * (input.is_real - 1))
  assertZero (input.is_commit.result * (input.is_commit.result - 1))
  assertZero (input.is_commit_deferred.result * (input.is_commit_deferred.result - 1))
  assertZero (input.is_halt * (input.is_halt - 1))
  assertZero (tableByteVar input * (tableByteVar input - 1))

  -- The identifier's byte split, and the five arm selectors on byte 0.
  assertion U16toU8OperationSafe.circuit
    ⟨input.op_a_memory.prev_value, input.syscall_id_bytes, input.is_real⟩
  assertion IsZeroOperation.circuit
    ⟨syscallIdVar input - natConst haltCode, input.is_halt_zero, input.is_real⟩
  assertion IsZeroOperation.circuit
    ⟨syscallIdVar input - natConst enterUnconstrainedCode, input.is_enter_unconstrained, input.is_real⟩
  assertion IsZeroOperation.circuit
    ⟨syscallIdVar input - natConst hintLenCode, input.is_hint_len, input.is_real⟩
  assertion IsZeroOperation.circuit
    ⟨syscallIdVar input - natConst commitCode, input.is_commit, input.is_real⟩
  assertion IsZeroOperation.circuit
    ⟨syscallIdVar input - natConst commitDeferredCode, input.is_commit_deferred, input.is_real⟩
  -- `is_halt` carries the `is_real` factor already.
  assertZero (input.is_halt - input.is_halt_zero.result * input.is_real)
  -- Padding rows select nothing and dispatch nothing.
  assertZero ((input.is_real - 1) * tableByteVar input)
  assertZero ((input.is_real - 1) * input.is_halt)
  assertZero ((input.is_real - 1) * input.is_commit_deferred.result)

  -- The state edge: pull `(clk, pc)`, push `(clk + 264, next_pc)`.
  let _ ← Readers.CPUState.circuit ⟨input.state, input.next_pc, 264, input.is_real⟩
  -- Per-register timestamp byte checks at the standard access offsets.
  assertion Readers.RegisterAccessCols.circuit
    ⟨input.op_a_memory, input.is_real, clkLowVar input + 4⟩
  assertion Readers.RegisterAccessCols.circuit
    ⟨input.op_b_memory, input.is_real, clkLowVar input + 3⟩
  assertion Readers.RegisterAccessCols.circuit
    ⟨input.op_c_memory, input.is_real, clkLowVar input + 2⟩
  -- The committed `ECALL` at `pc`.
  programChannel.pullIf input.is_real (programMsg input)

  -- `t0` is written; `a0` and `a1` are read back unchanged.
  memoryChannel.pullIf input.is_real (memPullMsg input input.op_a_memory input.op_a)
  memoryChannel.pushIf input.is_real (memPushMsg input input.op_a 4 input.op_a_value)
  memoryChannel.pullIf input.is_real (memPullMsg input input.op_b_memory input.op_b)
  memoryChannel.pushIf input.is_real
    (memPushMsg input input.op_b 3 input.op_b_memory.prev_value)
  memoryChannel.pullIf input.is_real (memPullMsg input input.op_c_memory input.op_c)
  memoryChannel.pushIf input.is_real
    (memPushMsg input input.op_c 2 input.op_c_memory.prev_value)

  -- The five arms, each a bundled assertion (`Native/Chips/SyscallInstrsChip/Arms.lean`).
  assertion WriteArm.circuit
    ⟨input.op_a_memory.prev_value, input.op_a_value, input.op_a_0,
     input.is_enter_unconstrained.result, input.is_hint_len.result, input.is_real⟩
  assertion PcArm.circuit ⟨input.state.pc, input.next_pc, input.is_real, input.is_halt⟩
  assertion DispatchArm.circuit
    ⟨input.op_b_memory.prev_value, input.op_c_memory.prev_value, tableByteVar input⟩
  -- The same valid-field-element bound, on `a0` for HALT and on `a1` for COMMIT_DEFERRED.
  assertion FieldBoundArm.circuit
    ⟨input.op_b_memory.prev_value, input.op_b_cmp.bit, input.is_halt⟩
  assertion FieldBoundArm.circuit
    ⟨input.op_c_memory.prev_value, input.op_c_cmp.bit, input.is_commit_deferred.result⟩
  assertion CommitArm.circuit
    ⟨input.digest_index_bits, input.digest_word, input.op_b_memory.prev_value,
     input.op_c_memory.prev_value, input.is_commit.result, input.is_commit_deferred.result,
     input.is_real⟩

  -- `op_a_value` is a valid word even on the one arm that leaves it free (`HINT_LEN`): SP1's
  -- `slice_range_check_u16`. This is what lets the `t0` read-back push discharge the Memory bus's
  -- `isU64` requirement without any profile restriction.
  byteChannel.pullIf input.is_real ⟨6, input.op_a_value[0], natConst 16, 0⟩
  byteChannel.pullIf input.is_real ⟨6, input.op_a_value[1], natConst 16, 0⟩
  byteChannel.pullIf input.is_real ⟨6, input.op_a_value[2], natConst 16, 0⟩
  byteChannel.pullIf input.is_real ⟨6, input.op_a_value[3], natConst 16, 0⟩
  -- The cached digest word is four genuine bytes, checked in pairs.
  byteChannel.pullIf input.is_commit.result
    ⟨3, 0, input.digest_word[0], input.digest_word[1]⟩
  byteChannel.pullIf input.is_commit.result
    ⟨3, 0, input.digest_word[2], input.digest_word[3]⟩

  -- The five public-value bindings, each one message built from columns above (see the docstring).
  exitChannel.pushIf input.is_halt (exitMsg input)
  publicValuesChannel.pullIf input.is_commit.result ⟨natConst 145, 1⟩
  publicValuesChannel.pullIf input.is_commit_deferred.result ⟨natConst 147, 1⟩
  publicValuesChannel.pullIf input.is_commit.result
    ⟨selectedIndex input 32 4 + 0, input.digest_word[0]⟩
  publicValuesChannel.pullIf input.is_commit.result
    ⟨selectedIndex input 32 4 + 1, input.digest_word[1]⟩
  publicValuesChannel.pullIf input.is_commit.result
    ⟨selectedIndex input 32 4 + 2, input.digest_word[2]⟩
  publicValuesChannel.pullIf input.is_commit.result
    ⟨selectedIndex input 32 4 + 3, input.digest_word[3]⟩
  publicValuesChannel.pullIf (input.is_real * input.is_commit_deferred.result)
    ⟨selectedIndex input 72 1, reduceWord input.op_c_memory.prev_value⟩

  -- The generic hand-off: multiplicity is the identifier's table byte.
  syscallChannel.pushIf (tableByteVar input) (syscallMsg input)

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  localLength_eq := by
    preserve_tactic_target
    intro input offset
    simp only [circuit_norm, main, Readers.CPUState.circuit,
      Readers.RegisterAccessCols.circuit, IsZeroOperation.circuit,
      U16toU8OperationSafe.circuit]
  -- Every bus the row touches. Byte arrives through the readers and the three gadget families;
  -- State through `CPUState`; Program, Memory, Exit, Syscall and PublicValues directly.
  channelsWithGuarantees :=
    [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
     exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw]
  channelsLawful := by
    preserve_tactic_target
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    dsimp only [Operations.ChannelsLawful]
    refine ⟨by simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit, IsZeroOperation.circuit,
        U16toU8OperationSafe.circuit], ?_,
      by simp only [circuit_norm, main, Readers.CPUState.circuit,
        Readers.RegisterAccessCols.circuit, IsZeroOperation.circuit,
        U16toU8OperationSafe.circuit]⟩
    intro env
    rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
    intro interaction h_interaction
    simp only [circuit_norm, main, Readers.CPUState.circuit,
      Readers.RegisterAccessCols.circuit, IsZeroOperation.circuit,
      U16toU8OperationSafe.circuit] at h_interaction
    refine Or.inl ?_
    rcases h_interaction with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h <;>
      subst h <;> simp only [circuit_norm]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.SyscallInstrsChip
