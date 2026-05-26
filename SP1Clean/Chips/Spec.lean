import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.Chips.Structs
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.ITypeReaderImmutable
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Reader.JTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.AddressShape
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.AddwOperation
import SP1Clean.Operations.SubOperation
import SP1Clean.Operations.SubwOperation
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Operations.IsZeroOperation
import SP1Clean.Operations.IsZeroWordOperation
import SP1Clean.Operations.IsEqualWordOperation
import SP1Clean.Operations.GatedAddOp
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.LoadByteSelector
import SP1Clean.Operations.LoadHalfSelector
import SP1Clean.Operations.LoadWordSelector
import SP1Clean.Operations.LoadMemoryAccessGated
import SP1Clean.Operations.StoreMemoryAccessGated
import SP1Clean.Operations.StoreByteAssembler
import SP1Clean.Operations.StoreHalfAssembler
import SP1Clean.Operations.StoreWordAssembler
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # Unified chip `FormalSpec` definitions

Central audit point for every IN-USE chip's `FormalSpec` (and `AssertionGated.FormalSpec`
for the Memory chips). Each chip's `Cols.lean` / `Aggregate.lean` /
single-file imports this module and references `FormalSpec` unqualified
from within its `namespace Assertion` / `namespace AssertionGated` blocks
(name resolution walks the surrounding namespace tree). Pattern A chips
also keep an `abbrev FormalSpec := @SP1Clean.<X>.FormalSpec p` in their
`Circuit.lean` that re-exports the chip-namespace-level definition into
`Assertion`.

Organization mirrors `SP1Clean/Chips/` directory layout: ALU → Control →
Memory. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## ALU chips -/

namespace SP1Clean.Add

/-- The unified chip Spec for `AddChip`. Conjuncts:
- `CPUState.Gated.Assertion.Spec` — flag-threaded CPUState sub-circuit
  composition (binary gate + 2 state-bus + 2 byte-opcode, all gated by
  `cols.is_real`). The chip-level `is_real * (is_real - 1) = 0` gate is
  now this Spec's first conjunct.
- `RTypeReader.Gated.Assertion.Spec` — flag-threaded R-type reader
  sub-circuit composition (binary gate + program + 3 register accesses +
  4 op_a_0 mask gates), gated by `cols.is_real` / `cols.adapter_cols.is_trusted`.
- `adapter.op_a_0 = 0` — chip-level `op_a_0` zero gate (distinct from
  the 4× `op_a_0 * op_a_write_value[i] = 0` masked gates inside the
  reader's Gated.Spec).
- Semantic RV64 conjunct (conditional on `is_real = 1`): the result
  fits in 64 bits AND equals the BitVec `RV64.add` of the operands. The
  byte-carry decomposition that the SP1 `AddOperation` circuit threads
  internally is *not* exposed here; it's the implementation detail of
  the `AddOp` sub-circuit and is reconstructed on demand via
  `SP1Clean.AddOp.iff_sp1_full` (see `Lemmas.lean`). The monadic Sail
  equivalence to `_root_.Add.spec_add` is recovered externally via
  `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def FormalSpec (cols : AddCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 0, cols.state.pc,
       cols.op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    Word.toBitVec64 cols.op_a_write_value =
      RV64.add (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
               (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Add

namespace SP1Clean.Addi

/-- The unified chip Spec for `AddiChip`. Conjuncts:
- `CPUState.Gated.Assertion.Spec` — flag-threaded CPUState sub-circuit
  composition (binary gate + 2 state-bus + 2 byte-opcode, all gated by
  `cols.is_real`). Absorbs the free `is_real * (is_real - 1) = 0` gate.
- `ITypeReader.Gated.Assertion.Spec` — flag-threaded I-type reader
  sub-circuit composition (binary gate + program + 2 register accesses
  + 4 op_a_0 masked gates), gated by `cols.is_real` /
  `cols.adapter_cols.is_trusted`.
- `adapter.op_a_0 = 0` — chip-level `op_a_0` zero gate.
- Semantic RV64 conjunct (conditional on `is_real = 1`): the result
  fits in 64 bits AND equals the BitVec `RV64.addi` of the sign-extended
  immediate and `op_b` operand. The byte-carry decomposition that the
  SP1 `AddOperation` circuit threads internally is *not* exposed here;
  it's the implementation detail of the `AddOp` sub-circuit and is
  reconstructed on demand via `SP1Clean.AddOp.iff_sp1_full` (see
  `Lemmas.lean`). The sign-extension identity is enforced inside the
  program-bus clause's `Opcode.trusted_instr` predicate; the monadic
  Sail equivalence to `_root_.Addi.spec_addi` is recovered externally
  via `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def FormalSpec (cols : AddiCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.ITypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 1, cols.state.pc,
       cols.op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    Word.toBitVec64 cols.op_a_write_value =
      RV64.addi (BitVec.ofNat 12 cols.adapter.op_c_imm[0].val)
                (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Addi

namespace SP1Clean.Addw

/-- The unified chip Spec for `AddwChip`: the ADDW carry-chain arithmetic
(`AddwOp.Spec`, Inputs-shape) plus the flag-threaded sub-circuit
composition (`CPUState.Gated` + `ALUTypeReader.Gated`) plus the
chip-level `op_a_0 = 0` gate plus the two pure BitVec semantic clauses
(`RV64.addw` when `imm_c = 0`, `RV64.addiw` when `imm_c = 1`). The free
`is_real * (is_real - 1) = 0` gate now lives inside both Gated.Specs'
first conjuncts. -/
def FormalSpec (cols : AddwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let op_a_write_value : Word (ZMod p) :=
    #v[cols.addw_value[0], cols.addw_value[1],
       cols.addw_msb * 65535, cols.addw_msb * 65535]
  SP1Clean.AddwOp.Spec
      ⟨cols.adapter.op_b_memory.prev_value,
       cols.adapter.op_c_memory.prev_value,
       cols.addw_value,
       cols.addw_msb⟩ ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 19, cols.state.pc,
       op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Pure BitVec semantic for ADDW (imm_c = 0). The ADDIW variant
  -- (imm_c = 1) is intentionally deferred: closing it requires the
  -- ALUTypeReader's `Gated.Assertion.Spec` to expose the trusted
  -- instruction's immediate sign-extension contract (currently bundled
  -- inside ProgramGated.Spec's opaque table lookup). Tracked under
  -- Phase 1.1 of the canonicalization plan — promote the reader to
  -- surface the sign-ext fact, then add a parallel RV64.addiw conjunct.
  (cols.is_real = 1 → cols.adapter.imm_c = 0 →
    Word.toBitVec64 op_a_write_value =
      RV64.addw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Addw

namespace SP1Clean.Sub

/-- The unified chip Spec for `SubChip`. Mirrors `SP1Clean.Add.FormalSpec`
swapping `AddOp` → `SubOp`, opcode `0` → `2`, `RV64.add` → `RV64.sub`.
Semantic-only contract: the byte-borrow decomposition that the SP1
`SubOperation` circuit threads internally is *not* exposed here; it's
the implementation detail of the `SubOp` sub-circuit and is
reconstructed on demand via `SubOperation.iff_sp1_full` (see
`Lemmas.lean`). The pure BitVec `RV64.sub` semantic is the trailing
conjunct (conditional on `is_real = 1`); the monadic Sail equivalence
to `_root_.Sub.spec_sub` is recovered externally via
`sail_correct_of_formalSpec` in `SailBridge.lean`. The standalone
`is_real * (is_real - 1) = 0` binary gate is absorbed into both
`CPUState.Gated.Assertion.Spec` and `RTypeReader.Gated.Assertion.Spec`'s
first conjuncts. -/
def FormalSpec (cols : SubCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 2, cols.state.pc,
       cols.op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    Word.toBitVec64 cols.op_a_write_value =
      RV64.sub (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
               (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Sub

namespace SP1Clean.Subw

/-- The unified chip Spec for `SubwChip`: the flag-threaded sub-circuit
composition (`CPUState.Gated` + `RTypeReader.Gated`, opcode 20), the
chip-level `op_a_0 = 0` gate, the 32-bit Sail-form internals triple
(`isU32 ∧ BV32 identity ∧ msb sign-extension bit`, matching
`SubwOperation.iff_sp1_full`'s RHS verbatim), and the trailing pure
BitVec `RV64.subw` semantic clause (gated on `is_real = 1`).

Diverges in shape from `SP1Clean/SubChip/Cols.lean`'s BV64-only form
because SubwChip's storage is BV32 + msb, not a 4-limb Word: the BV32
triple is kept as the internals exposure so completeness can drive
`SubwOperation.iff_sp1_full.mpr` to witness `subw_value` / `subw_msb`
without a costly BV64↔BV32+msb inversion. The `RV64.subw` 64-bit
clause is derived inline from the BV32 triple via the bridge
`rv64_subw_eq_of_subwop_spec` (see `Lemmas.lean`). -/
def FormalSpec (cols : SubwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let op_a_write_value : Word (ZMod p) :=
    #v[cols.subw_value[0], cols.subw_value[1],
       cols.subw_msb * 65535, cols.subw_msb * 65535]
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 20, cols.state.pc,
       op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    HWord.isU32 cols.subw_value ∧
    HWord.toBitVec32 cols.subw_value =
      execute_RTYPEW_pure_32_w cols.adapter.op_b_memory.prev_value
                                cols.adapter.op_c_memory.prev_value .SUBW ∧
    cols.subw_msb =
      if (HWord.toBitVec32 cols.subw_value).msb then 1 else 0) ∧
  -- Pure BitVec semantic for SUBW. Derived inline from the BV32 triple
  -- above via `rv64_subw_eq_of_subwop_spec`, using the operand
  -- `Word.isU64` bounds exposed by `RTypeReader.Gated.Assertion.Spec`'s
  -- `RegisterAccess.Spec` sub-conjuncts.
  (cols.is_real = 1 →
    Word.toBitVec64 op_a_write_value =
      RV64.subw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Subw

namespace SP1Clean.UType

/-- Chip-level Spec for `UTypeChip`. Mirrors what `Assertion.main`
emits, matching the monolith's TraceSpec shape (cpuStateSpec
+ raw AddOp `.allHold` + jtypeReaderSpec + scalar gates) and adding the
new pure BitVec conjunct so the chip's per-row RV64 semantics are visible
at a glance. The AddOp clause stays in raw `.allHold` form (with the
conditional gate `is_real - op_a_0`) because `AddOperation.allHold_constraints_iff`
is only stated at `is_real_arg = 1` — keeping the raw form here lets
`allHold_iff_structural` (Lemmas.lean) bridge to SP1's flat constraint list
without a case split on `op_a_0`.

Conjuncts:
- `cpuStateSpec` — the two clock-field byte-bound consequences.
- AddOp `.allHold` — raw 4-limb carry chain over `addend` + `op_b_imm` =
  `add_result`, gated by `is_real - op_a_0` (matches SP1's emission).
- `jtypeReaderSpec` — full J-type reader spec at `is_real = is_trusted = 1`
  (composes `trusted_instr`, register-index bounds, op_a_0 binary, op_a
  iff, pc bounds, timestamp, `Word.isU64` on prev_value, and the
  op_a_0-masked write-value gates).
- Six scalar trailing gates (`is_real`/`is_auipc` binary, three addend
  gates `addend[i] - is_auipc * pc[i] = 0`, and `(is_real - 1) * op_a_0 = 0`).
- Pure BitVec equation (conditional on `is_real = 1 ∧ op_a_0 = 0`):
  `add_result = if is_auipc = 1 then RV64.auipc imm pc else RV64.lui imm`.
  The sign-extension identity is enforced inside the program-bus clause's
  `Opcode.trusted_instr` predicate; the per-row Sail-monadic equivalence
  to `_root_.UType.spec_lui` / `spec_auipc` is recovered externally via
  `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def FormalSpec (cols : UTypeCols (ZMod p)) : Prop :=
  let opcode_e : ZMod p := cols.is_auipc * 48 + (1 - cols.is_auipc) * 49
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  (_root_.AddOperation.constraints (F := ZMod p)
      #v[cols.addend[0], cols.addend[1], cols.addend[2], 0]
      cols.adapter.op_b_imm
      { value := cols.add_result }
      (cols.is_real - cols.adapter.op_a_0)).allHold ∧
  SP1Clean.JTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
       cols.add_result, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.is_auipc * (cols.is_auipc - 1) = 0 ∧
  cols.addend[0] - cols.is_auipc * cols.state.pc[0] = 0 ∧
  cols.addend[1] - cols.is_auipc * cols.state.pc[1] = 0 ∧
  cols.addend[2] - cols.is_auipc * cols.state.pc[2] = 0 ∧
  (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 → cols.adapter.op_a_0 = 0 →
    Word.toBitVec64 cols.add_result =
      (let imm : BitVec 20 :=
        BitVec.ofNat 20 (cols.adapter.op_b_imm[0].val / 4096 +
                         cols.adapter.op_b_imm[1].val * 16)
       if cols.is_auipc = 1
       then RV64.auipc imm
                       (Word.toBitVec64
                          #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)])
       else RV64.lui imm))

end SP1Clean.UType

namespace SP1Clean.Bitwise

namespace Assertion

/-- The byte- and program-lookup-derivable subset of `Spec`. Includes
the two sub-assertion consequences plus the four trailing assert
clauses. Drops the BitwiseU16 carry chain + `aluTypeReaderSpec`
content, which is not derivable from `main`'s lookups alone. -/
def FormalSpec (cols : BitwiseCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_xor * (cols.is_xor - 1) = 0 ∧
  cols.is_or * (cols.is_or - 1) = 0 ∧
  cols.is_and * (cols.is_and - 1) = 0 ∧
  (cols.is_xor + cols.is_or + cols.is_and)
    * (cols.is_xor + cols.is_or + cols.is_and - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

end Assertion

end SP1Clean.Bitwise

namespace SP1Clean.Mul

namespace Assertion

/-- Semantic-only chip Spec for `MulChip`. Four conjuncts:
- `CPUState.Gated.Assertion.Spec` — sub-CPU assertion (absorbs the
  `is_real * (is_real - 1) = 0` gate as its first conjunct).
- `RTypeReader.Gated.Assertion.Spec` — sub-reader assertion (absorbs the
  4 op_a_0 mask gates and reader binarity).
- `cols.adapter.op_a_0 = 0` — chip-level op_a_0 scalar gate (Mul always
  writes its result).
- RV64 fact (selector-dispatched, gated on `is_real = 1`): the result
  word is U64 and equals the corresponding `RV64.{mul,mulh,mulhu,mulhsu,mulw}`
  of the operands. Mirrors AddChip's pattern fanned out for the five Mul
  variants.

Chip-internal items deliberately NOT in the Spec: the five
`is_mulX * (is_mulX - 1) = 0` selector binarities, the sum binarity, and
the indirect `MulOp.Spec` reference. They still appear inside
`Assertion.main` (re-emitted faithfully per SP1's `MulChip::eval`), but
their semantic content is already captured by the four conjuncts above
(selector binarities are needed for completeness witness construction
inside `MulOp.assertion`; the RV64 fact subsumes `MulOp.Spec`'s 5-way
implication structure). -/
def FormalSpec (cols : MulCols (ZMod p)) : Prop :=
  -- Summand order matches `SP1Clean.Soundness.IsRealBinary.is_real_binary_mul`'s
  -- goal expression so `tauto` keeps finding the binary conjunct downstream.
  let is_real : ZMod p :=
    cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu
  let opcode_e : ZMod p :=
    cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
      + cols.is_mulhsu * 14 + cols.is_mulhu * 24
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let bw : BitVec 64 := Word.toBitVec64 cols.adapter.op_b_memory.prev_value
  let cw : BitVec 64 := Word.toBitVec64 cols.adapter.op_c_memory.prev_value
  let aw : BitVec 64 := Word.toBitVec64 cols.op_a_write_value
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     cols.op_a_write_value, cols.adapter, is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  (is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    (cols.is_mul    = 1 → aw = RV64.mul    cw bw) ∧
    (cols.is_mulh   = 1 → aw = RV64.mulh   cw bw) ∧
    (cols.is_mulhu  = 1 → aw = RV64.mulhu  cw bw) ∧
    (cols.is_mulhsu = 1 → aw = RV64.mulhsu cw bw) ∧
    (cols.is_mulw   = 1 → aw = RV64.mulw   cw bw))

end Assertion

end SP1Clean.Mul

namespace SP1Clean.ShiftLeft

namespace Assertion

def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_sll * 8 + cols.is_sllw * 14,
      op_a := cols.adapter.op_a, op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_sll * (cols.is_sll - 1) = 0 ∧
  cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
  (cols.is_sll + cols.is_sllw) * (cols.is_sll + cols.is_sllw - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low,
     cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low,
     cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

end Assertion

end SP1Clean.ShiftLeft

namespace SP1Clean.ShiftRight

namespace Assertion

def FormalSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode_e : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_srl * (cols.is_srl - 1) = 0 ∧
  cols.is_sra * (cols.is_sra - 1) = 0 ∧
  cols.is_srlw * (cols.is_srlw - 1) = 0 ∧
  cols.is_sraw * (cols.is_sraw - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

end Assertion

end SP1Clean.ShiftRight

namespace SP1Clean.Lt

namespace Assertion

/-- The chip's Circuit-derivable spec: byte-lookup consequences for the
clock-decomposition gadget, the program-bus existential witness, and the
four scalar trailing assertZero gates. -/
def FormalSpec (cols : LtCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := cols.is_slt * 9 + cols.is_sltu * 10,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := cols.adapter.imm_c } ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (cols.is_slt + cols.is_sltu) * (cols.is_slt + cols.is_sltu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type-shaped: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

end Assertion

end SP1Clean.Lt

namespace SP1Clean.DivRem

namespace Assertion

/-- Faithful sub-circuit-composed `FormalSpec`: one conjunct per emission
in `main`. Sub-Specs are referenced by direct field application per
CLAUDE.md principle #2 — no `RawSpec` / `List.Forall SP1Constraint.toProp`
envelopes. -/
def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_div   : ZMod p := cols.aux_post.mode_flags[0]
  let is_divu  : ZMod p := cols.aux_post.mode_flags[1]
  let is_rem_f : ZMod p := cols.aux_post.mode_flags[2]
  let is_remu  : ZMod p := cols.aux_post.mode_flags[3]
  let is_divw  : ZMod p := cols.aux_post.mode_flags[4]
  let is_remw  : ZMod p := cols.aux_post.mode_flags[5]
  let is_divuw : ZMod p := cols.aux_post.mode_flags[6]
  let is_remuw : ZMod p := cols.aux_post.mode_flags[7]
  let e92      : ZMod p := is_div + is_rem_f
  let e93      : ZMod p := is_divu + is_remu
  let opcode_e : ZMod p :=
    is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
      + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28
  -- Reader Specs.
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     cols.op_a_write_value, cols.adapter, cols.is_real,
     cols.adapter_cols.is_trusted⟩ ∧
  -- Arithmetic sub-fragment Specs (CS0–CS16).
  SP1Clean.MulOp.Spec
    ⟨#v[cols.c_times_quotient[0], cols.c_times_quotient[1],
        cols.c_times_quotient[2], cols.c_times_quotient[3]],
     cols.quotient_comp, cols.c,
     cols.c_times_quotient_lower.carry, cols.c_times_quotient_lower.product,
     cols.c_times_quotient_lower.b_lower_byte.low_bytes,
     cols.c_times_quotient_lower.c_lower_byte.low_bytes,
     cols.c_times_quotient_lower.b_msb, cols.c_times_quotient_lower.c_msb,
     cols.c_times_quotient_lower.product_msb.msb,
     cols.c_times_quotient_lower.b_sign_extend,
     cols.c_times_quotient_lower.c_sign_extend,
     cols.is_real, 0, 0, 0, 0⟩ ∧
  SP1Clean.MulOp.Spec
    ⟨#v[cols.c_times_quotient[4], cols.c_times_quotient[5],
        cols.c_times_quotient[6], cols.c_times_quotient[7]],
     cols.quotient_comp, cols.c,
     cols.c_times_quotient_upper.carry, cols.c_times_quotient_upper.product,
     cols.c_times_quotient_upper.b_lower_byte.low_bytes,
     cols.c_times_quotient_upper.c_lower_byte.low_bytes,
     cols.c_times_quotient_upper.b_msb, cols.c_times_quotient_upper.c_msb,
     cols.c_times_quotient_upper.product_msb.msb,
     cols.c_times_quotient_upper.b_sign_extend,
     cols.c_times_quotient_upper.c_sign_extend,
     0, e92, e93, 0, 0⟩ ∧
  SP1Clean.IsEqualWordOp.Spec
    ⟨cols.adapter.op_b_memory.prev_value, #v[0, 0, 0, 32768],
     #v[cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].result],
     cols.aux_post.is_overflow_b.is_diff_zero.is_zero_first_half,
     cols.aux_post.is_overflow_b.is_diff_zero.is_zero_second_half,
     cols.aux_post.is_overflow_b.is_diff_zero.result⟩ ∧
  SP1Clean.IsEqualWordOp.Spec
    ⟨cols.adapter.op_c_memory.prev_value, #v[65535, 65535, 65535, 65535],
     #v[cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].result],
     cols.aux_post.is_overflow_c.is_diff_zero.is_zero_first_half,
     cols.aux_post.is_overflow_c.is_diff_zero.is_zero_second_half,
     cols.aux_post.is_overflow_c.is_diff_zero.result⟩ ∧
  SP1Clean.IsEqualWordOp.Spec
    ⟨#v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1], 0, 0],
     #v[0, 32768, 0, 0],
     #v[cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].inverse,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].result,
        cols.aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].result],
     cols.aux_post.is_overflow_b.is_diff_zero.is_zero_first_half,
     cols.aux_post.is_overflow_b.is_diff_zero.is_zero_second_half,
     cols.aux_post.is_overflow_b.is_diff_zero.result⟩ ∧
  SP1Clean.IsEqualWordOp.Spec
    ⟨#v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1], 0, 0],
     #v[65535, 65535, 0, 0],
     #v[cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].inverse,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].result,
        cols.aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].result],
     cols.aux_post.is_overflow_c.is_diff_zero.is_zero_first_half,
     cols.aux_post.is_overflow_c.is_diff_zero.is_zero_second_half,
     cols.aux_post.is_overflow_c.is_diff_zero.result⟩ ∧
  SP1Clean.IsZeroWordOp.Spec
    ⟨cols.c,
     #v[cols.aux_post.is_c_0.is_zero_limb[0].inverse,
        cols.aux_post.is_c_0.is_zero_limb[1].inverse,
        cols.aux_post.is_c_0.is_zero_limb[2].inverse,
        cols.aux_post.is_c_0.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_c_0.is_zero_limb[0].result,
        cols.aux_post.is_c_0.is_zero_limb[1].result,
        cols.aux_post.is_c_0.is_zero_limb[2].result,
        cols.aux_post.is_c_0.is_zero_limb[3].result],
     cols.aux_post.is_c_0.is_zero_first_half,
     cols.aux_post.is_c_0.is_zero_second_half,
     cols.aux_post.is_c_0.result⟩ ∧
  SP1Clean.AddOp.Assertion.Spec
    ⟨cols.c, cols.abs_c, cols.aux_post.c_neg_operation.value, cols.abs_c_alu_event⟩ ∧
  SP1Clean.AddOp.Assertion.Spec
    ⟨cols.remainder_comp, cols.abs_remainder,
     cols.aux_post.rem_neg_operation.value, cols.abs_rem_alu_event⟩ ∧
  SP1Clean.LtUnsignedOp.Spec
    ⟨cols.abs_remainder, cols.max_abs_c_or_1,
     cols.aux_post.remainder_lt_operation.u16_compare_operation.bit,
     cols.aux_post.remainder_lt_operation.u16_flags,
     cols.aux_post.remainder_lt_operation.not_eq_inv,
     cols.aux_post.remainder_lt_operation.comparison_limbs⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value[3], cols.aux_post.b_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.adapter.op_c_memory.prev_value[3], cols.aux_post.c_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.remainder[3], cols.aux_post.rem_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value[1], cols.aux_post.b_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.adapter.op_c_memory.prev_value[1], cols.aux_post.c_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.remainder[1], cols.aux_post.rem_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec
    ⟨cols.quotient[1], cols.aux_post.quot_msb.msb⟩ ∧
  -- Chip-level scalar gates.
  cols.c_neg             * (cols.c_neg             - 1) = 0 ∧
  cols.abs_c_alu_event   * (cols.abs_c_alu_event   - 1) = 0 ∧
  cols.abs_rem_alu_event * (cols.abs_rem_alu_event - 1) = 0 ∧
  cols.is_real           * (cols.is_real           - 1) = 0 ∧
  cols.remainder_check_multiplicity *
    (cols.remainder_check_multiplicity - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end Assertion

end SP1Clean.DivRem

/-! ## Control chips -/

namespace SP1Clean.Branch

namespace Assertion

def FormalSpec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.is_branching * (cols.is_branching - 1) = 0 ∧
  -- State-bus next_pc grounding: two gated carry chains targeting the
  -- same committed `next_pc` (padded to 4 limbs with high limb 0).
  -- Mirrors upstream's `when(is_branching) / when(is_real - is_branching)`
  -- conditional carry checks in `../sp1/.../control_flow/branch/air.rs`.
  (cols.is_branching = 0 ∨ SP1Clean.GatedAddOp.Spec
    (cols.state.pc.push 0) cols.adapter.op_c_imm (cols.next_pc.push 0)) ∧
  (1 - cols.is_branching = 0 ∨ SP1Clean.GatedAddOp.Spec
    (cols.state.pc.push 0) #v[4, 0, 0, 0] (cols.next_pc.push 0)) ∧
  -- Range bounds on `next_pc[i]` (replaces the lookups previously
  -- carried by `AddrAddOp.assertion`).
  (cols.next_pc[0]).val < 65536 ∧
  (cols.next_pc[1]).val < 65536 ∧
  (cols.next_pc[2]).val < 65536 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- Branch emits 2 register accesses: op_a/+4 and op_b/+3 (pure reads).
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

end SP1Clean.Branch

namespace SP1Clean.Jal

namespace Assertion

/-- Chip-level FormalSpec mirroring AddChip's canonical pattern
(commit `b82c79e`): the two AddOp sub-circuit conjuncts are now stated
semantically (`is_real = 1 → isU64 result ∧ result.toBitVec64 = a + b`),
matching `AddOp.Assertion.Spec`'s shape directly. The carry-chain
implementation detail is reconstructed on demand via `AddOp.iff_sp1_full`
when bridging back to SP1's `allHold` at the trace level. -/
def FormalSpec (cols : JalCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.next_pc ∧
    Word.toBitVec64 cols.next_pc =
      Word.toBitVec64 (cols.state.pc.push 0) +
      Word.toBitVec64 cols.adapter.op_b_imm) ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    Word.toBitVec64 cols.op_a_write_value =
      Word.toBitVec64 (cols.state.pc.push 0) +
      Word.toBitVec64 (#v[4, 0, 0, 0] : Vector (ZMod p) 4)) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 46, op_a := cols.adapter.op_a,
      op_b := cols.adapter.op_b_imm, op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 1, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequence.
  -- Jal emits a single op_a register access at offset +4.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩

end Assertion

end SP1Clean.Jal

namespace SP1Clean.Jalr

namespace Assertion

/-- Chip-level FormalSpec mirroring JalChip's canonical semantic-only pattern
(commit `186a456`): the jump-target `AddOperation` is now stated semantically
(`is_real = 1 → isU64 jump_target ∧ jump_target.toBitVec64 = b + c_imm`),
matching `AddOp.Assertion.Spec`'s shape directly. The carry-chain
implementation detail is reconstructed on demand via `AddOperation.iff_sp1_full`
when bridging back to SP1's `allHold` at the trace level. -/
def FormalSpec (cols : JalrCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 47, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  (cols.is_real = 1 →
    Word.isU64 cols.jump_target ∧
    Word.toBitVec64 cols.jump_target =
      Word.toBitVec64 cols.adapter.op_b_memory.prev_value +
      Word.toBitVec64 cols.adapter.op_c_imm) ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.lsb * (cols.lsb - 1) = 0 ∧
  (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- Jalr emits 2 register accesses: op_a/+4 and op_b/+3.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

end SP1Clean.Jalr

/-! ## Memory chips -/

namespace SP1Clean.LoadByte

namespace Assertion

def FormalSpec (cols : LoadByteCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_lb * 29 + cols.is_lbu * 32,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  (cols.is_lb + cols.is_lbu) * (cols.is_lb + cols.is_lbu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E (partial). Register-side memory-bus byte content:
  -- op_a/+4, op_b/+3. The load_mem/+1 access is deferred.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : LoadByteCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_lb + cols.is_lbu
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_lb * 29 + cols.is_lbu * 32
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.selected_byte + 65280 * cols.signed_extension_flag,
       65535 * cols.signed_extension_flag,
       65535 * cols.signed_extension_flag,
       65535 * cols.signed_extension_flag]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
     cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     cols.offset_bit_2, cols.offset_bit_1, cols.offset_bit_0⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value,
     cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩ ∧
  SP1Clean.LoadByteSelector.Assertion.Spec
    ⟨cols.load_prev_value, cols.offset_bit_2, cols.offset_bit_1, cols.offset_bit_0,
     cols.selected_limb, cols.selected_limb_low_byte, cols.selected_byte,
     cols.signed_extension_flag, cols.is_lbu⟩ ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  (cols.is_lb + cols.is_lbu) * (cols.is_lb + cols.is_lbu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end AssertionGated

end SP1Clean.LoadByte

namespace SP1Clean.LoadHalf

namespace Assertion

def FormalSpec (cols : LoadHalfCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_lh * 30 + cols.is_lhu * 33,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : LoadHalfCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_lh + cols.is_lhu
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_lh * 30 + cols.is_lhu * 33
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.op_a_write_value_lo,
       65535 * cols.signed_extension_msb,
       65535 * cols.signed_extension_msb,
       65535 * cols.signed_extension_msb]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     0, cols.offset_bit_1, cols.offset_bit_0⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value, cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩ ∧
  SP1Clean.LoadHalfSelector.Assertion.Spec
    ⟨cols.load_prev_value, 0, cols.offset_bit_1, cols.offset_bit_0,
     cols.op_a_write_value_lo, cols.signed_extension_msb, cols.is_lhu⟩ ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end AssertionGated

end SP1Clean.LoadHalf

namespace SP1Clean.LoadWord

namespace Assertion

def FormalSpec (cols : LoadWordCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_lw * 31 + cols.is_lwu * 34,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  (cols.is_lw + cols.is_lwu) * (cols.is_lw + cols.is_lwu - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : LoadWordCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_lw + cols.is_lwu
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_lw * 31 + cols.is_lwu * 34
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.op_a_write_value_lo[0], cols.op_a_write_value_lo[1],
       65535 * cols.signed_extension_msb,
       65535 * cols.signed_extension_msb]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, cols.offset_bit, 0, 0⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value, cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩ ∧
  SP1Clean.LoadWordSelector.Assertion.Spec
    ⟨cols.load_prev_value, cols.offset_bit, 0, 0,
     cols.op_a_write_value_lo[0], cols.op_a_write_value_lo[1],
     cols.signed_extension_msb, cols.is_lwu⟩ ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  (cols.is_lw + cols.is_lwu) * (cols.is_lw + cols.is_lwu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end AssertionGated

end SP1Clean.LoadWord

namespace SP1Clean.LoadDouble

namespace Assertion

def FormalSpec (cols : LoadDoubleCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 35, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : LoadDoubleCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_real * 35
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.load_prev_value[0], cols.load_prev_value[1],
       cols.load_prev_value[2], cols.load_prev_value[3]]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, 0, 0, 0⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value, cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, cols.is_real⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end AssertionGated

end SP1Clean.LoadDouble

namespace SP1Clean.LoadX0

namespace Assertion

def FormalSpec (cols : LoadX0Cols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode_e : ZMod p :=
    cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
      cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  cols.is_ld * (cols.is_ld - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : LoadX0Cols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p :=
    cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
      cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35
  let op_a_write_value : Vector (ZMod p) 4 := #v[0, 0, 0, 0]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     cols.offset_bit[0], cols.offset_bit[1], cols.offset_bit[2]⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value, cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩ ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  cols.is_ld * (cols.is_ld - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 1

end AssertionGated

end SP1Clean.LoadX0

namespace SP1Clean.StoreByte

namespace Assertion

def FormalSpec (cols : StoreByteCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 36, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : StoreByteCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_real * 36
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     cols.byte_selector_top, cols.byte_selector_mid, cols.byte_selector_lo⟩ ∧
  SP1Clean.ITypeReaderImmutable.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.adapter⟩ ∧
  SP1Clean.StoreMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.store_prev_value,
     cols.store_value,
     cols.store_memory_prev_high, cols.store_memory_prev_low,
     cols.store_memory_diff_low, cols.store_memory_diff_high,
     cols.store_memory_flag, cols.is_real⟩ ∧
  SP1Clean.StoreByteAssembler.Assertion.Spec
    ⟨cols.store_prev_value, cols.store_value,
     cols.register_low_byte, cols.mem_limb_low_byte,
     cols.byte_selector_top, cols.byte_selector_mid, cols.byte_selector_lo⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0

end AssertionGated

end SP1Clean.StoreByte

namespace SP1Clean.StoreHalf

namespace Assertion

def FormalSpec (cols : StoreHalfCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 37, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : StoreHalfCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_real * 37
  let store_halfword : ZMod p := cols.adapter.op_a_memory.prev_value[0]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     0, cols.offset_bit_1, cols.offset_bit_0⟩ ∧
  SP1Clean.ITypeReaderImmutable.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.adapter⟩ ∧
  SP1Clean.StoreMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value,
     cols.store_prev_value, cols.store_value,
     cols.store_memory_prev_high, cols.store_memory_prev_low,
     cols.store_memory_diff_low, cols.store_memory_diff_high,
     cols.store_memory_flag, cols.is_real⟩ ∧
  SP1Clean.StoreHalfAssembler.Assertion.Spec
    ⟨cols.store_prev_value, cols.store_value, store_halfword,
     0, cols.offset_bit_1, cols.offset_bit_0⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0

end AssertionGated

end SP1Clean.StoreHalf

namespace SP1Clean.StoreWord

namespace Assertion

def FormalSpec (cols : StoreWordCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 38, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : StoreWordCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_real * 38
  let store_low : ZMod p := cols.adapter.op_a_memory.prev_value[0]
  let store_high : ZMod p := cols.adapter.op_a_memory.prev_value[1]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, cols.offset_bit, 0, 0⟩ ∧
  SP1Clean.ITypeReaderImmutable.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.adapter⟩ ∧
  SP1Clean.StoreMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value,
     cols.store_prev_value, cols.store_value,
     cols.store_memory_prev_high, cols.store_memory_prev_low,
     cols.store_memory_diff_low, cols.store_memory_diff_high,
     cols.store_memory_flag, cols.is_real⟩ ∧
  SP1Clean.StoreWordAssembler.Assertion.Spec
    ⟨cols.store_prev_value, cols.store_value, store_low, store_high,
     cols.offset_bit, 0, 0⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0

end AssertionGated

end SP1Clean.StoreWord

namespace SP1Clean.StoreDouble

namespace Assertion

def FormalSpec (cols : StoreDoubleCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 39, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

end Assertion

namespace AssertionGated

def FormalSpec (cols : StoreDoubleCols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_real * 39
  let store_value : Vector (ZMod p) 4 :=
    #v[cols.adapter.op_a_memory.prev_value[0], cols.adapter.op_a_memory.prev_value[1],
       cols.adapter.op_a_memory.prev_value[2], cols.adapter.op_a_memory.prev_value[3]]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, 0, 0, 0⟩ ∧
  SP1Clean.ITypeReaderImmutable.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.adapter⟩ ∧
  SP1Clean.StoreMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value,
     cols.store_prev_value, store_value,
     cols.store_memory_prev_high, cols.store_memory_prev_low,
     cols.store_memory_diff_low, cols.store_memory_diff_high,
     cols.store_memory_flag, cols.is_real⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0

end AssertionGated

end SP1Clean.StoreDouble

/-! ## Boundary memory chip -/

namespace SP1Clean.MemoryGlobal

namespace Assertion

/-- Phase 1 scaffold FormalSpec mirroring the partial `main` composition in
`SP1Clean/Chips/Memory/MemoryGlobalChip.lean`. The `LtUnsignedOp` /
monotonicity / x0-case conjuncts are deferred to Phase 4.5 pending the
`MemoryGlobalCols.lt_cols` struct expansion documented in the chip file. -/
def FormalSpec (cols : MemoryGlobalCols (ZMod p)) : Prop :=
  cols.is_real * (cols.is_real - 1) = 0 ∧
  (cols.value[0]).val < 65536 ∧
  (cols.value[1]).val < 65536 ∧
  (cols.value[2]).val < 65536 ∧
  (cols.value[3]).val < 65536 ∧
  (cols.prev_addr[0]).val < 65536 ∧
  (cols.prev_addr[1]).val < 65536 ∧
  (cols.prev_addr[2]).val < 65536 ∧
  (cols.addr[0]).val < 65536 ∧
  (cols.addr[1]).val < 65536 ∧
  (cols.addr[2]).val < 65536 ∧
  cols.value[2] - (cols.value_lower + 256 * cols.value_upper) = 0 ∧
  (cols.value_lower).val < 256 ∧
  (cols.value_upper).val < 256 ∧
  SP1Clean.IsZeroOp.Assertion.Spec
    ⟨cols.prev_addr[0] + cols.prev_addr[1] + cols.prev_addr[2],
     cols.is_prev_addr_zero[0], cols.is_prev_addr_zero[1]⟩ ∧
  SP1Clean.IsZeroOp.Assertion.Spec
    ⟨cols.index, cols.is_index_zero[0], cols.is_index_zero[1]⟩ ∧
  cols.is_comp - cols.is_real *
    (1 - cols.is_prev_addr_zero[1] * cols.is_index_zero[1]) = 0 ∧
  cols.is_comp * (cols.is_comp - 1) = 0

end Assertion

end SP1Clean.MemoryGlobal
