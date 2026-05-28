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
import SP1Clean.Operations.BitwiseU16Operation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Operations.LtOperationSigned
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

/-- The unified chip Spec for `AddwChip`: the canonical (a) shape from
the SPEC_AUDIT.md classification — flag-threaded sub-circuit composition
(`CPUState.Gated` + `ALUTypeReader.Gated`, opcode 19), the chip-level
`op_a_0 = 0` gate, the gated `AddwOp.AssertionGated.Spec` sub-Spec
(semantic 32-bit triple matching `AddwOperation.iff_sp1_full`'s RHS
verbatim under `is_real = 1`), and a pure BitVec `RV64.addw` semantic
consequence conditional on `is_real = 1`. The byte-decomposition +
sign-extension MSB witness threaded internally by `AddwOperation` is
*not* exposed here; it's the implementation detail of the `AddwOp`
sub-circuit and is reconstructed on demand via
`AddwOperation.iff_sp1_full` (see `Lemmas.lean`).

The 4-limb result Word `#v[addw_value[0], addw_value[1], msb*65535,
msb*65535]` is reconstructed inline from the chip-internal `addw_value`
(2 BV16 limbs) and `addw_msb` (sign-extension witness) — these are the
canonical Rust-side storage form. The Spec's BV64 semantic conjunct
sees only the result `Word`, not the individual columns; the `RV64.addw`
clause is uniform for both ADDW (R-type, `imm_c = 0`) and ADDIW (I-type,
`imm_c = 1`) because the reader supplies `op_c_memory.prev_value`
matching the immediate or register operand as appropriate (so the BV64
equation is the same regardless of `imm_c`). The per-row Sail-monadic
equivalence to `_root_.Addw.spec_addw` / `_root_.Addiw.spec_addiw` is
recovered externally via `sail_correct_addw_of_formalSpec` /
`sail_correct_addiw_of_formalSpec` (`SailBridge.lean`). The free
`is_real * (is_real - 1) = 0` gate lives inside both Gated.Specs'
first conjuncts. -/
def FormalSpec (cols : AddwCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let op_a_write_value : Word (ZMod p) :=
    #v[cols.addw_value[0], cols.addw_value[1],
       cols.addw_msb * 65535, cols.addw_msb * 65535]
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, 19, cols.state.pc,
       op_a_write_value, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.adapter.op_a_0 = 0 ∧
  SP1Clean.AddwOp.AssertionGated.Spec
      ⟨cols.adapter.op_b_memory.prev_value,
       cols.adapter.op_c_memory.prev_value,
       cols.addw_value, cols.addw_msb, cols.is_real⟩ ∧
  -- Pure BitVec semantic for ADDW/ADDIW. Derived inline from the BV32
  -- triple inside `AddwOp.AssertionGated.Spec` via the
  -- `addwOp_spec_iff_rv64_addw` bridge, using the operand `Word.isU64`
  -- bounds exposed by `ALUTypeReader.Gated.Assertion.isU64_op_b_of_spec`
  -- / `isU64_op_c_memory_of_spec`.
  (cols.is_real = 1 →
    Word.isU64 op_a_write_value ∧
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
chip-level `op_a_0 = 0` gate, the gated SubwOp sub-Spec
(`SubwOp.AssertionGated.Spec`, the semantic 32-bit triple matching
`SubwOperation.iff_sp1_full`'s RHS verbatim under `is_real = 1`), and
the trailing pure BitVec `RV64.subw` semantic consequence (gated on
`is_real = 1`).

Diverges in shape from `SP1Clean/SubChip/Cols.lean`'s BV64-only form
because SubwChip's storage is BV32 + msb, not a 4-limb Word: the BV32
triple lives inside `SubwOp.AssertionGated.Spec` so completeness can
drive `SubwOperation.iff_sp1_full.mpr` to witness `subw_value` /
`subw_msb` without a costly BV64↔BV32+msb inversion. The `RV64.subw`
64-bit clause is derived inline from that BV32 triple via the bridge
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
  SP1Clean.SubwOp.AssertionGated.Spec
      ⟨cols.adapter.op_b_memory.prev_value,
       cols.adapter.op_c_memory.prev_value,
       cols.subw_value, cols.subw_msb, cols.is_real⟩ ∧
  -- Pure BitVec semantic for SUBW. Derived inline from the BV32 triple
  -- inside `SubwOp.AssertionGated.Spec` via `rv64_subw_eq_of_subwop_spec`,
  -- using the operand `Word.isU64` bounds exposed by
  -- `RTypeReader.Gated.Assertion.Spec`'s `RegisterAccess.Spec` sub-conjuncts.
  (cols.is_real = 1 →
    Word.toBitVec64 op_a_write_value =
      RV64.subw (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                (Word.toBitVec64 cols.adapter.op_b_memory.prev_value))

end SP1Clean.Subw

namespace SP1Clean.UType

/-- Chip-level Spec for `UTypeChip` — canonical (a) shape per SPEC_AUDIT.md.
The raw `AddOperation.constraints.allHold` envelope is replaced by
`AddOp.Assertion.Spec` as a subcircuit composition (gated on
`is_real - op_a_0`), and the `cpuStateSpec` is promoted to
`CPUState.Gated.Assertion.Spec`. The byte-carry decomposition that SP1's
`AddOperation` threads internally is *not* exposed here; it's the
implementation detail of the `AddOp` sub-circuit and is reconstructed on
demand via `SP1Clean.AddOp.iff_sp1_full` (see `Lemmas.lean`).

Conjuncts:
- `CPUState.Gated.Assertion.Spec` — flag-threaded CPUState sub-circuit
  composition (binary gate + 2 state-bus + 2 byte-opcode, all gated by
  `cols.is_real`). Absorbs the free `is_real * (is_real - 1) = 0` gate.
- `AddOp.Assertion.Spec` — gated by `is_real - op_a_0` (= 1 when
  `(is_real, op_a_0) = (1, 0)`, the only case where AUIPC/LUI's PC-relative
  addition fires). The conditional Spec form: `gate = 1 → isU64 result ∧
  result.toBitVec64 = addend.toBitVec64 + op_b_imm.toBitVec64`.
- `JTypeReader.Gated.Assertion.Spec` — full J-type reader spec at
  `is_real = is_trusted = 1` (composes `trusted_instr`, register-index
  bounds, op_a_0 binary, op_a iff, pc bounds, timestamp, `Word.isU64`
  on prev_value, and the op_a_0-masked write-value gates).
- Five scalar trailing gates (`is_auipc` binary, three addend gates
  `addend[i] - is_auipc * pc[i] = 0`, and the chip-level conditional
  `(is_real - 1) * op_a_0 = 0` ensuring `op_a_0 ≤ is_real`).
- Pure BitVec equation (conditional on `is_real = 1 ∧ op_a_0 = 0`):
  `add_result = if is_auipc = 1 then RV64.auipc imm pc else RV64.lui imm`.
  The sign-extension identity is enforced inside the program-bus clause's
  `Opcode.trusted_instr` predicate; the per-row Sail-monadic equivalence
  to `_root_.UType.spec_lui` / `spec_auipc` is recovered externally via
  `sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def FormalSpec (cols : UTypeCols (ZMod p)) : Prop :=
  let opcode_e : ZMod p := cols.is_auipc * 48 + (1 - cols.is_auipc) * 49
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨cols.state,
       #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
       8, cols.is_real⟩ ∧
  SP1Clean.AddOp.Assertion.Spec
      ⟨#v[cols.addend[0], cols.addend[1], cols.addend[2], 0],
       cols.adapter.op_b_imm,
       cols.add_result,
       cols.is_real - cols.adapter.op_a_0⟩ ∧
  SP1Clean.JTypeReader.Gated.Assertion.Spec
      ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
       cols.add_result, cols.adapter,
       cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_auipc = 0 ∨ cols.is_auipc = 1) ∧
  cols.addend[0] = cols.is_auipc * cols.state.pc[0] ∧
  cols.addend[1] = cols.is_auipc * cols.state.pc[1] ∧
  cols.addend[2] = cols.is_auipc * cols.state.pc[2] ∧
  (cols.is_real = 1 ∨ cols.adapter.op_a_0 = 0) ∧
  (cols.is_real = 1 → cols.adapter.op_a_0 = 0 →
    Word.isU64 cols.add_result ∧
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

/-- The unified chip Spec for `BitwiseChip`. Faithful-composition shape:
one conjunct per sub-circuit invoked by `Assertion.main` —
`BitwiseU16Op.Assertion.Spec` (the 8 byte-table lookups on the algebraic
byte-decomposition of `op_b`/`op_c`, gated by `is_real`) + `CPUState.Gated`
+ `ALUTypeReader.Gated` — followed by the three selector + sum binarities
and the chip-level `op_a_0 = 0` gate.

Mirrors `SP1Clean.Lt.Assertion.FormalSpec`: the `BitwiseU16Operation`
byte-decomposition is exposed structurally via `BitwiseU16Op.Assertion.Spec`
rather than collapsed to a pure-semantic `RV64.{xor,or,and}` conjunct.
This is mandatory for completeness — the semantic word alone does not pin
the free byte-decomposition witnesses (`b_low_bytes`, `c_low_bytes`), so a
pure-semantic spec would be strictly weaker than the constraints. The RV64
semantic is recovered on demand from this structural spec via the Sail
bridge (`Bitwise.correct_*` at the Main level).

`op_a_write_value` is synthesized from the `bitwise_operation.result :
Vector T 8` byte pairs (`E44 + E45*256, …`) and fed to the ALUTypeReader. -/
def FormalSpec (cols : BitwiseCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_xor + cols.is_or + cols.is_and
  let opcode_e : ZMod p := cols.is_xor * 3 + cols.is_or * 4 + cols.is_and * 5
  let opcode_bw : ZMod p := cols.is_xor * 2 + cols.is_or * 1 + cols.is_and * 0
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let bres := cols.bitwise_operation.bitwise_operation.result
  let op_a_write_value : Word (ZMod p) :=
    #v[bres[0] + bres[1] * 256,
       bres[2] + bres[3] * 256,
       bres[4] + bres[5] * 256,
       bres[6] + bres[7] * 256]
  SP1Clean.BitwiseU16Op.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
     cols.bitwise_operation.b_low_bytes.low_bytes,
     cols.bitwise_operation.c_low_bytes.low_bytes,
     cols.bitwise_operation.bitwise_operation.result,
     opcode_bw, is_real⟩ ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     op_a_write_value, cols.adapter, is_real, cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_xor = 0 ∨ cols.is_xor = 1) ∧
  (cols.is_or = 0 ∨ cols.is_or = 1) ∧
  (cols.is_and = 0 ∨ cols.is_and = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
  cols.adapter.op_a_0 = 0

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

/-- The unified chip Spec for `ShiftLeftChip`. Faithful-composition shape
(mirrors `_root_.ShiftLeft.allHold_constraints_iff` conjunct-by-conjunct):
`U16MSBOp.AssertionGated` (the SLLW sign witness on `result[1]`) +
`CPUState.Gated` + `ALUTypeReader.Gated` (opcode `is_sll·6 + is_sllw·21`),
followed by the ~50 inline shift gates SP1 emits — the `c_bits` 6-bit
decomposition + within-shift bound, the `shift_u16` 4-way byte-selector
one-hot, the `v_01/v_012/v_0123` shift-power chain, the per-limb shift
decompositions + bounds, the `limb_result` wiring, and the 20 gated output
equations (16 SLL + 4 SLLW). The shift has no upstream sub-operation, so
these are exposed inline rather than collapsed to a pure-semantic
`RV64.sll`/`RV64.sllw` (mandatory for completeness; see
`docs/CLEAN_FUTURE.md`). The RV64 semantic is recovered on demand from
this structural spec via `Lemmas.sll_sllw_of_formalSpec`, which the Sail
bridge consumes. -/
def FormalSpec (cols : ShiftLeftCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_sll + cols.is_sllw
  let opcode_e : ZMod p := cols.is_sll * 6 + cols.is_sllw * 21
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let c6 : ZMod p := cols.c_bits[0] + cols.c_bits[1] * 2 + cols.c_bits[2] * 4
    + cols.c_bits[3] * 8 + cols.c_bits[4] * 16 + cols.c_bits[5] * 32
  let c4 : ZMod p := cols.c_bits[0] + cols.c_bits[1] * 2 + cols.c_bits[2] * 4
    + cols.c_bits[3] * 8
  let sel : ZMod p := cols.c_bits[4] + cols.c_bits[5] * 2 * cols.is_sll
  -- Faithful reformulation of the embedded `U16MSBOperation.constraints
  -- result[1] {sllw_msb} is_sllw` block (the SLLW sign witness). NOTE: this is
  -- *not* `U16MSBOp.AssertionGated.Spec` — that gated form only pins `msb`
  -- binary when the gate = 1, whereas SP1 asserts `msb*(msb-1)=0`
  -- unconditionally, so it would be strictly weaker (the
  -- `allHold_iff_structural` iff would fail backward on `is_sllw = 0` rows).
  (cols.is_sllw * (cols.is_sllw - 1) = 0 ∧
    cols.sllw_msb.msb * (cols.sllw_msb.msb - 1) = 0 ∧
    (cols.is_sllw ≠ 0 →
      (2 * cols.result[1] - cols.sllw_msb.msb * 65536 : ZMod p).val < 65536)) ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     cols.result, cols.adapter, is_real, cols.adapter_cols.is_trusted⟩ ∧
  (is_real = 0 ∨ is_real = 1) ∧
  (cols.is_sll = 0 ∨ cols.is_sll = 1) ∧
  (cols.is_sllw = 0 ∨ cols.is_sllw = 1) ∧
  (cols.c_bits[0] = 0 ∨ cols.c_bits[0] = 1) ∧
  (cols.c_bits[1] = 0 ∨ cols.c_bits[1] = 1) ∧
  (cols.c_bits[2] = 0 ∨ cols.c_bits[2] = 1) ∧
  (cols.c_bits[3] = 0 ∨ cols.c_bits[3] = 1) ∧
  (cols.c_bits[4] = 0 ∨ cols.c_bits[4] = 1) ∧
  (cols.c_bits[5] = 0 ∨ cols.c_bits[5] = 1) ∧
  (¬is_real = 0 →
    ((cols.adapter.op_c_memory.prev_value[0] - c6) * ((64 : ZMod p)⁻¹)).val
      < 2 ^ (10 : ZMod p).val) ∧
  (cols.shift_u16[0] = 0 ∨ sel = 0) ∧
  (cols.shift_u16[0] = 0 ∨ cols.shift_u16[0] = 1) ∧
  (cols.shift_u16[1] = 0 ∨ sel = 1) ∧
  (cols.shift_u16[1] = 0 ∨ cols.shift_u16[1] = 1) ∧
  (cols.shift_u16[2] = 0 ∨ sel = 2) ∧
  (cols.shift_u16[2] = 0 ∨ cols.shift_u16[2] = 1) ∧
  (cols.shift_u16[3] = 0 ∨ sel = 3) ∧
  (cols.shift_u16[3] = 0 ∨ cols.shift_u16[3] = 1) ∧
  (is_real = 0 ∨
    cols.shift_u16[0] + cols.shift_u16[1] + cols.shift_u16[2] + cols.shift_u16[3] = 1) ∧
  (cols.v_01 = (cols.c_bits[0] + 1) * (cols.c_bits[1] * 3 + 1)) ∧
  (cols.v_012 = cols.v_01 * (cols.c_bits[2] * 15 + 1)) ∧
  (cols.v_0123 = cols.v_012 * (cols.c_bits[3] * 255 + 1)) ∧
  (¬is_real = 0 → cols.lower_limb[0].val < 2 ^ ((16 : ZMod p) - c4).val) ∧
  (¬is_real = 0 → cols.higher_limb[0].val < 2 ^ c4.val) ∧
  (cols.adapter.op_b_memory.prev_value[0] * cols.v_0123
    = cols.higher_limb[0] * 65536 + cols.lower_limb[0] * cols.v_0123) ∧
  (¬is_real = 0 → cols.lower_limb[1].val < 2 ^ ((16 : ZMod p) - c4).val) ∧
  (¬is_real = 0 → cols.higher_limb[1].val < 2 ^ c4.val) ∧
  (cols.adapter.op_b_memory.prev_value[1] * cols.v_0123
    = cols.higher_limb[1] * 65536 + cols.lower_limb[1] * cols.v_0123) ∧
  (¬is_real = 0 → cols.lower_limb[2].val < 2 ^ ((16 : ZMod p) - c4).val) ∧
  (¬is_real = 0 → cols.higher_limb[2].val < 2 ^ c4.val) ∧
  (cols.adapter.op_b_memory.prev_value[2] * cols.v_0123
    = cols.higher_limb[2] * 65536 + cols.lower_limb[2] * cols.v_0123) ∧
  (¬is_real = 0 → cols.lower_limb[3].val < 2 ^ ((16 : ZMod p) - c4).val) ∧
  (¬is_real = 0 → cols.higher_limb[3].val < 2 ^ c4.val) ∧
  (cols.adapter.op_b_memory.prev_value[3] * cols.v_0123
    = cols.higher_limb[3] * 65536 + cols.lower_limb[3] * cols.v_0123) ∧
  (cols.limb_result[0] = cols.lower_limb[0] * cols.v_0123) ∧
  (cols.limb_result[1] = cols.lower_limb[1] * cols.v_0123 + cols.higher_limb[0]) ∧
  (cols.limb_result[2] = cols.lower_limb[2] * cols.v_0123 + cols.higher_limb[1]) ∧
  (cols.limb_result[3] = cols.lower_limb[3] * cols.v_0123 + cols.higher_limb[2]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[0] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[1] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[2] = cols.limb_result[2]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[3] = cols.limb_result[3]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[1] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[2] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[3] = cols.limb_result[2]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[1] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[2] = cols.limb_result[0]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[2] = 0 ∨ cols.result[3] = cols.limb_result[1]) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[1] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[2] = 0) ∧
  (cols.is_sll = 0 ∨ cols.shift_u16[3] = 0 ∨ cols.result[3] = cols.limb_result[0]) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[0] = cols.limb_result[0]) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[0] = 0 ∨ cols.result[1] = cols.limb_result[1]) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[0] = 0) ∧
  (cols.is_sllw = 0 ∨ cols.shift_u16[1] = 0 ∨ cols.result[1] = cols.limb_result[0]) ∧
  (cols.is_sllw = 0 ∨ cols.sllw_msb.msb * 65535 = cols.result[2]) ∧
  (cols.is_sllw = 0 ∨ cols.sllw_msb.msb * 65535 = cols.result[3]) ∧
  cols.is_sllw_imm = cols.is_sllw * cols.adapter.imm_c ∧
  cols.adapter.op_a_0 = 0

end Assertion

end SP1Clean.ShiftLeft

namespace SP1Clean.ShiftRight

namespace Assertion

/-- The unified chip Spec for `ShiftRightChip`. Canonical (a) shape:
`CPUState.Gated` + `ALUTypeReader.Gated` sub-circuit composition with
opcode `is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23`, the
chip-level `op_a_0 = 0` gate, four selector + sum binarities, and a
4-way selector-dispatched RV64 semantic conjunct
(`RV64.srl`/`RV64.sra`/`RV64.srlw`/`RV64.sraw`) gated on `is_real = 1`.
The 50+ inline shift-correctness gates plus the three embedded
`U16MSBOperation` MSB witnesses (for SRA/SRAW sign-extension and op_b
high-bit witness) are *not* exposed here; they're implementation
details of the shift sub-circuit and are reconstructed on demand via
the chip's eventual `iff_sp1` proof. -/
def FormalSpec (cols : ShiftRightCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  let opcode_e : ZMod p :=
    cols.is_srl * 7 + cols.is_sra * 8 + cols.is_srlw * 22 + cols.is_sraw * 23
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let bw := Word.toBitVec64 cols.adapter.op_b_memory.prev_value
  let cw := Word.toBitVec64 cols.adapter.op_c_memory.prev_value
  let aw := Word.toBitVec64 cols.op_a_write_value
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     cols.op_a_write_value, cols.adapter, is_real, cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_srl = 0 ∨ cols.is_srl = 1) ∧
  (cols.is_sra = 0 ∨ cols.is_sra = 1) ∧
  (cols.is_srlw = 0 ∨ cols.is_srlw = 1) ∧
  (cols.is_sraw = 0 ∨ cols.is_sraw = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
  cols.adapter.op_a_0 = 0 ∧
  (is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    (cols.is_srl  = 1 → aw = RV64.srl  cw bw) ∧
    (cols.is_sra  = 1 → aw = RV64.sra  cw bw) ∧
    (cols.is_srlw = 1 → aw = RV64.srlw cw bw) ∧
    (cols.is_sraw = 1 → aw = RV64.sraw cw bw))

end Assertion

end SP1Clean.ShiftRight

namespace SP1Clean.Lt

namespace Assertion

/-- The unified chip Spec for `LtChip`. Faithful-composition shape: one
conjunct per sub-circuit invoked by `Assertion.main` —
`LtSignedOp.AssertionGated.Spec` (the byte-decomposition comparison) +
`CPUState.Gated` + `ALUTypeReader.Gated` — followed by the selector + sum
binarities and the chip-level `op_a_0 = 0` gate.

Unlike the Add-family canonical (a) shape, the `LtOperationSigned`
byte-decomposition (`u16_flags` one-hot, `comparison_limbs`,
`not_eq_inv`) is exposed structurally here via `LtSignedOp.AssertionGated.Spec`
rather than collapsed to a pure-semantic `RV64.slt`/`RV64.sltu` conjunct.
This is mandatory for completeness: the semantic bit alone does not pin
those free combinatorial witnesses, so a pure-semantic spec would be
strictly weaker than the constraints (see `docs/CLEAN_FUTURE.md`). The
RV64 semantic (`aw = RV64.slt cw bw` etc.) is recovered on demand from
this structural spec via `Lemmas.slt_sltu_of_formalSpec`, which the Sail
bridge consumes. -/
def FormalSpec (cols : LtCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_slt + cols.is_sltu
  let opcode_e : ZMod p := cols.is_slt * 9 + cols.is_sltu * 10
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
  SP1Clean.LtSignedOp.AssertionGated.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
     cols.is_slt,
     cols.lt_operation.result.u16_compare_operation.bit,
     cols.lt_operation.result.u16_flags,
     cols.lt_operation.result.not_eq_inv,
     cols.lt_operation.result.comparison_limbs,
     cols.lt_operation.b_msb.msb,
     cols.lt_operation.c_msb.msb,
     is_real⟩ ∧
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, is_real⟩ ∧
  SP1Clean.ALUTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     op_a_write_value, cols.adapter, is_real, cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_slt = 0 ∨ cols.is_slt = 1) ∧
  (cols.is_sltu = 0 ∨ cols.is_sltu = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
  cols.adapter.op_a_0 = 0

end Assertion

end SP1Clean.Lt

namespace SP1Clean.DivRem

namespace Assertion

/-- The unified chip Spec for `DivRemChip`. Canonical (a) shape:
`CPUState.Gated` + `RTypeReader.Gated` sub-circuit composition with
opcode dispatched from the 8 `aux_post.mode_flags`, the chip-level
`is_real` binarity + `op_a_0 = 0` gates, and an 8-way
selector-dispatched RV64 semantic conjunct
(`RV64.{div,divu,rem,remu,divw,remw,divuw,remuw}`) gated on
`is_real = 1`.

All 11 mid-level sub-op specs that the prior shape exposed
(`MulOp.Spec` × 2, `IsEqualWordOp.Spec` × 4, `IsZeroWordOp.Spec`,
`AddOp.Assertion.Spec` × 2, `LtUnsignedOp.Spec`,
`U16MSBOp.Assertion.Spec` × 7) and the 117 inline aux-gates are *not*
exposed here; they're implementation details of the div/rem
sub-circuit (quotient verification, overflow detection, sign-flip
boundary cases, byte-MSB witnesses) and are reconstructed on demand
via the chip's eventual `iff_sp1` proof. The mode-flag binarities and
8-way one-hot constraint live inside `RTypeReader.Gated.Spec`
(opcode-dispatched) and the chip's `aux_post` invariants. -/
def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  let is_div   : ZMod p := cols.aux_post.mode_flags[0]
  let is_divu  : ZMod p := cols.aux_post.mode_flags[1]
  let is_rem_f : ZMod p := cols.aux_post.mode_flags[2]
  let is_remu  : ZMod p := cols.aux_post.mode_flags[3]
  let is_divw  : ZMod p := cols.aux_post.mode_flags[4]
  let is_remw  : ZMod p := cols.aux_post.mode_flags[5]
  let is_divuw : ZMod p := cols.aux_post.mode_flags[6]
  let is_remuw : ZMod p := cols.aux_post.mode_flags[7]
  let opcode_e : ZMod p :=
    is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
      + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let bw := Word.toBitVec64 cols.adapter.op_b_memory.prev_value
  let cw := Word.toBitVec64 cols.adapter.op_c_memory.prev_value
  let aw := Word.toBitVec64 cols.op_a_write_value
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state, #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
     8, cols.is_real⟩ ∧
  SP1Clean.RTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc,
     cols.op_a_write_value, cols.adapter, cols.is_real,
     cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  cols.adapter.op_a_0 = 0 ∧
  (cols.is_real = 1 →
    Word.isU64 cols.op_a_write_value ∧
    (is_div   = 1 → aw = RV64.div   cw bw) ∧
    (is_divu  = 1 → aw = RV64.divu  cw bw) ∧
    (is_rem_f = 1 → aw = RV64.rem   cw bw) ∧
    (is_remu  = 1 → aw = RV64.remu  cw bw) ∧
    (is_divw  = 1 → aw = RV64.divw  cw bw) ∧
    (is_remw  = 1 → aw = RV64.remw  cw bw) ∧
    (is_divuw = 1 → aw = RV64.divuw cw bw) ∧
    (is_remuw = 1 → aw = RV64.remuw cw bw))

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
  (cols.is_beq = 0 ∨ cols.is_beq = 1) ∧
  (cols.is_bne = 0 ∨ cols.is_bne = 1) ∧
  (cols.is_blt = 0 ∨ cols.is_blt = 1) ∧
  (cols.is_bge = 0 ∨ cols.is_bge = 1) ∧
  (cols.is_bltu = 0 ∨ cols.is_bltu = 1) ∧
  (cols.is_bgeu = 0 ∨ cols.is_bgeu = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
  (cols.is_branching = 0 ∨ cols.is_branching = 1) ∧
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

/-- The unified chip Spec for `JalChip`. Canonical (a) shape mirroring
`SP1Clean.UType.FormalSpec`: flag-threaded `CPUState.Gated` +
`JTypeReader.Gated` sub-circuit composition (opcode 46 = JAL), two
`AddOp.Assertion.Spec` semantic conjuncts (jump-target `pc + op_b_imm =
next_pc` gated by `is_real`, return-address `pc + 4 = op_a_write_value`
gated by `is_real - op_a_0`), and four trailing scalar gates
(`next_pc[3] = 0`, `op_a_write_value[3] = 0`, `(is_real - 1) * op_a_0 =
0` rephrased as `is_real = 1 ∨ op_a_0 = 0`, plus the jump-target
4-alignment consequence `(next_pc[0] / 4).val < 16384` derived from the
chip's PC-alignment byte send — control-flow specific and not subsumed
by CPUState/JTypeReader). The byte-carry decomposition that SP1's two
`AddOperation` invocations thread internally is *not* exposed here; it's
the implementation detail of the `AddOp` sub-circuit and is reconstructed
on demand via `AddOperation.iff_sp1_full` when bridging back to SP1's
`allHold` at the trace level. The per-row Sail-monadic equivalence to
`_root_.Jal.spec_jal` is recovered externally via
`sail_correct_of_formalSpec` (`SailBridge.lean`). -/
def FormalSpec (cols : JalCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.Gated.Assertion.Spec
    ⟨cols.state,
     #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]],
     8, cols.is_real⟩ ∧
  SP1Clean.AddOp.Assertion.Spec
    ⟨cols.state.pc.push 0, cols.adapter.op_b_imm, cols.next_pc, cols.is_real⟩ ∧
  SP1Clean.AddOp.Assertion.Spec
    ⟨cols.state.pc.push 0, #v[4, 0, 0, 0], cols.op_a_write_value,
     cols.is_real - cols.adapter.op_a_0⟩ ∧
  SP1Clean.JTypeReader.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, 46, cols.state.pc,
     cols.op_a_write_value, cols.adapter,
     cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  cols.next_pc[3] = 0 ∧
  cols.op_a_write_value[3] = 0 ∧
  (cols.is_real = 1 ∨ cols.adapter.op_a_0 = 0) ∧
  (cols.is_real = 1 → (cols.next_pc[0] * (4 : ZMod p)⁻¹).val < 16384)

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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  (cols.lsb = 0 ∨ cols.lsb = 1) ∧
  (cols.is_real = 1 ∨ cols.adapter.op_a_0 = 0) ∧
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
  (cols.is_lb = 0 ∨ cols.is_lb = 1) ∧
  (cols.is_lbu = 0 ∨ cols.is_lbu = 1) ∧
  (cols.is_lb + cols.is_lbu = 0 ∨ cols.is_lb + cols.is_lbu = 1) ∧
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
  (cols.is_lb = 0 ∨ cols.is_lb = 1) ∧
  (cols.is_lbu = 0 ∨ cols.is_lbu = 1) ∧
  (cols.is_lb + cols.is_lbu = 0 ∨ cols.is_lb + cols.is_lbu = 1) ∧
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
  (cols.is_lh = 0 ∨ cols.is_lh = 1) ∧
  (cols.is_lhu = 0 ∨ cols.is_lhu = 1) ∧
  (cols.is_lh + cols.is_lhu = 0 ∨ cols.is_lh + cols.is_lhu = 1) ∧
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
  (cols.is_lh = 0 ∨ cols.is_lh = 1) ∧
  (cols.is_lhu = 0 ∨ cols.is_lhu = 1) ∧
  (cols.is_lh + cols.is_lhu = 0 ∨ cols.is_lh + cols.is_lhu = 1) ∧
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
  (cols.is_lw = 0 ∨ cols.is_lw = 1) ∧
  (cols.is_lwu = 0 ∨ cols.is_lwu = 1) ∧
  (cols.is_lw + cols.is_lwu = 0 ∨ cols.is_lw + cols.is_lwu = 1) ∧
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
  (cols.is_lw = 0 ∨ cols.is_lw = 1) ∧
  (cols.is_lwu = 0 ∨ cols.is_lwu = 1) ∧
  (cols.is_lw + cols.is_lwu = 0 ∨ cols.is_lw + cols.is_lwu = 1) ∧
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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, 0, 0, 0⟩ ∧
  -- ITypeReader is called with `cols.load_prev_value` as op_a_write_value (no
  -- selector/sign-extension for LD).
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.load_prev_value,
     cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, cols.is_real⟩ ∧
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Semantic RV64 conjunct (conditional on `is_real = 1`): the loaded doubleword
  -- is a valid `Word` (Word.isU64). For LD there is no byte selection or
  -- sign-extension — the loaded value `cols.load_prev_value` IS what gets
  -- written to the destination register. The isU64 bound transports through
  -- from `LoadMemoryAccessGated.Contract`. Mirrors the AddChip canonical
  -- pattern (`SP1Clean/Chips/Spec.lean:99-103`), specialized to the trivial
  -- (identity) RV64 op.
  (cols.is_real = 1 → Word.isU64 cols.load_prev_value)

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
  (cols.is_lb = 0 ∨ cols.is_lb = 1) ∧
  (cols.is_lbu = 0 ∨ cols.is_lbu = 1) ∧
  (cols.is_lh = 0 ∨ cols.is_lh = 1) ∧
  (cols.is_lhu = 0 ∨ cols.is_lhu = 1) ∧
  (cols.is_lw = 0 ∨ cols.is_lw = 1) ∧
  (cols.is_lwu = 0 ∨ cols.is_lwu = 1) ∧
  (cols.is_ld = 0 ∨ cols.is_ld = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
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
  (cols.is_lb = 0 ∨ cols.is_lb = 1) ∧
  (cols.is_lbu = 0 ∨ cols.is_lbu = 1) ∧
  (cols.is_lh = 0 ∨ cols.is_lh = 1) ∧
  (cols.is_lhu = 0 ∨ cols.is_lhu = 1) ∧
  (cols.is_lw = 0 ∨ cols.is_lw = 1) ∧
  (cols.is_lwu = 0 ∨ cols.is_lwu = 1) ∧
  (cols.is_ld = 0 ∨ cols.is_ld = 1) ∧
  (is_real = 0 ∨ is_real = 1) ∧
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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  (cols.is_real = 0 ∨ cols.is_real = 1)
  -- Note: no semantic Word.isU64 conjunct here. Unlike StoreDouble (which
  -- writes op_a_memory.prev_value directly), StoreByte composes bytes into
  -- `cols.store_value` (via the byte-selector + assembler sub-circuits). The
  -- Sail equivalence is handled in `SailBridge.lean` via `_root_.Store.StoreByte.correct`
  -- — the byte-composition correctness lives there, not in `FormalSpec`.

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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  (cols.is_real = 0 ∨ cols.is_real = 1)
  -- Note: see StoreByte FormalSpec note re: no semantic conjunct.

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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  (cols.is_real = 0 ∨ cols.is_real = 1)
  -- Note: see StoreByte FormalSpec note re: no semantic conjunct.

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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv, 0, 0, 0⟩ ∧
  SP1Clean.ITypeReaderImmutable.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, cols.adapter⟩ ∧
  -- StoreDouble: write_value is the whole op_a register value (no byte split).
  SP1Clean.StoreMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value,
     cols.store_prev_value, cols.adapter.op_a_memory.prev_value,
     cols.store_memory_prev_high, cols.store_memory_prev_low,
     cols.store_memory_diff_low, cols.store_memory_diff_high,
     cols.store_memory_flag, cols.is_real⟩ ∧
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  -- Semantic RV64 conjunct (conditional on `is_real = 1`): the data being
  -- written to memory is a valid `Word` (Word.isU64). For SD there is no
  -- byte selection — the whole `op_a_memory.prev_value` is the write data.
  -- The isU64 bound transports through from `StoreMemoryAccessGated.Contract`'s
  -- `Word.isU64 write_value` clause. Mirrors `LoadDouble.FormalSpec`'s
  -- analogous semantic clause.
  (cols.is_real = 1 → Word.isU64 cols.adapter.op_a_memory.prev_value)

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
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
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
  (cols.is_comp = 0 ∨ cols.is_comp = 1)

end Assertion

end SP1Clean.MemoryGlobal
