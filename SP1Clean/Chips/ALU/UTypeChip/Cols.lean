import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Chips.UType.UTypeChip
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.Operations.AddOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `UTypeChip` cols-level surface (LUI / AUIPC, bundled)

Entry-point module for `SP1Clean.UTypeChip`: defines the `UTypeCols` column
struct (mirroring SP1's Rust `UTypeCols<T, M: TrustMode>` under
`M = UserMode`), the `fromMain`/`toMain` projections between the flat
SP1 row and the structured `UTypeCols` view, and the `cols`-level
Sail-side helpers (`sp1_op_a_cols`, `sp1_op_b_cols`, `sp1_utype_cols`,
`utypeInitialState_cols`) that mirror `_root_.UType`'s Main-level
definitions but project off `UTypeCols` fields directly.

The U-type chip bundles two RV64IM variants (`auipc` and `lui`) into a
single 31-column trace, distinguished by the `is_auipc` selector at
`Main[29]`. The chip's `AddOperation` adds a conditional addend
(`is_auipc * pc` — i.e., `pc` for AUIPC, `0` for LUI) to the 32-bit
immediate, producing the 64-bit value written to `op_a`.

Imported (in order) by:
- `SP1Clean.UTypeChip.Lemmas` — non-trivial lemmas about cols
  (`fromMain_toMain`, `allHold_iff_structural`).
- `SP1Clean.UTypeChip.Circuit` — `Assertion.main`, `FormalSpec`,
  soundness/completeness, and the `assertion : FormalAssertion`.
- `SP1Clean.UTypeChip.SailBridge` — the external
  `sail_correct_of_formalSpec` Sail-equivalence bridge. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions BitVec Sail

namespace SP1Clean.UType

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `UTypeCols<T, M: TrustMode>`.
`addend` is the conditional `is_auipc * pc` carried into the AddOperation,
and `add_result` is the 64-bit AddOp output written to op_a. -/
@[ext]
structure UTypeCols (T : Type) where
  state : CPUState T
  adapter : JTypeReader T
  addend : Vector T 3
  add_result : Vector T 4
  is_auipc : T
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `UTypeCols` view. Mirrors
the index map in `SP1Chips/UType/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[30]` (= `is_real`) because the current extractor passes
`Main[30] Main[30]` to `JTypeReader.constraints`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 31) : UTypeCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    #v[Main[14], Main[15], Main[16], Main[17]],
    #v[Main[18], Main[19], Main[20], Main[21]]⟩,
   #v[Main[22], Main[23], Main[24]],
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29], Main[30],
   ⟨Main[30]⟩⟩

/-- Right inverse of `fromMain`: pack a `UTypeCols` into a 31-element flat
row using the same index map as `fromMain`. Slot 30 carries both `is_real`
and `adapter_cols.is_trusted` (matching `fromMain`'s aliasing), so the
round-trip lemma requires `cols.adapter_cols.is_trusted = cols.is_real`. -/
@[reducible] def toMain (cols : UTypeCols (ZMod p)) : Vector (ZMod p) 31 :=
  #v[cols.state.clk_high, cols.state.clk_16_24, cols.state.clk_0_16,
     cols.state.pc[0], cols.state.pc[1], cols.state.pc[2],
     cols.adapter.op_a,
     cols.adapter.op_a_memory.prev_value[0],
     cols.adapter.op_a_memory.prev_value[1],
     cols.adapter.op_a_memory.prev_value[2],
     cols.adapter.op_a_memory.prev_value[3],
     cols.adapter.op_a_memory.access_timestamp.prev_low,
     cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_0,
     cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
     cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3],
     cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
     cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3],
     cols.addend[0], cols.addend[1], cols.addend[2],
     cols.add_result[0], cols.add_result[1],
     cols.add_result[2], cols.add_result[3],
     cols.is_auipc, cols.is_real]

/-! ## Cols-level Sail-side helpers

Mirror the Main-level `_root_.UType.sp1_op_a` / `sp1_op_b` / `sp1_utype`
projections directly off `UTypeCols` fields. Each helper is `@[reducible]`
so the round-trip lemma `<helper>_cols (fromMain Main) = UType.<helper> Main`
closes by `rfl`. -/

@[reducible] def sp1_op_a_cols (cols : UTypeCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

/-- The 20-bit U-type immediate, recovered from the high 20 bits of the
constrained 32-bit immediate stored in `op_b_imm[0]`/`op_b_imm[1]`.
Mirrors `_root_.UType.sp1_op_b`. -/
@[reducible] def sp1_op_b_cols (cols : UTypeCols (ZMod p)) : BitVec 20 :=
  BitVec.ofNat 20 (cols.adapter.op_b_imm[0].val / 4096 +
                   cols.adapter.op_b_imm[1].val * 16)

/-- The SP1 implementation: shared between AUIPC and LUI; the addend
(`pc` for AUIPC, `0` for LUI) is built into the trace via the `addend`
field. Mirrors `_root_.UType.sp1_utype`. -/
def sp1_utype_cols (cols : UTypeCols (ZMod p)) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg (sp1_op_a_cols cols) (Word.toBitVec64 cols.add_result)
  return RETIRE_SUCCESS

/-- The cols-level state-bus precondition for the per-row Sail clause,
mirroring `addiInitialState_cols`: universally lifted over any flat `Main`
row that re-projects to the given `cols`. -/
def utypeInitialState_cols (cols : UTypeCols (ZMod p)) (s : SailState) : Prop :=
  ∀ Main : Vector (ZMod p) 31, fromMain Main = cols →
    (_root_.UType.constraints Main).initialState s

/-- The op_a register access (read prior, write result), exposed for
trace-level OfflineMemory aggregation. `write_value` at aggregation time
is `cols.add_result`. Consumed by `SP1Clean.Soundness.MemoryConsistency`. -/
def opAMemoryAccess (cols : UTypeCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

/-! ### Round-trip lemmas

Each `cols`-level helper equals the corresponding `Main`-level def when
applied to `fromMain Main`. All hold by `rfl` thanks to `@[reducible]`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_a_cols_fromMain (Main : Vector (ZMod p) 31) :
    sp1_op_a_cols (fromMain Main) = _root_.UType.sp1_op_a Main := rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_op_b_cols_fromMain (Main : Vector (ZMod p) 31) :
    sp1_op_b_cols (fromMain Main) = _root_.UType.sp1_op_b Main := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] lemma sp1_utype_cols_fromMain (Main : Vector (ZMod p) 31) :
    sp1_utype_cols (fromMain Main) = _root_.UType.sp1_utype Main := by
  rfl

/-! ## Chip-level `FormalSpec`

The unified chip Spec. Composes the granular subcircuit Specs that
`Assertion.main` emits, matching the monolith's TraceSpec shape (cpuStateSpec
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
      (if cols.is_auipc = 1
       then RV64.auipc (sp1_op_b_cols cols)
                       (Word.toBitVec64
                          #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], (0 : ZMod p)])
       else RV64.lui (sp1_op_b_cols cols)))

end SP1Clean.UType
