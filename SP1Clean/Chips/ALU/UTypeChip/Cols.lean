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
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
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

end SP1Clean.UType
