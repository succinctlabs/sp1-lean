import SP1Clean.SubChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `SubChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract:
- `SubOperation` arithmetic `Spec` (natural-form carry chain).
- CPU-state gated sub-circuit composition (binary gate + state-bus + byte
  opcode, all gated by `is_real`).
- Full R-type reader gated sub-circuit composition (binary gate +
  program-bus + 3 register accesses + op_a_0 masked gates, gated by
  `is_real`/`is_trusted`).
- `adapter.op_a_0 = 0` chip-level gate.
- Pure BitVec `RV64.sub` semantic (conditional on `is_real = 1`).

`Assertion.main` composes three sub-circuits — `SubOp.assertion`,
`CPUState.Gated.assertion`, `RTypeReader.Gated.assertion` — mirroring
`SP1Chips/Sub/Constraints.lean`'s single `RTypeReader.constraints` call
and the upstream Rust `SubChip::eval`'s `RTypeReader::eval` invocation 1:1.

The per-row Sail-monadic equivalence to `_root_.Sub.spec_sub` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.SubChip.SailBridge.sail_correct_of_formalSpec`.

Mirrors `SP1Clean/AddChip/Circuit.lean` 1-for-1 with `AddOp` → `SubOp` and
opcode `0` → `2`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.SubChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `SubChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: one `SubOp.assertion` +
one `CPUState.Gated.assertion` (binary gate + state-bus + byte-opcode,
all gated by `is_real`) + one `RTypeReader.Gated.assertion` (binary gate
+ program-bus + 3 register accesses + op_a_0 masked gates, gated by
`is_real`/`is_trusted`) + chip-level `op_a_0 = 0` gate. The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts (redundant but propositionally fine). -/
@[reducible]
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter,
       op_a_write_value, is_real, adapter_cols⟩ := cols
  SP1Clean.SubOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
      op_a_write_value⟩ :
      Var SP1Clean.SubOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 2, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubCols unit where
  name := "SP1Clean.Sub"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant. Its `adapter_cols.is_trusted`
payload is structurally equal to `is_real`. -/
def Assumptions (cols : SubCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.SubChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.SubChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_subop_sub, h_cpu_sub, h_rtr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_subop := h_subop_sub trivial
  have h_cpu := h_cpu_sub trivial
  have h_rtr := h_rtr_sub trivial
  refine ⟨h_subop, h_cpu, h_rtr, h_op_a_0, ?_⟩
  -- BitVec `RV64.sub` conjunct: discharge from `SubOp.Spec` (natural-form
  -- carry chain) + the per-operand `Word.isU64` bounds for op_b/op_c —
  -- inside `RTypeReader.Gated.Spec`'s 4th/5th `RegisterAccess.Spec`
  -- sub-conjuncts.
  intro h_is_real_eq
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨_h_ir_bin, _h_prog, _h_ra_a, h_ra_b, h_ra_c, _, _, _, _⟩ := h_rtr
  change (Expression.eval env input_var_is_real : ZMod p) = 1 at h_is_real_eq
  have h_ir_ne_zero :
      (Expression.eval env input_var_is_real : ZMod p) ≠ 0 := by
    rw [h_is_real_eq]; exact one_ne_zero
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    (h_ra_b.resolve_left h_ir_ne_zero).2.2
  have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value :=
    (h_ra_c.resolve_left h_ir_ne_zero).2.2
  -- Bridge the cols-level `SubOp.Spec` to SP1's constraint allHold form,
  -- then to the BitVec equation via `SubOperation.spec`.
  have h_allHold : (SubOperation.constraints
        input_adapter_op_b_memory_prev_value
        input_adapter_op_c_memory_prev_value
        { value := Vector.map (Expression.eval env) input_var_op_a_write_value }
        1).allHold :=
    (SP1Clean.SubOp.iff_sp1 _ _ _).mpr h_subop
  have ⟨_, h_bv⟩ := SubOperation.spec h_isU64_b h_isU64_c h_allHold
  -- `h_bv : op_a_write_value.toBitVec64 =
  --          op_b.toBitVec64 - op_c.toBitVec64` (from `execute_RTYPE_pure_w
  --          op_b op_c .SUB = op_b - op_c`).
  -- Goal after `RV64.sub` unfold: `op_a_write_value.toBitVec64 =
  --   RV64.sub (op_c.toBitVec64) (op_b.toBitVec64)`. Sail's `execute_RTYPE`
  --   takes `rs2 rs1` order, so `RV64.sub op_c op_b = op_b - op_c`. Match
  --   by direct substitution.
  simp only [RV64.sub]
  exact h_bv

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_subop, h_cpu, h_rtr, h_op_a_0, _h_rv64sub⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, h_subop⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_rtr⟩, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `SubChip`. Single subcircuit
composition (`SubOp.assertion + CPUState.Gated.assertion +
RTypeReader.Gated.assertion + 1 scalar gate`) backing one unified `Spec`
whose last conjunct is the pure BitVec `RV64.sub` semantic. Per-row Sail
equivalence is derived externally via `sail_correct_of_formalSpec`
(`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) SubCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubChip
