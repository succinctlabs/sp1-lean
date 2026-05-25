import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.RegisterAccess
import SP1Clean.Operations.GatedAddOp
import SP1Clean.SP1Lookup
import SP1Clean.TrustMode
import SP1Clean.Jalr.Cols

/-! # `JalrChip` Clean circuit + `FormalAssertion` (multiplicity-aware redesign)

Faithful structural mirror of Rust `JalrChip::eval`
(`sp1/crates/core/machine/src/control_flow/jalr/air.rs:29-153`). Every
`builder.assert_*` / sub-eval invocation in `air.rs` maps to exactly one
sub-`FormalAssertion` (or one scalar gate) in `main`, with the same
multiplicity argument made explicit.

Differences from `SP1Clean.Jal.Circuit`:
- The jump-target add is `op_b_memory.prev_value + op_c_imm`, not
  `pc + op_b_imm` (JALR computes from a register value, not from PC).
- An `lsb` column captures `(op_b + op_c) & 1` and is subtracted from
  `jump_target[0]` before the alignment range lookup (RISC-V `JALR`
  clears bit 0 of the next PC).
- Uses `ITypeReader.Gated` (op_b is a register, op_c is a 4-limb
  immediate) instead of `JTypeReader.Gated`.

Sub-circuits composed (in `air.rs` source order):
1. `is_real * (is_real - 1) === 0`.                                  (air.rs:34)
2. `GatedAddOp.assertion` for `op_b + op_c = jump_target`,
   `gate := is_real`.                                                (air.rs:49)
3. `jump_target[3] === 0`.                                           (air.rs:52)
4. `lsb * (lsb - 1) === 0`.                                          (air.rs:55)
5. `SP1Lookup.byteOpcodeGated` for `(jump_target[0] - lsb) * 4⁻¹
    ∈ Range14`, `mult := is_real`.                                   (air.rs:60-66)
6. `CPUState.assertion`.                                             (air.rs:71-79)
7. `ITypeReader.Gated.assertion` (program-bus + 2 register accesses
   for op_a write at +4 and op_b read at +3),
   `is_real := is_real`,
   `is_trusted := adapter_cols.is_trusted`.                          (air.rs:112-124)
8. `(is_real - 1) * op_a_0 === 0`.                                   (air.rs:126)
9. `GatedAddOp.assertion` for `pc + 4 = op_a_write_value`,
   `gate := is_real - op_a_0`.                                       (air.rs:148)
10. `op_a_write_value[3] === 0`.                                    (air.rs:149)
11. Three `op_a_0 * op_a_write_value[i] === 0` gates, i = 0..2.     (air.rs:150-152)

Sail bridging is deferred; the iter-9 Approach A baseline lives in
`SP1Clean/JalrChip.lean`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jalr

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

-- Derive `Fact (p > 512)` from `Fact (2 ^ 17 < p)` for byteOpcodeGated.
instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Clean-side chip circuit. One sub-`FormalAssertion` per Rust
`air.rs` eval invocation; see the file docstring for the 1-to-1 map. -/
@[reducible]
def main (cols : Var JalrCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       is_real, jump_target, op_a_write_value, lsb, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  -- (1) is_real boolean (air.rs:34).
  is_real * (is_real - 1) === 0
  -- (2) AddOperation for jump target (op_b + op_c_imm = jump_target),
  --     gated by is_real (air.rs:49). Note: a is the register's prev
  --     value (4 limbs), not the PC.
  SP1Clean.GatedAddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_imm, jump_target, is_real⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (3) jump_target[3] = 0 (air.rs:52).
  jump_target[3] === 0
  -- (4) lsb boolean (air.rs:55).
  lsb * (lsb - 1) === 0
  -- (5) Byte-bus send: (jump_target[0] - lsb) / 4 ∈ Range14, gated by
  --     is_real (air.rs:60-66). RISC-V JALR clears bit 0 of next PC.
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)),
         (jump_target[0] - lsb) * (4 : ZMod p)⁻¹, 14, 0],
       is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- (6) CPUState clock-fields range bounds (air.rs:71-79).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- (7) ITypeReader.Gated: program-bus + op_a/op_b register accesses
  --     (air.rs:112-124). Opcode 47 = JALR. Untrusted-mode default:
  --     `is_trusted = adapter_cols.is_trusted`.
  SP1Clean.ITypeReader.Gated.assertion
    (⟨clk_high, clk_low, 47, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ITypeReader.Gated.Inputs (ZMod p))
  -- (8) when_not(is_real).assert_zero(op_a_0) (air.rs:126).
  (is_real - 1) * adapter.op_a_0 === 0
  -- (9) AddOperation for return address (pc + 4 = op_a_write_value),
  --     gated by `is_real - op_a_0` (air.rs:148).
  SP1Clean.GatedAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], 0], #v[4, 0, 0, 0],
       op_a_write_value, is_real - adapter.op_a_0⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (10) op_a_write_value[3] = 0 (air.rs:149).
  op_a_write_value[3] === 0
  -- (11) op_a_0 * op_a_write_value[i] = 0 for i ∈ {0,1,2} (air.rs:150-152).
  adapter.op_a_0 * op_a_write_value[0] === 0
  adapter.op_a_0 * op_a_write_value[1] === 0
  adapter.op_a_0 * op_a_write_value[2] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalrCols unit where
  name := "SP1Clean.Jalr"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : JalrCols (ZMod p)) : Prop := True

/-- Chip-level `FormalSpec`. Each conjunct corresponds to one numbered
emission in the docstring (in the same order). -/
def FormalSpec (cols : JalrCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  (cols.is_real = 0 ∨ cols.is_real - 1 = 0) ∧                                      -- (1)
  SP1Clean.GatedAddOp.assertion.Spec                                               -- (2)
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
     cols.jump_target, cols.is_real⟩ ∧
  cols.jump_target[3] = 0 ∧                                                        -- (3)
  (cols.lsb = 0 ∨ cols.lsb - 1 = 0) ∧                                              -- (4)
  SP1Lookup.ByteOpcodeGated.Spec                                                   -- (5)
    ⟨#v[(6 : ZMod p), (cols.jump_target[0] - cols.lsb) * (4 : ZMod p)⁻¹, 14, 0],
     cols.is_real⟩ ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧        -- (6)
  SP1Clean.ITypeReader.Gated.Assertion.Spec                                        -- (7)
    ⟨cols.state.clk_high, clk_low, 47, cols.state.pc, cols.op_a_write_value,
     cols.adapter, cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
  (cols.is_real - 1 = 0 ∨ cols.adapter.op_a_0 = 0) ∧                               -- (8)
  SP1Clean.GatedAddOp.assertion.Spec                                               -- (9)
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[4, 0, 0, 0], cols.op_a_write_value,
     cols.is_real - cols.adapter.op_a_0⟩ ∧
  cols.op_a_write_value[3] = 0 ∧                                                   -- (10)
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[0] = 0) ∧                       -- (11)
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[1] = 0) ∧
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[2] = 0)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c16_24, e_c0_16, e_pc⟩,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩,
          e_ir, e_jt, e_oawv, e_lsb, e_at⟩ := h_input
  subst_eqs
  obtain ⟨h_isreal_bool, h_add_jump_sub, h_jt3, h_lsb_bool, h_byte_sub,
          h_cpu_sub, h_itype_sub, h_when_not, h_add_ret_sub, h_oawv3,
          h_z0, h_z1, h_z2⟩ := h_holds
  unfold id at *
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg]
  simp only [mul_eq_zero] at h_isreal_bool h_lsb_bool h_when_not h_z0 h_z1 h_z2
  exact ⟨h_isreal_bool, h_add_jump_sub trivial, h_jt3, h_lsb_bool,
         h_byte_sub trivial, h_cpu_sub trivial, h_itype_sub trivial,
         h_when_not, h_add_ret_sub trivial, h_oawv3, h_z0, h_z1, h_z2⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c16_24, e_c0_16, e_pc⟩,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩,
          e_ir, e_jt, e_oawv, e_lsb, e_at⟩ := h_input
  subst_eqs
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨h_isreal_bool, h_add_jump, h_jt3, h_lsb_bool, h_byte, h_cpu,
          h_itype, h_when_not, h_add_ret, h_oawv3, h_z0, h_z1, h_z2⟩ := h_spec
  unfold id at *
  simp only [mul_eq_zero]
  exact ⟨h_isreal_bool, ⟨trivial, h_add_jump⟩, h_jt3, h_lsb_bool,
         ⟨trivial, h_byte⟩, ⟨trivial, h_cpu⟩, ⟨trivial, h_itype⟩,
         h_when_not, ⟨trivial, h_add_ret⟩, h_oawv3, h_z0, h_z1, h_z2⟩

end Assertion

/-- The full Clean `FormalAssertion` for `JalrChip` rebuilt on the
multiplicity-aware lookup bus. -/
def assertion : FormalAssertion (ZMod p) JalrCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jalr
