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
import SP1Clean.Reader.JTypeReader
import SP1Clean.Reader.RegisterAccess
import SP1Clean.Operations.GatedAddOp
import SP1Clean.SP1Lookup
import SP1Clean.TrustMode
import SP1Clean.Chips.Control.JalChip.Multiplicity.Cols

/-! # `JalChip` Clean circuit + `FormalAssertion` (multiplicity-aware redesign)

Faithful structural mirror of Rust `JalChip::eval`
(`sp1/crates/core/machine/src/control_flow/jal/air.rs:24-144`). Every
`builder.assert_*` / sub-eval invocation in `air.rs` maps to exactly one
sub-`FormalAssertion` (or one scalar gate) in `main`, with the same
multiplicity argument made explicit. Mirrors the AddwChip template
(`SP1Clean/AddwChip/Circuit.lean`) but for control-flow chips that
gate sub-AddOps by `is_real` / `is_real - op_a_0`.

Sub-circuits composed (in `air.rs` source order):
1. `is_real` boolean gate.                                        (air.rs:29)
2. `GatedAddOp.assertion` for `pc + op_b_imm = next_pc`,
   `gate := is_real`.                                              (air.rs:49)
3. `next_pc[3] === 0`.                                            (air.rs:52)
4. `SP1Lookup.byteOpcodeGated` for `next_pc[0] * 4⁻¹ ∈ Range14`,
   `mult := is_real`.                                              (air.rs:55-61)
5. `CPUState.assertion` (clock-fields range bounds).               (air.rs:66-72)
6. `(is_real - 1) * op_a_0 === 0` (when_not(is_real) gate).        (air.rs:74)
7. `GatedAddOp.assertion` for `pc + 4 = op_a_write_value`,
   `gate := is_real - op_a_0`.                                     (air.rs:92)
8. `op_a_write_value[3] === 0`.                                   (air.rs:93)
9. Three `op_a_0 * op_a_write_value[i] === 0` gates, i = 0..2.    (air.rs:94-96)
10. `JTypeReader.Gated.assertion` (program-bus + op_a register
    access write at +4), `is_real := is_real`,
    `is_trusted := adapter_cols.is_trusted`.                        (air.rs:133-143)

Sail bridging (`spec_implies_allHold`, `correct_jal`, `iff_sp1`) is
deferred; the sibling iter-9 Approach A baseline lives in
`SP1Clean/JalChip.lean` and is unaffected by this file. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

-- Derive `Fact (p > 512)` from `Fact (2 ^ 17 < p)` for byteOpcodeGated.
instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Clean-side chip circuit. One sub-`FormalAssertion` per Rust
`air.rs` eval invocation; see the file docstring for the 1-to-1 map. -/
@[reducible]
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       next_pc, op_a_write_value, is_real, adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  -- (1) is_real boolean (air.rs:29).
  is_real * (is_real - 1) === 0
  -- (2) AddOperation for jump target (pc + op_b_imm = next_pc),
  --     gated by is_real (air.rs:49).
  SP1Clean.GatedAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], 0], adapter.op_b_imm, next_pc, is_real⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (3) next_pc[3] = 0 (air.rs:52).
  next_pc[3] === 0
  -- (4) Byte-bus send: next_pc[0] / 4 ∈ Range14, gated by is_real
  --     (air.rs:55-61).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), next_pc[0] * (4 : ZMod p)⁻¹, 14, 0],
       is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- (5) CPUState clock-fields range bounds (air.rs:66-72).
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- (6) when_not(is_real).assert_zero(op_a_0) (air.rs:74).
  (is_real - 1) * adapter.op_a_0 === 0
  -- (7) AddOperation for return address (pc + 4 = op_a_write_value),
  --     gated by `is_real - op_a_0` (air.rs:92).
  SP1Clean.GatedAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], 0], #v[4, 0, 0, 0], op_a_write_value, is_real - adapter.op_a_0⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (8) op_a_write_value[3] = 0 (air.rs:93).
  op_a_write_value[3] === 0
  -- (9) op_a_0 * op_a_write_value[i] = 0 for i ∈ {0,1,2} (air.rs:94-96).
  adapter.op_a_0 * op_a_write_value[0] === 0
  adapter.op_a_0 * op_a_write_value[1] === 0
  adapter.op_a_0 * op_a_write_value[2] === 0
  -- (10) JTypeReader.Gated: program-bus send + op_a register-access
  --      write (air.rs:133-143). Untrusted-mode default:
  --      `is_trusted = adapter_cols.is_trusted`.
  SP1Clean.JTypeReader.Gated.assertion
    (⟨clk_high, clk_low, 46, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.JTypeReader.Gated.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalCols unit where
  name := "SP1Clean.Jal"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : JalCols (ZMod p)) : Prop := True

/-- Chip-level `FormalSpec`: composes the sub-`Spec`s of each
sub-`FormalAssertion` in `main`. Each conjunct corresponds to one
numbered emission in the docstring (in the same order). -/
def FormalSpec (cols : JalCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  (cols.is_real = 0 ∨ cols.is_real - 1 = 0) ∧                                      -- (1)
  SP1Clean.GatedAddOp.assertion.Spec                                                   -- (2)
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0], cols.adapter.op_b_imm, cols.next_pc, cols.is_real⟩ ∧
  cols.next_pc[3] = 0 ∧                                                            -- (3)
  SP1Lookup.ByteOpcodeGated.Spec                                                   -- (4)
    ⟨#v[(6 : ZMod p), cols.next_pc[0] * (4 : ZMod p)⁻¹, 14, 0], cols.is_real⟩ ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧        -- (5)
  (cols.is_real - 1 = 0 ∨ cols.adapter.op_a_0 = 0) ∧                               -- (6)
  SP1Clean.GatedAddOp.assertion.Spec                                                   -- (7)
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0], #v[4, 0, 0, 0], cols.op_a_write_value,
     cols.is_real - cols.adapter.op_a_0⟩ ∧
  cols.op_a_write_value[3] = 0 ∧                                                   -- (8)
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[0] = 0) ∧                             -- (9)
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[1] = 0) ∧
  (cols.adapter.op_a_0 = 0 ∨ cols.op_a_write_value[2] = 0) ∧
  SP1Clean.JTypeReader.Gated.Assertion.Spec                                        -- (10)
    ⟨cols.state.clk_high, clk_low, 46, cols.state.pc, cols.op_a_write_value,
     cols.adapter, cols.is_real, cols.adapter_cols.is_trusted⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c16_24, e_c0_16, e_pc⟩,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_obi, e_oci⟩,
          e_npc, e_oawv, e_ir, e_at⟩ := h_input
  subst_eqs
  obtain ⟨h_isreal_bool, h_add_jump_sub, h_npc3, h_byte_sub, h_cpu_sub,
          h_when_not, h_add_ret_sub, h_oawv3, h_z0, h_z1, h_z2,
          h_jtype_sub⟩ := h_holds
  unfold id at *
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg]
  simp only [mul_eq_zero] at h_isreal_bool h_when_not h_z0 h_z1 h_z2
  exact ⟨h_isreal_bool, h_add_jump_sub trivial, h_npc3, h_byte_sub trivial,
         h_cpu_sub trivial, h_when_not, h_add_ret_sub trivial, h_oawv3,
         h_z0, h_z1, h_z2, h_jtype_sub trivial⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c16_24, e_c0_16, e_pc⟩,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_obi, e_oci⟩,
          e_npc, e_oawv, e_ir, e_at⟩ := h_input
  subst_eqs
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨h_isreal_bool, h_add_jump, h_npc3, h_byte, h_cpu,
          h_when_not, h_add_ret, h_oawv3, h_z0, h_z1, h_z2, h_jtype⟩ := h_spec
  unfold id at *
  simp only [mul_eq_zero]
  exact ⟨h_isreal_bool, ⟨trivial, h_add_jump⟩, h_npc3, ⟨trivial, h_byte⟩,
         ⟨trivial, h_cpu⟩, h_when_not, ⟨trivial, h_add_ret⟩, h_oawv3,
         h_z0, h_z1, h_z2, ⟨trivial, h_jtype⟩⟩

end Assertion

/-- The full Clean `FormalAssertion` for `JalChip` rebuilt on the
multiplicity-aware lookup bus. -/
def assertion : FormalAssertion (ZMod p) JalCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jal
