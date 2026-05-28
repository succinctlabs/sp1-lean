import SP1Clean.Chips.Control.JalChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Clean.Operations.AddOperation
import SP1Chips.Jal.Common

/-! # `JalChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.Jal.constraints Main).allHold`
  under `Main[30] = 1` to the canonical (a) structural conjunction over
  `fromMain Main`: `CPUState.Gated.Assertion.Spec`, two `AddOp.Assertion.Spec`
  (jump-target gated by `Main[30]`, return-address gated by `Main[30] - Main[13]
  = 1 - Main[13]`), `JTypeReader.Gated.Assertion.Spec` (with both `is_real` and
  `is_trusted` instantiated to `Main[30] = 1`), four scalar gates (`Main[25] = 0`
  next_pc[3]=0, `Main[29] = 0` op_a_write_value[3]=0, `Main[30] = 1 ∨ Main[13]
  = 0`, and the jump-target alignment Range14 consequence). Used downstream by
  `SailBridge.lean` to reconstruct SP1's `allHold` from the structural conjuncts
  of `FormalSpec`. **Structural sorry stub** for now (mirrors `UTypeChip/
  Circuit.lean`'s sorry'd soundness/completeness — both flow from the new
  canonical-(a) Spec shape and need the same proof restructuring); the
  one-directional `formalSpec_implies_allHold` direction can be reconstructed
  via the legacy `Jal.allHold_constraints_iff` (`SP1Chips/Jal/Common.lean:18`)
  plus `AddOperation.iff_sp1_full` plus `JTypeReader.Gated.Assertion.Spec_iff_sp1`
  using the operand `Word.isU64` bound from the JTypeReader's program-bus
  clause; that closure is mechanical but interacts with the inline-sends shape
  of `Jal.constraints` (no `CPUState.constraints` / `JTypeReader.constraints`
  sub-call envelope to bridge through directly). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[30] = is_real` (the chip
is UserMode). Recursive `ext` through `@[ext]`-marked `JalCols` / `CPUState` /
`JTypeReader` / `MemoryAccessInSharedCols` / `UserModeReaderCols` sub-structures
reduces to per-element `rfl`s via `Vector.ext` + `interval_cases`. -/
lemma fromMain_toMain (cols : JalCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, next_pc, op_a_write_value, is_real, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩
  rcases op_a_memory with ⟨prev_value, ts⟩
  rcases ts with ⟨prev_low, diff_low_limb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have : is_trusted = is_real := by simpa using h_trusted
  simp only [this, fromMain, toMain, JalCols.mk.injEq, CPUState.mk.injEq,
    JTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Jal.constraints Main` is exactly the canonical-(a) structural conjunction
under `is_real = Main[30] = 1`. Mirrors UTypeChip's `allHold_iff_structural`
in role.

**Structural sorry stub.** The forward direction is straightforward via
`Jal.allHold_constraints_iff` (`SP1Chips/Jal/Common.lean:18`) plus
`AddOperation.iff_sp1_full`. The reverse direction reconstructs the 24
inline propositional conjuncts of `Jal.constraints` from the four canonical
sub-circuit Specs — straightforward once the inline-send shape is mapped to
the `CPUState.Gated.Assertion.Spec` / `JTypeReader.Gated.Assertion.Spec`
conjuncts (no `CPUState.constraints` / `JTypeReader.constraints` sub-call
envelope to bridge through directly, unlike AddChip/UType). Closing this is
mechanical and tracked alongside the `UTypeChip/Circuit.lean` sorry'd
soundness/completeness. -/
theorem allHold_iff_structural
    (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1) :
    (_root_.Jal.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[22], Main[23], Main[24]], 8, Main[30]⟩ ∧
       SP1Clean.AddOp.Assertion.Spec
          ⟨#v[Main[3], Main[4], Main[5], 0],
           #v[Main[14], Main[15], Main[16], Main[17]],
           #v[Main[22], Main[23], Main[24], Main[25]],
           Main[30]⟩ ∧
       SP1Clean.AddOp.Assertion.Spec
          ⟨#v[Main[3], Main[4], Main[5], 0],
           #v[4, 0, 0, 0],
           #v[Main[26], Main[27], Main[28], Main[29]],
           Main[30] - Main[13]⟩ ∧
       SP1Clean.JTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 46,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[26], Main[27], Main[28], Main[29]],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13],
             op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
             op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] },
           1, 1⟩ ∧
       Main[25] = 0 ∧
       Main[29] = 0 ∧
       (Main[30] = 1 ∨ Main[13] = 0) ∧
       (Main[30] = 1 → (Main[22] * (4 : ZMod p)⁻¹).val < 16384)) := by
  sorry

/-! ## Chip-level FormalSpec ↔ sub-circuit Specs

Stable midpoint of `JalChip`'s `soundness` / `completeness` proofs, mirroring
`AddChip`'s eponymous lemmas. JalChip composes *two* `AddOp` sub-circuits
(jump-target gated by `is_real`, return-address gated by `is_real - op_a_0`):
the second gate's binarity is recovered from `JTypeReader`'s program-bus
`op_a_0 ∈ {0,1}` clause, and the operand `Word.isU64` bounds come from the
chip-level `Assumptions` (`Word.isU64 (pc.push 0)` / `Word.isU64 op_b_imm`). -/

/-- **Forward** (soundness midpoint): assemble the chip-level `FormalSpec`
from the per-sub-circuit Specs returned by `circuit_proof_start`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : JalCols (ZMod p))
    (h_is_real : cols.is_real = 1)
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_isU64_pc : Word.isU64 (cols.state.pc.push 0))
    (h_isU64_opb : Word.isU64 cols.adapter.op_b_imm)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state, #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]], 8,
         cols.is_real⟩)
    (h_addop1 : SP1Clean.AddOp.Assertion.Assumptions
        ⟨cols.state.pc.push 0, cols.adapter.op_b_imm, cols.next_pc, cols.is_real⟩ →
      SP1Clean.AddOp.Assertion.Spec
        ⟨cols.state.pc.push 0, cols.adapter.op_b_imm, cols.next_pc, cols.is_real⟩)
    (h_addop2 : SP1Clean.AddOp.Assertion.Assumptions
        ⟨cols.state.pc.push 0, #v[4, 0, 0, 0], cols.op_a_write_value,
         cols.is_real - cols.adapter.op_a_0⟩ →
      SP1Clean.AddOp.Assertion.Spec
        ⟨cols.state.pc.push 0, #v[4, 0, 0, 0], cols.op_a_write_value,
         cols.is_real - cols.adapter.op_a_0⟩)
    (h_jtr : SP1Clean.JTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         46, cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_real, cols.adapter_cols.is_trusted⟩)
    (h_byteopcode : SP1Lookup.ByteOpcodeGated.Spec
        ⟨#v[(6 : ZMod p), cols.next_pc[0] * (4 : ZMod p)⁻¹, 14, 0], cols.is_real⟩)
    (h_g1 : cols.next_pc[3] = 0)
    (h_g2 : cols.op_a_write_value[3] = 0) :
    Assertion.FormalSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_trusted1 : cols.adapter_cols.is_trusted = 1 := by rw [h_trusted, h_is_real]
  -- `op_a_0 ∈ {0,1}` from `JTypeReader`'s `ProgramSpec` clause (under is_trusted = 1).
  have h_op_a_0_bin : cols.adapter.op_a_0 = 0 ∨ cols.adapter.op_a_0 = 1 := by
    have h_prog := h_jtr.2.1
    have h_progspec := h_prog.resolve_left (by rw [h_trusted1]; exact one_ne_zero)
    exact h_progspec.2.2.2.2.1
  refine ⟨h_cpu, ?_, ?_, h_jtr, h_g1, h_g2, Or.inl h_is_real, ?_⟩
  · -- AddOp jump-target Spec.
    exact h_addop1 ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_pc, h_isU64_opb⟩⟩
  · -- AddOp return-address Spec; gate `is_real - op_a_0` binarity from op_a_0 ∈ {0,1}.
    refine h_addop2 ⟨?_, fun _ => ⟨h_isU64_pc, Word.four_isU64⟩⟩
    rcases h_op_a_0_bin with h | h
    · right; rw [h, h_is_real]; ring
    · left; rw [h, h_is_real]; ring
  · -- Jump-target 4-alignment Range14 from `byteOpcodeGated.Spec` under is_real = 1.
    intro _
    have h_bspec := h_byteopcode.resolve_left (by rw [h_is_real]; exact one_ne_zero)
    have h_range := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range _ _ _ h_bspec
    have hval14 : (14 : ZMod p).val = 14 := by
      rw [show (14 : ZMod p) = ((14 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast,
          Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
    rw [hval14] at h_range
    exact h_range

/-- **Backward** (completeness midpoint): peel the chip-level `FormalSpec` into
the per-sub-circuit Specs. The `byteOpcodeGated` Spec is reconstructed from the
`FormalSpec` alignment range (under `is_real = 1`), and `op_a_0 ∈ {0,1}` is
re-extracted from `JTypeReader`'s `ProgramSpec` clause. -/
lemma subcircuit_specs_of_formalSpec
    (cols : JalCols (ZMod p))
    (h_is_real : cols.is_real = 1)
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_spec : Assertion.FormalSpec cols) :
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state, #v[cols.next_pc[0], cols.next_pc[1], cols.next_pc[2]], 8,
         cols.is_real⟩ ∧
    SP1Clean.AddOp.Assertion.Spec
        ⟨cols.state.pc.push 0, cols.adapter.op_b_imm, cols.next_pc, cols.is_real⟩ ∧
    SP1Clean.AddOp.Assertion.Spec
        ⟨cols.state.pc.push 0, #v[4, 0, 0, 0], cols.op_a_write_value,
         cols.is_real - cols.adapter.op_a_0⟩ ∧
    SP1Clean.JTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         46, cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
    SP1Lookup.ByteOpcodeGated.Spec
        ⟨#v[(6 : ZMod p), cols.next_pc[0] * (4 : ZMod p)⁻¹, 14, 0], cols.is_real⟩ ∧
    (cols.adapter.op_a_0 = 0 ∨ cols.adapter.op_a_0 = 1) ∧
    cols.next_pc[3] = 0 ∧
    cols.op_a_write_value[3] = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_addop1, h_addop2, h_jtr, h_g1, h_g2, _h_or, h_align⟩ := h_spec
  refine ⟨h_cpu, h_addop1, h_addop2, h_jtr, ?_, ?_, h_g1, h_g2⟩
  · -- `byteOpcodeGated.Spec` from the alignment range (real row).
    right
    apply SP1Clean.AddOp.Assertion.byteOpcodeSpec_range_of_lt
    have hval14 : (14 : ZMod p).val = 14 := by
      rw [show (14 : ZMod p) = ((14 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast,
          Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
    rw [hval14]
    exact h_align h_is_real
  · -- `op_a_0 ∈ {0,1}` from `JTypeReader`'s `ProgramSpec` clause.
    have h_trusted1 : cols.adapter_cols.is_trusted = 1 := by rw [h_trusted, h_is_real]
    have h_prog := h_jtr.2.1
    have h_progspec := h_prog.resolve_left (by rw [h_trusted1]; exact one_ne_zero)
    exact h_progspec.2.2.2.2.1

end SP1Clean.Jal
