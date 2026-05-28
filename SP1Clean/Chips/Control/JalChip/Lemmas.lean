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
  of `FormalSpec`. **Closed (axiom-clean).** Because `Jal.constraints` inlines
  and interleaves the CPUState / JTypeReader sends (no `CPUState.constraints` /
  `JTypeReader.constraints` sub-call envelope), the decomposition first refolds
  the flat list into the envelope form by a direct atom-matching `obtain`/`refine`
  (the atoms agree as a multiset; `tauto` whnf-times-out on the ~50-atom goal),
  then bridges via `CPUState.Gated.Assertion.Spec_iff_sp1` /
  `JTypeReader.Gated.Assertion.Spec_iff_sp1` plus `AddOperation.iff_sp1_full`
  for the two AddOp pieces (operand `Word.isU64` bounds from the JTypeReader
  program-bus clause; the return-AddOp gate `1 - Main[13]` needs a
  `Main[13] ∈ {0,1}` case-split). -/

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

Closed axiom-clean. The interleaved inline sends of `Jal.constraints` are
first refolded into the `CPUState.constraints` / `JTypeReader.constraints`
envelope form by direct atom-matching (the two sides agree as a multiset of
propositions; the redundant `Main[30] * (Main[30] - 1) = 0` gate and the
`Main[13] * (Main[k] - 0)` dups collapse via `sub_zero`/`trivial`). The two
envelopes then bridge to the Gated Specs via `*.Gated.Assertion.Spec_iff_sp1`,
and the two AddOp pieces via `AddOperation.iff_sp1_full` (operand `Word.isU64`
bounds from the JTypeReader program-bus clause; the return-AddOp gate
`1 - Main[13]` under a `Main[13] ∈ {0,1}` case-split). -/
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
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Step 1: refold Jal's flat inline-send list into CPUState / two AddOp /
  -- JTypeReader sub-`.allHold` envelopes plus the trailing scalar gates.
  -- The inline sends are interleaved (not block-grouped like UType), so the
  -- iff is proved order-independently via `tauto` after unfolding both sides
  -- to the same atom set (`CPUState.constraints` / `JTypeReader.constraints`
  -- unfolded on the RHS too).
  rw [show (_root_.Jal.constraints Main).allHold ↔
        ((_root_.CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[22], Main[23], Main[24]] 8 Main[30]).allHold ∧
          (_root_.AddOperation.constraints (F := ZMod p)
              #v[Main[3], Main[4], Main[5], 0]
              #v[Main[14], Main[15], Main[16], Main[17]]
              { value := #v[Main[22], Main[23], Main[24], Main[25]] }
              Main[30]).allHold ∧
          (_root_.AddOperation.constraints (F := ZMod p)
              #v[Main[3], Main[4], Main[5], 0]
              #v[4, 0, 0, 0]
              { value := #v[Main[26], Main[27], Main[28], Main[29]] }
              (Main[30] - Main[13])).allHold ∧
          (_root_.JTypeReader.constraints (F := ZMod p)
              Main[0] (Main[2] + Main[1] * 65536)
              #v[Main[3], Main[4], Main[5]]
              46
              #v[Main[26], Main[27], Main[28], Main[29]]
              { op_a := Main[6],
                op_a_memory :=
                  { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                    access_timestamp :=
                      { prev_low := Main[11], diff_low_limb := Main[12] } },
                op_a_0 := Main[13],
                op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
                op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] }
              Main[30] Main[30]).allHold ∧
          (Main[25] = 0 ∧
           Main[29] = 0 ∧
           (Main[30] ≠ 0 → (ByteOpcode.ofNat 6).constrain (Main[22] * (4 : ZMod p)⁻¹) 14 0) ∧
           (Main[30] - 1) * Main[13] = 0)) from by
      have hval46 : (46 : ZMod p).val = 46 := by
        rw [show (46 : ZMod p) = ((46 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast,
            Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      simp only [_root_.Jal.constraints, _root_.CPUState.constraints,
        _root_.JTypeReader.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, coeHead_zmod_eq_val, hval46, sub_zero, and_assoc]
      push_cast
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _⟩ := h
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _⟩ := h
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial]
  -- Step 2: convert the CPUState / JTypeReader envelopes into their `Gated`
  -- Specs; collapse the return-AddOp gate `Main[30] - Main[13]` to `1 - Main[13]`.
  rw [show Main[30] - Main[13] = (1 : ZMod p) - Main[13] from by rw [h_is_real],
      h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.JTypeReader.Gated.Assertion.Spec_iff_sp1]
  push_cast
  -- Local helpers used in both directions.
  haveI h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
  refine ⟨?_, ?_⟩
  · -- Forward: envelopes → structural spec.
    rintro ⟨h_cpu, h_addop_jump, h_addop_ret, h_jtr, h_m25, h_m29, h_align, h_ret_gate⟩
    -- Extract op_b_imm bounds, pc bounds, op_a_0 binarity from JTypeReader Spec.
    have h_jtr_copy := h_jtr
    obtain ⟨_, h_prog_disj, _, _, _, _, _⟩ := h_jtr
    have h_prog := h_prog_disj.resolve_left h_one_ne_zero
    simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
    obtain ⟨_, _, ⟨h_ob0, h_ob1, h_ob2, h_ob3⟩, _, h_op_a_0_bin, _, _, _,
            h_pc0_mod, h_pc0_lt_raw, h_pc1_lt_raw, h_pc2_lt_raw⟩ := h_prog
    have h_isU64_op_b : Word.isU64
        #v[Main[14], Main[15], Main[16], Main[17]] :=
      Word.isU64_of_cases (lt65k _ h_ob0) (lt65k _ h_ob1)
                          (lt65k _ h_ob2) (lt65k _ h_ob3)
    have h_pc0_lt := lt65k _ h_pc0_lt_raw
    have h_pc1_lt := lt65k _ h_pc1_lt_raw
    have h_pc2_lt := lt65k _ h_pc2_lt_raw
    have h_isU64_pc : Word.isU64
        #v[Main[3], Main[4], Main[5], (0 : ZMod p)] :=
      Word.isU64_of_cases h_pc0_lt h_pc1_lt h_pc2_lt (by simp [ZMod.val_zero])
    refine ⟨h_cpu, ?_, ?_, h_jtr_copy, h_m25, h_m29, Or.inl rfl, ?_⟩
    · -- Jump AddOp Spec (gate 1).
      intro _
      exact (AddOperation.iff_sp1_full h_isU64_pc h_isU64_op_b).mp h_addop_jump
    · -- Return AddOp Spec (gate 1 - Main[13]).
      intro h_gate
      have h13_zero : Main[13] = 0 := by linear_combination -h_gate
      have h_addop_ret' : (_root_.AddOperation.constraints (F := ZMod p)
            #v[Main[3], Main[4], Main[5], 0]
            #v[4, 0, 0, 0]
            { value := #v[Main[26], Main[27], Main[28], Main[29]] } 1).allHold := by
        have := h_addop_ret
        rw [h13_zero, sub_zero] at this
        exact this
      exact (AddOperation.iff_sp1_full h_isU64_pc Word.four_isU64).mp h_addop_ret'
    · -- Jump-target alignment Range14 consequence.
      intro _
      have h_bc := h_align one_ne_zero
      have hval14 : (14 : ZMod p).val = 14 := by
        rw [show (14 : ZMod p) = ((14 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast,
            Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      simp only [ByteOpcode.ofNat_seven, ByteOpcode.constrain_Range, hval14] at h_bc
      -- `h_bc : (Main[22] * 4⁻¹).val < 2 ^ 14`; `2 ^ 14 = 16384`.
      simpa using h_bc
  · -- Backward: structural spec → envelopes.
    rintro ⟨h_cpu, h_addop_jump_spec, h_addop_ret_spec, h_jtr, h_m25, h_m29,
            _h_or, h_align⟩
    -- Re-extract bounds + op_a_0 binarity from JTypeReader Spec.
    have h_jtr_copy := h_jtr
    obtain ⟨_, h_prog_disj, _, _, _, _, _⟩ := h_jtr
    have h_prog := h_prog_disj.resolve_left h_one_ne_zero
    simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
    obtain ⟨_, _, ⟨h_ob0, h_ob1, h_ob2, h_ob3⟩, _, h_op_a_0_bin, _, _, _,
            h_pc0_mod, h_pc0_lt_raw, h_pc1_lt_raw, h_pc2_lt_raw⟩ := h_prog
    have h_isU64_op_b : Word.isU64
        #v[Main[14], Main[15], Main[16], Main[17]] :=
      Word.isU64_of_cases (lt65k _ h_ob0) (lt65k _ h_ob1)
                          (lt65k _ h_ob2) (lt65k _ h_ob3)
    have h_pc0_lt := lt65k _ h_pc0_lt_raw
    have h_pc1_lt := lt65k _ h_pc1_lt_raw
    have h_pc2_lt := lt65k _ h_pc2_lt_raw
    have h_isU64_pc : Word.isU64
        #v[Main[3], Main[4], Main[5], (0 : ZMod p)] :=
      Word.isU64_of_cases h_pc0_lt h_pc1_lt h_pc2_lt (by simp [ZMod.val_zero])
    -- Jump AddOp envelope (gate 1).
    have h_addop_jump : (_root_.AddOperation.constraints (F := ZMod p)
          #v[Main[3], Main[4], Main[5], 0]
          #v[Main[14], Main[15], Main[16], Main[17]]
          { value := #v[Main[22], Main[23], Main[24], Main[25]] } 1).allHold :=
      (AddOperation.iff_sp1_full h_isU64_pc h_isU64_op_b).mpr
        (h_addop_jump_spec rfl)
    -- Return AddOp envelope (gate 1 - Main[13]); case-split on Main[13] ∈ {0,1}.
    have h_addop_ret : (_root_.AddOperation.constraints (F := ZMod p)
          #v[Main[3], Main[4], Main[5], 0]
          #v[4, 0, 0, 0]
          { value := #v[Main[26], Main[27], Main[28], Main[29]] }
          ((1 : ZMod p) - Main[13])).allHold := by
      rcases h_op_a_0_bin with h0 | h1
      · rw [h0, sub_zero]
        exact (AddOperation.iff_sp1_full h_isU64_pc Word.four_isU64).mpr
          (h_addop_ret_spec (by rw [h0]; ring))
      · rw [h1, show (1 : ZMod p) - 1 = 0 from by ring]
        simp [_root_.AddOperation.constraints, SP1ConstraintList.allHold,
          List.Forall, SP1Constraint.toProp]
    -- Reconstruct the alignment byte send from the Range14 consequence.
    have h_align_byte : (1 : ZMod p) ≠ 0 →
        (ByteOpcode.ofNat 6).constrain (Main[22] * (4 : ZMod p)⁻¹) 14 0 := by
      intro _
      have hlt := h_align rfl
      have hval14 : (14 : ZMod p).val = 14 := by
        rw [show (14 : ZMod p) = ((14 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast,
            Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      simp only [ByteOpcode.ofNat_seven, ByteOpcode.constrain_Range, hval14]
      -- goal: `(Main[22] * 4⁻¹).val < 2 ^ 14`; `2 ^ 14 = 16384`.
      simpa using hlt
    exact ⟨h_cpu, h_addop_jump, h_addop_ret, h_jtr_copy, h_m25, h_m29,
           h_align_byte, by ring⟩

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
