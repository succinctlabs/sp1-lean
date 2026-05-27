import SP1Clean.Chips.ALU.AddiChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Reader.ITypeReader
import SP1Chips.Addi.Common

/-! # `AddiChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real` (carried as the chip's
  `Assumptions` in `Circuit.lean`).
- `allHold_iff_structural` — bridges `(_root_.Addi.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `CPUState.Gated.Assertion.Spec`,
  `ITypeReader.Gated.Assertion.Spec`, the `op_a_0` scalar gate, and the
  semantic RV64-addi conjunct (`Word.isU64` of the result + the BitVec
  equation with sign-extended 12-bit immediate). The byte-carry
  decomposition that SP1's `AddOperation` threads internally is not
  exposed in the RHS — it's reconstructed from the BitVec equation, the
  `isU64` bounds of `op_b`/`op_c_imm` (available from
  `ITypeReader.Gated.Spec`'s `RegisterAccess.Spec` and `ProgramSpec` sub-
  conjuncts), and the sign-extension identity (from
  `ProgramSpec.trusted_instr` for the ADDI opcode) via
  `AddOperation.iff_sp1_full`. Used downstream by `SailBridge.lean` to
  reconstruct `(Addi.constraints (toMain cols)).allHold` from the
  structural conjuncts of `FormalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[29] = is_real` (which
matches the constraint compiler's emission — Main[29] is both `is_real` and
`is_trusted`). Recursive `ext` through `@[ext]`-marked sub-structures plus
`Vector.ext` reduces to per-element equations closed by `rfl` (each
`(toMain cols)[k]` reduces by `@[reducible]` to the matching `cols`
projection) or by the precondition on the lone `adapter_cols.is_trusted` leaf. -/
lemma fromMain_toMain (cols : AddiCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, op_a_write_value, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, AddiCols.ext_iff, CPUState.ext_iff,
    ITypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Addi.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `ITypeReader.Gated.Assertion.Spec`,
`Main[13] = 0` (the chip-level `op_a_0` zero gate), and the semantic
RV64-addi conjunct (`isU64` of the result + the BitVec equation), under
`is_real = Main[29] = 1`. The byte-carry decomposition that SP1's
`AddOperation` threads internally is *not* exposed in the RHS — it's
reconstructed from the BitVec equation, the `isU64` bounds of `op_b`
(from `RegisterAccess.Spec`) and `op_c_imm` (from `ProgramSpec`'s op_c
range conjunct), and the sign-extension identity (from
`ProgramSpec.trusted_instr` for ADDI) via `AddOperation.iff_sp1_full`.
Used inside the Sail clause's external bridge
(`SailBridge.sail_correct_of_formalSpec`) to construct an `allHold` from
the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 30) (h_is_real : Main[29] = 1) :
    (_root_.Addi.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[29]⟩ ∧
       SP1Clean.ITypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 1,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[25], Main[26], Main[27], Main[28]],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13], op_b := Main[14],
             op_b_memory :=
               { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                 access_timestamp :=
                   { prev_low := Main[19], diff_low_limb := Main[20] } },
             op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] },
           Main[29], Main[29]⟩ ∧
       Main[13] = 0 ∧
       Word.isU64 #v[Main[25], Main[26], Main[27], Main[28]] ∧
       Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] =
         RV64.addi (BitVec.ofNat 12 Main[21].val)
                   (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Addi.allHold_constraints_iff Main, h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.ITypeReader.Gated.Assertion.Spec_iff_sp1]
  -- After the rewrite, LHS is:
  --   AddOperation.allHold (op_b op_c_imm result 1) ∧
  --   CPUState.Gated.Spec ∧ ITypeReader.Gated.Spec ∧ 1*(1-1)=0 ∧ Main[13]=0
  -- We use `iff_sp1_full` to swap `AddOperation.allHold` for `(isU64 ∧ bv_eq)`,
  -- pulling `isU64 op_b` from RegisterAccess.Spec and `isU64 op_c_imm` from
  -- ProgramSpec's op_c range conjunct; the sign-extension identity that
  -- bridges `exec_RTYPE .ADD` to `RV64.addi` comes from `trusted_instr` for
  -- ADDI (opcode = 1).
  have h65 : (65536 : ZMod p).val = 65536 := by
    have hp : 2 ^ 17 < p := Fact.out
    rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · -- Forward: allHold → structural conjuncts + (isU64 ∧ RV64.addi eq).
    -- After `rw [h_is_real]`, the gating disjunctions in `ProgramGated.Spec`
    -- and the op_b `RegisterAccess.Spec` resolve via `one_ne_zero`.
    rintro ⟨h_op, h_cpu, h_itr, _, h_op_a_0⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_itr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_ps := h_itr.2.1.resolve_left h_one_ne_zero
    obtain ⟨h_ti, _h_op_a, _h_op_b, ⟨h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt⟩,
            _, _, _, _, _, _, _, _⟩ := h_ps
    have h_isU64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] :=
      Word.isU64_of_cases
        (by have : Main[21].val < (65536 : ZMod p).val := h_c0_lt; rwa [h65] at this)
        (by have : Main[22].val < (65536 : ZMod p).val := h_c1_lt; rwa [h65] at this)
        (by have : Main[23].val < (65536 : ZMod p).val := h_c2_lt; rwa [h65] at this)
        (by have : Main[24].val < (65536 : ZMod p).val := h_c3_lt; rwa [h65] at this)
    have h_signExt : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp only [Opcode.trusted_instr, Opcode.ofNat, ZMod.val_one,
                 i_type_constraints, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ] at h_ti
      exact h_ti.2.2
    have ⟨h_isU64_v, h_bv⟩ :=
      (AddOperation.iff_sp1_full h_isU64_b h_isU64_c).mp h_op
    refine ⟨h_cpu, h_itr, h_op_a_0, h_isU64_v, ?_⟩
    -- `h_bv : v.toBitVec64 = execute_RTYPE_pure_w op_b op_c_imm .ADD`
    --       = op_b.toBitVec64 + op_c_imm.toBitVec64.
    -- Goal: `v.toBitVec64 = RV64.addi (signExt12 Main[21]) op_b.toBitVec64`
    --     = `op_b.toBitVec64 + signExtend64 (BitVec.ofNat 12 Main[21].val)`.
    -- Bridge via `h_signExt` (op_c_imm.toBitVec64 = signExtend64 …).
    simp only [RV64.addi]
    rw [h_bv]
    simp only [execute_RTYPE_pure_w]
    rw [h_signExt]
    rfl
  · -- Backward: structural conjuncts + (isU64 ∧ RV64.addi eq) → allHold.
    rintro ⟨h_cpu, h_itr, h_op_a_0, h_isU64_v, h_bv⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_itr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_ps := h_itr.2.1.resolve_left h_one_ne_zero
    obtain ⟨h_ti, _h_op_a, _h_op_b, ⟨h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt⟩,
            _, _, _, _, _, _, _, _⟩ := h_ps
    have h_isU64_c : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] :=
      Word.isU64_of_cases
        (by have : Main[21].val < (65536 : ZMod p).val := h_c0_lt; rwa [h65] at this)
        (by have : Main[22].val < (65536 : ZMod p).val := h_c1_lt; rwa [h65] at this)
        (by have : Main[23].val < (65536 : ZMod p).val := h_c2_lt; rwa [h65] at this)
        (by have : Main[24].val < (65536 : ZMod p).val := h_c3_lt; rwa [h65] at this)
    have h_signExt : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
      simp only [Opcode.trusted_instr, Opcode.ofNat, ZMod.val_one,
                 i_type_constraints, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ] at h_ti
      exact h_ti.2.2
    have h_bv' : Word.toBitVec64 #v[Main[25], Main[26], Main[27], Main[28]] =
        execute_RTYPE_pure_w #v[Main[15], Main[16], Main[17], Main[18]]
                             #v[Main[21], Main[22], Main[23], Main[24]] .ADD := by
      simp only [RV64.addi] at h_bv
      simp only [execute_RTYPE_pure_w]
      rw [h_bv, h_signExt]
      rfl
    have h_op :=
      (AddOperation.iff_sp1_full h_isU64_b h_isU64_c).mpr ⟨h_isU64_v, h_bv'⟩
    refine ⟨h_op, h_cpu, h_itr, ?_, h_op_a_0⟩
    ring

/-- Under `is_real = 1`, extract from `ITypeReader.Gated.Assertion.Spec`'s
`ProgramSpec` clause both (a) the `Word.isU64` bound on `op_c_imm`
(reconstructed from the four `< 65536` byte bounds in the ProgramSpec
op_c range conjunct) and (b) the sign-extension identity
`op_c_imm.toBitVec64 = signExtend 64 (BitVec.ofNat 12 op_c_imm[0].val)`
(from `trusted_instr` for the ADDI opcode = 1).

Shared by `AddiChip`'s `formalSpec_of_subcircuit_specs` /
`subcircuit_specs_of_formalSpec` midpoints — both directions need the
same isU64+signExt bridge to convert between `AddOp.Spec`'s natural
`a + b` BitVec form and `FormalSpec`'s `RV64.addi (signExt12 imm) b` form. -/
lemma isU64_op_c_imm_and_signExt_of_itr_spec
    (cols : AddiCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_itr : SP1Clean.ITypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536, 1,
         cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_real, cols.adapter_cols.is_trusted⟩) :
    Word.isU64 cols.adapter.op_c_imm ∧
    Word.toBitVec64 cols.adapter.op_c_imm =
      BitVec.signExtend 64 (BitVec.ofNat 12 cols.adapter.op_c_imm[0].val) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_trusted_one : cols.adapter_cols.is_trusted = 1 := h_trusted.trans h_is_real
  have h_t_ne_zero : cols.adapter_cols.is_trusted ≠ 0 := by
    rw [h_trusted_one]; exact one_ne_zero
  have h_ps := h_itr.2.1.resolve_left h_t_ne_zero
  obtain ⟨h_ti, _h_op_a, _h_op_b, ⟨h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt⟩,
          _, _, _, _, _, _, _, _⟩ := h_ps
  have h65 : (65536 : ZMod p).val = 65536 := by
    have hp : 2 ^ 17 < p := Fact.out
    rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h_isU64_c : Word.isU64 cols.adapter.op_c_imm :=
    Word.isU64_of_cases
      (by have : cols.adapter.op_c_imm[0].val < (65536 : ZMod p).val := h_c0_lt
          rwa [h65] at this)
      (by have : cols.adapter.op_c_imm[1].val < (65536 : ZMod p).val := h_c1_lt
          rwa [h65] at this)
      (by have : cols.adapter.op_c_imm[2].val < (65536 : ZMod p).val := h_c2_lt
          rwa [h65] at this)
      (by have : cols.adapter.op_c_imm[3].val < (65536 : ZMod p).val := h_c3_lt
          rwa [h65] at this)
  have h_signExt : Word.toBitVec64 cols.adapter.op_c_imm =
      BitVec.signExtend 64 (BitVec.ofNat 12 cols.adapter.op_c_imm[0].val) := by
    simp only [Opcode.trusted_instr, Opcode.ofNat, ZMod.val_one,
               i_type_constraints, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ] at h_ti
    -- `h_ti.2.2` after simp gives the sign-extension equation, but its
    -- `op_c_imm` projection may need a Vector destructure to align with
    -- the goal's `cols.adapter.op_c_imm` form.
    have h_eq := h_ti.2.2
    convert h_eq using 2
    apply Vector.ext
    intro i hi
    interval_cases i <;> rfl
  exact ⟨h_isU64_c, h_signExt⟩

/-! ## Chip-level FormalSpec ↔ sub-circuit Specs

The two lemmas below name the *stable midpoint* of `AddiChip`'s
`soundness` / `completeness` proofs. AddiChip differs from
AddChip/SubChip in two ways: (a) `Assumptions` is just the TrustMode
marker `is_trusted = is_real` (no `is_real = 1` upfront), so the
semantic implication's `is_real = 1` hypothesis is introduced *inside*
the `(is_real = 1 → …)` clause; (b) the BV64 equation in `FormalSpec`
uses `RV64.addi (signExt12 imm) op_b` while `AddOp.Spec`'s natural form
is plain `op_b + op_c_imm`, so the bridge in both directions goes
through `isU64_op_c_imm_and_signExt_of_itr_spec` above. -/

/-- **Forward** (soundness midpoint): assemble the chip-level
`FormalSpec` from the per-sub-circuit Specs returned by `h_holds`. The
`AddOp` hypothesis is kept in its `Assumptions → Spec` function form —
the literal shape of `h_holds.1` after `circuit_proof_start`'s
`subcircuit_norm` unfolding — and discharged internally using `h_trusted`
+ the `is_real = 1` antecedent of FormalSpec's last conjunct plus the
`isU64_op_b` / `(isU64 op_c_imm, signExt)` extraction from `h_itr`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : AddiCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_addop : SP1Clean.AddOp.Assertion.Assumptions
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
         cols.op_a_write_value, cols.is_real⟩ →
      SP1Clean.AddOp.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
         cols.op_a_write_value, cols.is_real⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_real⟩)
    (h_itr : SP1Clean.ITypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536, 1,
         cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_real, cols.adapter_cols.is_trusted⟩)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    FormalSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  refine ⟨h_cpu, h_itr, h_op_a_0, fun h_is_real_eq => ?_⟩
  have h_isU64_b :=
    SP1Clean.ITypeReader.Gated.Assertion.isU64_op_b_of_spec h_is_real_eq h_itr
  obtain ⟨h_isU64_c, h_signExt⟩ :=
    isU64_op_c_imm_and_signExt_of_itr_spec cols h_trusted h_is_real_eq h_itr
  have ⟨h_isU64_v, h_bv⟩ :=
    h_addop ⟨Or.inr h_is_real_eq, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩ h_is_real_eq
  refine ⟨h_isU64_v, ?_⟩
  -- `h_bv : result.toBitVec64 = op_b.toBitVec64 + op_c_imm.toBitVec64`
  -- Goal: `result.toBitVec64 = RV64.addi (signExt12 imm[0]) op_b.toBitVec64`
  simp only [RV64.addi]
  rw [h_bv, h_signExt]
  rfl

/-- **Backward** (completeness midpoint): peel the chip-level
`FormalSpec` apart into per-sub-circuit `Spec`s. The `AddOp` conjunct
is returned in **paired** form (`Assumptions ∧ Spec`) since AddiChip's
chip-level `Assumptions` lacks the `is_real = 1` clause that lets
AddChip return just the post-discharge `Spec`; the binary gate is
extracted from `h_itr.1` and the operand bounds from `h_itr`'s
RegisterAccess + ProgramSpec sub-conjuncts via the helpers above. -/
lemma subcircuit_specs_of_formalSpec
    (cols : AddiCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_spec : FormalSpec cols) :
    (SP1Clean.AddOp.Assertion.Assumptions
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
         cols.op_a_write_value, cols.is_real⟩ ∧
      SP1Clean.AddOp.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm,
         cols.op_a_write_value, cols.is_real⟩) ∧
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_real⟩ ∧
    SP1Clean.ITypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536, 1,
         cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
    cols.adapter.op_a_0 = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_itr, h_op_a_0, h_bv⟩ := h_spec
  refine ⟨⟨⟨?_, fun h_is_real_eq => ?_⟩, fun h_is_real_eq => ?_⟩,
          h_cpu, h_itr, h_op_a_0⟩
  · -- AddOp Assumptions: is_real ∈ {0, 1} via h_itr's binarity gate
    obtain ⟨h_ir_bin, _⟩ := h_itr
    rcases mul_eq_zero.mp h_ir_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · -- AddOp Assumptions: is_real = 1 → isU64 op_b ∧ isU64 op_c_imm
    have h_isU64_b :=
      SP1Clean.ITypeReader.Gated.Assertion.isU64_op_b_of_spec h_is_real_eq h_itr
    obtain ⟨h_isU64_c, _⟩ :=
      isU64_op_c_imm_and_signExt_of_itr_spec cols h_trusted h_is_real_eq h_itr
    exact ⟨h_isU64_b, h_isU64_c⟩
  · -- AddOp.Spec: is_real = 1 → (isU64 result ∧ result.toBitVec64 = op_b + op_c_imm)
    obtain ⟨_, h_signExt⟩ :=
      isU64_op_c_imm_and_signExt_of_itr_spec cols h_trusted h_is_real_eq h_itr
    have ⟨h_isU64_v, h_bv'⟩ := h_bv h_is_real_eq
    refine ⟨h_isU64_v, ?_⟩
    -- h_bv': result.toBitVec64 = RV64.addi (signExt12 imm[0]) op_b.toBitVec64
    -- Goal: result.toBitVec64 = op_b.toBitVec64 + op_c_imm.toBitVec64
    rw [h_bv']
    simp only [RV64.addi]
    rw [h_signExt]
    rfl

end SP1Clean.Addi
