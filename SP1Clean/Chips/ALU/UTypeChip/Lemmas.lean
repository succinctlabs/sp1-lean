import SP1Clean.Chips.ALU.UTypeChip.Cols
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader
import SP1Clean.Operations.AddOperation
import SP1Chips.UType.Common

/-! # `UTypeChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.UType.constraints Main).allHold`
  under `is_real = 1` to the structural conjunction
  (`CPUState.Gated.Assertion.Spec`, `AddOp.Assertion.Spec`,
  `JTypeReader.Gated.Assertion.Spec`, plus four scalar gates) over
  `fromMain Main`. This mirrors the new canonical (a) `FormalSpec` shape.
  Used downstream by `SailBridge.lean` to reconstruct SP1's `allHold` from
  the structural conjuncts of `FormalSpec`.

The AddOp clause is bridged through `AddOperation.iff_sp1_full` (which
needs `Word.isU64` of both operands). The operand bound on `op_b_imm`
comes from the `JTypeReader.Gated.Assertion.Spec` conjunct; the addend
bound on `#v[Main[22], Main[23], Main[24], 0]` is derived locally from
the three addend gates `Main[22+i] - Main[29] * Main[3+i] = 0` plus the
`Main[29]` (is_auipc) binary gate plus the pc-limb bounds (also from
`JTypeReader.Gated.Assertion.Spec`). The AddOp gate `is_real - op_a_0`
collapses to `1 - Main[13]` under `Main[30] = 1`; a case-split on
`Main[13] ∈ {0, 1}` (from JTypeReader's `op_a_0` binary clause) handles
both the gate-active (`Main[13] = 0 → gate = 1`) and gate-padding
(`Main[13] = 1 → gate = 0`, AddOp's RawSpec is trivially satisfiable)
branches symmetrically. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.UType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. The precondition
captures `fromMain`'s aliasing of `is_trusted := Main[30] = is_real` (which
matches the constraint compiler's emission — Main[30] is both `is_real` and
`is_trusted` because the chip is UserMode). -/
lemma fromMain_toMain (cols : UTypeCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, addend, add_result, is_auipc, is_real, adapter_cols⟩
  rcases state with ⟨clk_high, clk_16_24, clk_0_16, pc⟩
  rcases adapter with ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩
  rcases op_a_memory with ⟨prev_value, ts⟩
  rcases ts with ⟨prev_low, diff_low_limb⟩
  rcases adapter_cols with ⟨is_trusted⟩
  have : is_trusted = is_real := by simpa using h_trusted
  simp only [this, fromMain, toMain, UTypeCols.mk.injEq, CPUState.mk.injEq,
    JTypeReader.mk.injEq, MemoryAccessInSharedCols.mk.injEq,
    MemoryAccessInShardTimestamp.mk.injEq,
    UserModeReaderCols.mk.injEq, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, and_self, true_and,
    and_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply Vector.ext; intro i hi; interval_cases i <;> rfl)

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full UType
-- constraint list (CPUState ++ AddOperation ++ JTypeReader ++ 7 trailing
-- assertZeros), bridges the AddOp piece through `iff_sp1_full` under a
-- `Main[13] ∈ {0, 1}` case-split, and applies the
-- `CPUState.Gated.Assertion.Spec_iff_sp1` /
-- `JTypeReader.Gated.Assertion.Spec_iff_sp1` rewrites.
/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`UType.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `AddOp.Assertion.Spec` (gated by
`1 - Main[13]`, semantic-only form: `gate = 1 → isU64 result ∧ BV64 sum`),
`JTypeReader.Gated.Assertion.Spec` (with both `is_real` and `is_trusted`
instantiated to `Main[30] = 1`), and four scalar gates over `fromMain Main`,
under `is_real = Main[30] = 1`. The free chip-level
`Main[30] * (Main[30] - 1) = 0` and `(Main[30] - 1) * Main[13] = 0` gates
are absorbed into the two `Gated.Assertion.Spec` conjuncts (into the
CPUState's binary gate and into the JTypeReader's `ProgramSpec`
`op_a_0` binary clause respectively, both under `Main[30] = 1`). -/
theorem allHold_iff_structural
    (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1) :
    (_root_.UType.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
           ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] },
            #v[Main[3] + 4, Main[4], Main[5]], 8, Main[30]⟩ ∧
       SP1Clean.AddOp.Assertion.Spec
           ⟨#v[Main[22], Main[23], Main[24], 0],
            #v[Main[14], Main[15], Main[16], Main[17]],
            #v[Main[25], Main[26], Main[27], Main[28]],
            1 - Main[13]⟩ ∧
       SP1Clean.JTypeReader.Gated.Assertion.Spec
           ⟨Main[0], Main[2] + Main[1] * 65536,
            Main[29] * 48 + (1 - Main[29]) * 49,
            #v[Main[3], Main[4], Main[5]],
            #v[Main[25], Main[26], Main[27], Main[28]],
            { op_a := Main[6],
              op_a_memory :=
                { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                  access_timestamp :=
                    { prev_low := Main[11], diff_low_limb := Main[12] } },
              op_a_0 := Main[13],
              op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
              op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] },
            1, 1⟩ ∧
       Main[29] * (Main[29] - 1) = 0 ∧
       Main[22] - Main[29] * Main[3] = 0 ∧
       Main[23] - Main[29] * Main[4] = 0 ∧
       Main[24] - Main[29] * Main[5] = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Step 1: expand UType.constraints into its 3 sub-`.allHold` pieces +
  -- 7 chip-level trailing scalar gates. Uses an inline `show` block (rather
  -- than `UType.allHold_constraints_iff` directly) so each sub-clause is
  -- in `.allHold` (not `List.Forall SP1Constraint.toProp`) form — needed
  -- for the `_iff_sp1` rewrites below to fire syntactically.
  rw [show (_root_.UType.constraints Main).allHold ↔
        ((_root_.CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[30]).allHold ∧
          (_root_.AddOperation.constraints (F := ZMod p)
              #v[Main[22], Main[23], Main[24], 0]
              #v[Main[14], Main[15], Main[16], Main[17]]
              { value := #v[Main[25], Main[26], Main[27], Main[28]] }
              (Main[30] - Main[13])).allHold ∧
          (_root_.JTypeReader.constraints (F := ZMod p)
              Main[0] (Main[2] + Main[1] * 65536)
              #v[Main[3], Main[4], Main[5]]
              (Main[29] * 48 + (1 - Main[29]) * 49)
              #v[Main[25], Main[26], Main[27], Main[28]]
              { op_a := Main[6],
                op_a_memory :=
                  { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                    access_timestamp :=
                      { prev_low := Main[11], diff_low_limb := Main[12] } },
                op_a_0 := Main[13],
                op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
                op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] }
              Main[30] Main[30]).allHold ∧
          (Main[30] * (Main[30] - 1) = 0 ∧
           Main[29] * (Main[29] - 1) = 0 ∧
           Main[22] - (Main[29] * Main[3] + (1 - Main[29]) * 0) = 0 ∧
           Main[23] - (Main[29] * Main[4] + (1 - Main[29]) * 0) = 0 ∧
           Main[24] - (Main[29] * Main[5] + (1 - Main[29]) * 0) = 0 ∧
           (Main[30] - 1) * Main[13] = 0)) from by
      simp [_root_.UType.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  -- Step 2: apply h_is_real (Main[30] = 1) everywhere on the RHS that uses
  -- `Main[30]` as a multiplicity/flag (but keep the literal `Main[30]` in
  -- the CPUState/JTypeReader Spec targets so the conclusion is shape-matched
  -- against the literal `Main[30]` in the iff RHS the user expects). We
  -- only collapse `Main[30] - Main[13] = 1 - Main[13]` for the AddOp piece
  -- and the 6 trailing gates; the Gated.Spec rewrites already accept
  -- `Main[30] = 1` shape via `Spec_iff_sp1`'s pinned form.
  rw [show Main[30] - Main[13] = (1 : ZMod p) - Main[13] from by rw [h_is_real],
      h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.JTypeReader.Gated.Assertion.Spec_iff_sp1]
  -- Step 2.5: push_cast cleans the `↑1` / `↑48` literal casts that the
  -- generated `UType.constraints` introduces (its `F.coe_F` calls leave
  -- residual `Nat.cast` on the literals). After this, the AddOp gate and
  -- the addend gates are in their canonical `(1 - Main[13])` / `Main[k] -
  -- (Main[29] * Main[i] + (1 - Main[29]) * 0) = 0` form.
  push_cast
  -- Local helpers used in both directions of the iff.
  haveI h65k : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have lt65k : ∀ (x : ZMod p), x < (65536 : ZMod p) → x.val < 65536 :=
    fun x h => by have : x.val < (65536 : ZMod p).val := h; rwa [h65k] at this
  have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
  -- Step 4: bridge the AddOp `.allHold` piece (at multiplicity `1 - Main[13]`)
  -- to `AddOp.Assertion.Spec` form. Both directions of the iff are handled
  -- symmetrically below.
  -- LHS structure (9 conjuncts, after `rw [h_is_real]` collapsed Main[30] → 1):
  --   cpu_spec ∧ addop_allHold ∧ jtr_spec ∧ 1*(1-1)=0 ∧
  --   isa_bin ∧ addend0_with_trailing_zero ∧ addend1_... ∧ addend2_... ∧
  --   (1-1)*Main[13]=0
  -- where each addend gate carries the residual `(1 - Main[29]) * 0` term.
  -- RHS structure (7 conjuncts):
  --   cpu_spec ∧ addop_spec ∧ jtr_spec ∧ isa_bin ∧ addend0 ∧ addend1 ∧ addend2
  refine ⟨?_, ?_⟩
  · -- Forward direction: allHold → structural spec.
    rintro ⟨h_cpu, h_addop, h_jtr, _h_triv30, h_isa_bin, h_addend0_raw,
            h_addend1_raw, h_addend2_raw, _h_triv13⟩
    -- Normalize the addend gates by stripping `(1 - Main[29]) * 0 = 0`.
    have h_addend0 : Main[22] - Main[29] * Main[3] = 0 := by
      linear_combination h_addend0_raw
    have h_addend1 : Main[23] - Main[29] * Main[4] = 0 := by
      linear_combination h_addend1_raw
    have h_addend2 : Main[24] - Main[29] * Main[5] = 0 := by
      linear_combination h_addend2_raw
    -- Extract isU64 op_b_imm, Main[13] binary, pc bounds from h_jtr.
    -- Save a copy of h_jtr first since destructuring it consumes the
    -- hypothesis (we need it for the JTypeReader conjunct in the output).
    have h_jtr_copy := h_jtr
    obtain ⟨_, h_prog_disj, _, _, _, _, _⟩ := h_jtr
    have h_prog := h_prog_disj.resolve_left h_one_ne_zero
    simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
    obtain ⟨_, _, ⟨h_ob0, h_ob1, h_ob2, h_ob3⟩, _, _h_op_a_0_bin, _, _, _,
            _, h_pc0_lt_raw, h_pc1_lt_raw, h_pc2_lt_raw⟩ := h_prog
    have h_isU64_op_b : Word.isU64
        #v[Main[14], Main[15], Main[16], Main[17]] :=
      Word.isU64_of_cases (lt65k _ h_ob0) (lt65k _ h_ob1)
                          (lt65k _ h_ob2) (lt65k _ h_ob3)
    have h_pc0_lt := lt65k _ h_pc0_lt_raw
    have h_pc1_lt := lt65k _ h_pc1_lt_raw
    have h_pc2_lt := lt65k _ h_pc2_lt_raw
    -- Derive isU64 addend.
    have h_isU64_addend : Word.isU64
        #v[Main[22], Main[23], Main[24], (0 : ZMod p)] := by
      rcases mul_eq_zero.mp h_isa_bin with h0 | h1
      · -- LUI: Main[29] = 0, addend = 0 word.
        have h22 : Main[22] = 0 := by
          have := h_addend0; rw [h0] at this; linear_combination this
        have h23 : Main[23] = 0 := by
          have := h_addend1; rw [h0] at this; linear_combination this
        have h24 : Main[24] = 0 := by
          have := h_addend2; rw [h0] at this; linear_combination this
        rw [show #v[Main[22], Main[23], Main[24], (0 : ZMod p)]
              = #v[(0 : ZMod p), 0, 0, 0] from by rw [h22, h23, h24]]
        exact Word.isU64_of_cases (by simp [ZMod.val_zero])
              (by simp [ZMod.val_zero]) (by simp [ZMod.val_zero])
              (by simp [ZMod.val_zero])
      · -- AUIPC: Main[29] = 1, addend = pc.
        have h29 : Main[29] = 1 := by linear_combination h1
        have h22 : Main[22] = Main[3] := by
          have := h_addend0; rw [h29] at this; linear_combination this
        have h23 : Main[23] = Main[4] := by
          have := h_addend1; rw [h29] at this; linear_combination this
        have h24 : Main[24] = Main[5] := by
          have := h_addend2; rw [h29] at this; linear_combination this
        rw [show #v[Main[22], Main[23], Main[24], (0 : ZMod p)]
              = #v[Main[3], Main[4], Main[5], (0 : ZMod p)] from
            by rw [h22, h23, h24]]
        exact Word.isU64_of_cases h_pc0_lt h_pc1_lt h_pc2_lt
              (by simp [ZMod.val_zero])
    refine ⟨h_cpu, ?_, h_jtr_copy, h_isa_bin, h_addend0, h_addend1, h_addend2⟩
    -- Build AddOp.Assertion.Spec ⟨..., 1 - Main[13]⟩: `gate = 1 → isU64 result ∧ BV64 sum`.
    intro h_gate
    have h13_zero : Main[13] = 0 := by linear_combination -h_gate
    -- The original `h_addop` has multiplicity `(1 - Main[13])`; substituting
    -- `Main[13] = 0` reduces it to `1`. Use `rw` rather than the cast bridge
    -- since the original `h_addop`'s `1` and the iff_sp1_full's `1` already
    -- agree as `OfNat.ofNat 1 : ZMod p`.
    have h_addop' : (_root_.AddOperation.constraints (F := ZMod p)
          #v[Main[22], Main[23], Main[24], 0]
          #v[Main[14], Main[15], Main[16], Main[17]]
          { value := #v[Main[25], Main[26], Main[27], Main[28]] } 1).allHold := by
      have h_eq : (1 : ZMod p) - Main[13] = 1 := by rw [h13_zero]; ring
      have := h_addop
      rw [h13_zero, sub_zero] at this
      exact this
    exact (AddOperation.iff_sp1_full h_isU64_addend h_isU64_op_b).mp h_addop'
  · -- Backward direction: structural spec → allHold.
    rintro ⟨h_cpu, h_addop_spec, h_jtr, h_isa_bin, h_addend0, h_addend1,
            h_addend2⟩
    -- Re-extract bounds + op_a_0 binary from h_jtr (mirror of forward arm).
    have h_jtr_copy := h_jtr
    obtain ⟨_, h_prog_disj, _, _, _, _, _⟩ := h_jtr
    have h_prog := h_prog_disj.resolve_left h_one_ne_zero
    simp only [SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
    obtain ⟨_, _, ⟨h_ob0, h_ob1, h_ob2, h_ob3⟩, _, h_op_a_0_bin, _, _, _,
            _, h_pc0_lt_raw, h_pc1_lt_raw, h_pc2_lt_raw⟩ := h_prog
    have h_isU64_op_b : Word.isU64
        #v[Main[14], Main[15], Main[16], Main[17]] :=
      Word.isU64_of_cases (lt65k _ h_ob0) (lt65k _ h_ob1)
                          (lt65k _ h_ob2) (lt65k _ h_ob3)
    have h_pc0_lt := lt65k _ h_pc0_lt_raw
    have h_pc1_lt := lt65k _ h_pc1_lt_raw
    have h_pc2_lt := lt65k _ h_pc2_lt_raw
    have h_isU64_addend : Word.isU64
        #v[Main[22], Main[23], Main[24], (0 : ZMod p)] := by
      rcases mul_eq_zero.mp h_isa_bin with h0 | h1
      · have h22 : Main[22] = 0 := by
          have := h_addend0; rw [h0] at this; linear_combination this
        have h23 : Main[23] = 0 := by
          have := h_addend1; rw [h0] at this; linear_combination this
        have h24 : Main[24] = 0 := by
          have := h_addend2; rw [h0] at this; linear_combination this
        rw [show #v[Main[22], Main[23], Main[24], (0 : ZMod p)]
              = #v[(0 : ZMod p), 0, 0, 0] from by rw [h22, h23, h24]]
        exact Word.isU64_of_cases (by simp [ZMod.val_zero])
              (by simp [ZMod.val_zero]) (by simp [ZMod.val_zero])
              (by simp [ZMod.val_zero])
      · have h29 : Main[29] = 1 := by linear_combination h1
        have h22 : Main[22] = Main[3] := by
          have := h_addend0; rw [h29] at this; linear_combination this
        have h23 : Main[23] = Main[4] := by
          have := h_addend1; rw [h29] at this; linear_combination this
        have h24 : Main[24] = Main[5] := by
          have := h_addend2; rw [h29] at this; linear_combination this
        rw [show #v[Main[22], Main[23], Main[24], (0 : ZMod p)]
              = #v[Main[3], Main[4], Main[5], (0 : ZMod p)] from
            by rw [h22, h23, h24]]
        exact Word.isU64_of_cases h_pc0_lt h_pc1_lt h_pc2_lt
              (by simp [ZMod.val_zero])
    -- Case-split on Main[13] ∈ {0, 1} to bridge AddOp.Spec → allHold.
    -- The chip-level constraints use the gate form `(1 : ZMod p) - Main[13]`;
    -- after `push_cast` collapsed the literal `↑1` from `Main[30] - Main[13]`,
    -- the goal carries `(1 - Main[13])` exactly. We assemble `h_addop_allHold`
    -- in that shape.
    have h_addop_allHold : (_root_.AddOperation.constraints (F := ZMod p)
          #v[Main[22], Main[23], Main[24], 0]
          #v[Main[14], Main[15], Main[16], Main[17]]
          { value := #v[Main[25], Main[26], Main[27], Main[28]] }
          ((1 : ZMod p) - Main[13])).allHold := by
      rcases h_op_a_0_bin with h0 | h1
      · -- Main[13] = 0: gate = 1, use iff_sp1_full.mpr.
        rw [h0, sub_zero]
        exact (AddOperation.iff_sp1_full h_isU64_addend h_isU64_op_b).mpr
          (h_addop_spec (by rw [h0]; ring))
      · -- Main[13] = 1: gate = 0, allHold is trivially satisfied.
        rw [h1, show (1 : ZMod p) - 1 = 0 from by ring]
        simp [_root_.AddOperation.constraints, SP1ConstraintList.allHold,
          List.Forall, SP1Constraint.toProp]
    -- Build LHS (9-conjunct) from h_addop_allHold + remaining gates.
    refine ⟨h_cpu, ?_, h_jtr_copy, by ring, h_isa_bin,
            ?_, ?_, ?_, by ring⟩
    · -- The goal's gate is `↑1 - Main[13]` from elaboration; bridge from
      -- our `(1 : ZMod p) - Main[13]` form via push_cast.
      have := h_addop_allHold
      push_cast at this ⊢
      exact this
    · linear_combination h_addend0
    · linear_combination h_addend1
    · linear_combination h_addend2

end SP1Clean.UType
