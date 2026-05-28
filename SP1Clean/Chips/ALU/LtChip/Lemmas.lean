import SP1Clean.Chips.ALU.LtChip.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common

/-! # `LtChip` cols-level lemmas

Lemmas mirroring `SP1Clean/Chips/ALU/AddChip/Lemmas.lean`, adapted for
the 2-variant (`slt`/`sltu`) structural FormalSpec. The chip's
`FormalSpec` (`Chips/Spec.lean`) is the faithful bundle of the three
sub-circuit Specs (`LtSignedOp.AssertionGated` + `CPUState.Gated` +
`ALUTypeReader.Gated`) plus the selector/sum binarities and `op_a_0 = 0`,
NOT a pure-semantic `RV64.slt`/`RV64.sltu` bit. This is mandatory for
completeness: the semantic bit does not pin the free combinatorial
witnesses (`u16_flags`, `comparison_limbs`, `not_eq_inv`), so a
pure-semantic spec would be strictly weaker than the constraints.

- `fromMain_toMain` — `fromMain (toMain cols) = cols` round-trip,
  conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`.
- `slt_sltu_of_formalSpec` — recovers the RV64 semantic
  (`aw = RV64.slt cw bw` / `aw = RV64.sltu cw bw`) on demand from the
  structural `FormalSpec`, via `LtOperationSigned.spec.{signed,unsigned}`.
  Consumed by the Sail bridge.
- `formalSpec_of_subcircuit_specs` — soundness midpoint: bundles the
  per-sub-circuit Specs from `circuit_proof_start` into the chip
  `FormalSpec`.
- `subcircuit_specs_of_formalSpec` — completeness midpoint: destructures
  the chip `FormalSpec` back into the per-sub-circuit Specs (trivial
  now that `FormalSpec` *is* the bundle).
- `allHold_iff_structural` — bridges `(_root_.Lt.constraints
  Main).allHold` to the chip's `FormalSpec`, via
  `Lt.allHold_constraints_iff` + the readers' `Spec_iff_sp1` +
  `LtSignedOp.AssertionGated.iff_sp1`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols
round-trip), conditional on the UserMode TrustMode marker
`cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`. Recursive
`ext` through `@[ext]`-marked sub-structures plus `Vector.ext` reduces
to per-element equations closed by `rfl`. -/
lemma fromMain_toMain (cols : LtCols (ZMod p))
    (h_trusted_eq_sum :
      cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, is_slt, is_sltu, lt_operation, adapter_cols⟩
  rcases lt_operation with ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩,
                            ⟨b_msb⟩, ⟨c_msb⟩⟩
  have h : adapter_cols.is_trusted = is_slt + is_sltu := by simpa using h_trusted_eq_sum
  simp [h, LtCols.ext_iff, CPUState.ext_iff, ALUTypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    (simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp)

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is equivalent to the chip's structural `FormalSpec`,
under `Main[32] + Main[33] = 1` (is_real_sum gate). Composes
`Lt.allHold_constraints_iff` (splits the flat row into the 3 sub-circuit
constraint blocks + 4 gates), the readers' `Spec_iff_sp1`, and the gated
`LtSignedOp.AssertionGated.iff_sp1`. Axiom-clean — no `iff_sp1_full.mpr`
needed, since the structural `FormalSpec` exposes the byte-decomposition
witnesses directly rather than collapsing them to a semantic bit. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44) (h_is_real_sum : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Lt.allHold_constraints_iff Main]
  -- `Assertion.FormalSpec (fromMain Main)` unfolds + `fromMain` projections
  -- reduce to `Main[k]`; only `0 + Main[34]` (ALU op_a_write_value) needs
  -- `zero_add`. The opcode `↑9` cast cleans via `push_cast`.
  simp only [Assertion.FormalSpec, fromMain, zero_add]
  -- Selector/sum binarities ↔ disjunctions (one helper).
  have hbin : ∀ x : ZMod p, x * (x - 1) = 0 ↔ (x = 0 ∨ x = 1) := fun x =>
    ⟨fun h => by binary_iff (by linear_combination h : x * (x + -1) = 0),
     fun h => by rcases h with h | h <;> rw [h] <;> ring⟩
  -- The LtOperationSigned bridge (gated `iff_sp1`), the two reader bridges,
  -- and the gate conversions are assembled per direction.
  have hlt_iff : ∀ (h_slt : Main[32] = 0 ∨ Main[32] = 1),
      (LtOperationSigned.constraints (F := ZMod p)
        #v[Main[15], Main[16], Main[17], Main[18]]
        #v[Main[25], Main[26], Main[27], Main[28]]
        { result := { u16_compare_operation := { bit := Main[34] },
                      u16_flags := #v[Main[35], Main[36], Main[37], Main[38]],
                      not_eq_inv := Main[39],
                      comparison_limbs := #v[Main[40], Main[41]] },
          b_msb := { msb := Main[42] }, c_msb := { msb := Main[43] } }
        Main[32] (Main[32] + Main[33])).allHold ↔
      SP1Clean.LtSignedOp.AssertionGated.Spec
        ⟨#v[Main[15], Main[16], Main[17], Main[18]],
         #v[Main[25], Main[26], Main[27], Main[28]],
         Main[32], Main[34], #v[Main[35], Main[36], Main[37], Main[38]],
         Main[39], #v[Main[40], Main[41]], Main[42], Main[43],
         Main[32] + Main[33]⟩ := fun h_slt => by
    rw [h_is_real_sum]
    exact (SP1Clean.LtSignedOp.AssertionGated.iff_sp1
      ⟨#v[Main[15], Main[16], Main[17], Main[18]],
       #v[Main[25], Main[26], Main[27], Main[28]],
       Main[32], Main[34], #v[Main[35], Main[36], Main[37], Main[38]],
       Main[39], #v[Main[40], Main[41]], Main[42], Main[43],
       1⟩ h_slt rfl).symm
  constructor
  · rintro ⟨h_lt, h_cpu, h_alu, h_slt_bin, h_sltu_bin, _h_sum_bin, h_op_a_0⟩
    refine ⟨(hlt_iff ((hbin _).mp h_slt_bin)).mp h_lt,
            (SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1).mp h_cpu, ?_,
            (hbin _).mp h_slt_bin, (hbin _).mp h_sltu_bin,
            (hbin _).mp (by linear_combination _h_sum_bin), h_op_a_0⟩
    rw [h_is_real_sum] at h_alu ⊢
    exact (SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1).mp (by
      simpa using h_alu)
  · rintro ⟨h_lt, h_cpu, h_alu, h_slt_or, h_sltu_or, _h_sum_or, h_op_a_0⟩
    refine ⟨(hlt_iff h_slt_or).mpr h_lt,
            (SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1).mpr h_cpu, ?_,
            (hbin _).mpr h_slt_or, (hbin _).mpr h_sltu_or,
            (hbin _).mpr (by rw [h_is_real_sum]; exact Or.inr rfl), h_op_a_0⟩
    rw [h_is_real_sum]
    have h_alu' := h_alu
    rw [h_is_real_sum] at h_alu'
    simpa using (SP1Clean.ALUTypeReader.Gated.Assertion.Spec_iff_sp1).mpr h_alu'

/-- `Word.toBitVec64 #v[bit, 0, 0, 0]` for a boolean `bit = if cond then 1
else 0` collapses to the `BitVec`-level `setWidth 64 (ofBool (decide cond))`.
Stated over an abstract `cond`/`BitVec` so its proof term carries no `2 ^ N`
literal — the kernel re-check stays shallow (vs. inlining `Word.toNat_def`
limb expansion into the slt/sltu semantic goals, which trips deep
recursion). Shared by both arms of `formalSpec_of_subcircuit_specs`. -/
private lemma word_bit_toBitVec64 (bit : ZMod p) (cond : Prop) [Decidable cond]
    (h : bit = if cond then 1 else 0) :
    Word.toBitVec64 (#v[bit, 0, 0, 0] : Word (ZMod p)) =
      BitVec.setWidth 64 (BitVec.ofBool (decide cond)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hzero : Word.toBitVec64 (#v[(0 : ZMod p), 0, 0, 0]) = 0 := by
    simp [Word.toBitVec64, Word.toNat_def, ZMod.val_zero]
  have hone : Word.toBitVec64 (#v[(1 : ZMod p), 0, 0, 0]) = 1 := by
    have h1 : (1 : ZMod p).val = 1 :=
      ZMod.val_one_eq_one_mod p ▸
        Nat.one_mod_eq_one.mpr (by have := Fact.out (p := 2 ^ 17 < p); omega)
    simp [Word.toBitVec64, Word.toNat_def, ZMod.val_zero, h1]
  rw [h]; split_ifs with hc <;> [rw [hone]; rw [hzero]] <;> simp [hc]

/-- Recover the RV64 semantic (`aw = RV64.slt cw bw` / `aw = RV64.sltu cw
bw`, plus `Word.isU64` of the result) on demand from the structural
`FormalSpec`. This is the forward-only chain the prior pure-semantic
FormalSpec carried inline; now extracted as a standalone lemma the Sail
bridge consumes. Dispatched through `LtSignedOp.iff_sp1` /
`LtOperationSigned.allHold_constraints_iff` (gated sub-Spec → raw
`allHold`), `LtOperationSigned.spec.{signed,unsigned}` (raw `allHold` →
`toInt`/`toNat` bit value), and `word_bit_toBitVec64` (bit value →
`RV64.{slt,sltu}` BitVec form). `Word.isU64 op_b/op_c` come from the ALU
reader Spec's `RegisterAccess` sub-conjuncts. -/
lemma slt_sltu_of_formalSpec (cols : LtCols (ZMod p))
    (h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu)
    (h_spec : Assertion.FormalSpec cols) :
    cols.is_slt + cols.is_sltu = 1 →
      Word.isU64 (#v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0] :
          Word (ZMod p)) ∧
      (cols.is_slt = 1 →
        Word.toBitVec64 (#v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0] :
            Word (ZMod p)) =
          RV64.slt (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                   (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)) ∧
      (cols.is_sltu = 1 →
        Word.toBitVec64 (#v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0] :
            Word (ZMod p)) =
          RV64.sltu (Word.toBitVec64 cols.adapter.op_c_memory.prev_value)
                    (Word.toBitVec64 cols.adapter.op_b_memory.prev_value)) := by
  obtain ⟨h_ltop_spec, _h_cpu, h_alu, h_is_slt_or, _h_is_sltu_or, _h_sum_or, _h_op_a_0⟩ :=
    h_spec
  intro h_is_real
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Peel the gated `LtSignedOp.AssertionGated.Spec` body (real row).
  obtain ⟨_h_u16_b, _h_u16_c, h_lt_unsigned, _h_is_signed_bin, _h_b_vac, _h_c_vac⟩ :=
    h_ltop_spec h_is_real
  -- LtUnsignedOp.AssertionGated.Spec on the shifted operands embeds the
  -- compare_bit binarity (from U16CompareOp.Assertion.Spec).
  obtain ⟨h_u16cmp, _⟩ := h_lt_unsigned h_is_real
  have h_bit_bin : cols.lt_operation.result.u16_compare_operation.bit *
      (cols.lt_operation.result.u16_compare_operation.bit + -1) = 0 := by
    have h := h_u16cmp.1
    linear_combination h
  have h_bit_or : cols.lt_operation.result.u16_compare_operation.bit = 0 ∨
      cols.lt_operation.result.u16_compare_operation.bit = 1 := by
    binary_iff h_bit_bin
  -- Word.isU64 #v[bit, 0, 0, 0] from bit ∈ {0,1}; other limbs are 0.
  have h_isU64_aw : Word.isU64
      (#v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0] :
        Word (ZMod p)) := by
    apply Word.isU64_of_cases
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
      rcases h_bit_or with h | h <;> rw [h] <;>
        simp [ZMod.val_zero, ZMod.val_one]
    all_goals (simp only [Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]; omega)
  have h_trusted_eq : cols.adapter_cols.is_trusted = 1 := by
    rw [h_trusted, h_is_real_sum]
  have h_isU64_b :=
    SP1Clean.ALUTypeReader.Gated.Assertion.isU64_op_b_of_spec h_is_real h_alu
  have h_isU64_c :=
    SP1Clean.ALUTypeReader.Gated.Assertion.isU64_op_c_memory_of_spec
      h_is_real h_trusted_eq h_alu
  refine ⟨h_isU64_aw, ?_, ?_⟩
  · -- slt arm: signed `<` via `LtSignedOp.iff_sp1` + `spec.signed`.
    intro h_is_slt
    have h_lt_spec : SP1Clean.LtSignedOp.Spec
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
         cols.is_slt, cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags, cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs, cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb⟩ :=
      ⟨_h_u16_b h_is_slt, _h_u16_c h_is_slt, h_lt_unsigned h_is_real,
       by rw [h_is_slt]; ring, by rw [h_is_slt]; ring, by rw [h_is_slt]; ring⟩
    have h_allHold := (SP1Clean.LtSignedOp.iff_sp1 _ h_is_slt).mp h_lt_spec
    rw [h_is_slt] at h_allHold
    have h_bit_eq := LtOperationSigned.spec.signed h_isU64_b h_isU64_c h_allHold
    rw [← Word.toBitVec64_toInt h_isU64_b, ← Word.toBitVec64_toInt h_isU64_c]
      at h_bit_eq
    rw [RV64.slt, BitVec.slt]
    exact word_bit_toBitVec64 _ _ h_bit_eq
  · -- sltu arm: unsigned `<`; `is_sltu = 1` forces `is_slt = 0`, the two
    -- U16MSB blocks are mult-0 vacuous, sign-vacuity gives `b_msb = c_msb = 0`.
    intro h_is_sltu
    have h_is_slt : cols.is_slt = 0 := by
      rw [h_is_sltu] at h_is_real_sum; linear_combination h_is_real_sum
    have h_bmsb0 : cols.lt_operation.b_msb.msb = 0 := by
      have := _h_b_vac; rw [h_is_slt] at this; linear_combination - this
    have h_cmsb0 : cols.lt_operation.c_msb.msb = 0 := by
      have := _h_c_vac; rw [h_is_slt] at this; linear_combination - this
    have h_unsigned_spec : SP1Clean.LtUnsignedOp.Spec
        ⟨#v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
            cols.adapter.op_b_memory.prev_value[2],
            cols.adapter.op_b_memory.prev_value[3] + cols.is_slt * 32768 -
              65536 * cols.lt_operation.b_msb.msb],
         #v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1],
            cols.adapter.op_c_memory.prev_value[2],
            cols.adapter.op_c_memory.prev_value[3] + cols.is_slt * 32768 -
              65536 * cols.lt_operation.c_msb.msb],
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags, cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs⟩ := h_lt_unsigned h_is_real
    have h_lt_unsigned_allHold := (SP1Clean.LtUnsignedOp.iff_sp1 _).mp h_unsigned_spec
    have h_allHold : (LtOperationSigned.constraints
        cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
        { result := { u16_compare_operation :=
                        { bit := cols.lt_operation.result.u16_compare_operation.bit },
                      u16_flags := cols.lt_operation.result.u16_flags,
                      not_eq_inv := cols.lt_operation.result.not_eq_inv,
                      comparison_limbs := cols.lt_operation.result.comparison_limbs },
          b_msb := { msb := cols.lt_operation.b_msb.msb },
          c_msb := { msb := cols.lt_operation.c_msb.msb } } 0 1).allHold := by
      rw [show ((LtOperationSigned.constraints _ _ _ (0 : ZMod p) 1).allHold) =
            List.Forall SP1Constraint.toProp
              (LtOperationSigned.constraints cols.adapter.op_b_memory.prev_value
                cols.adapter.op_c_memory.prev_value _ (0 : ZMod p) 1) from rfl,
          LtOperationSigned.allHold_constraints_iff]
      refine ⟨?_, ?_, ?_, Or.inl rfl, Or.inr h_bmsb0, Or.inr h_cmsb0⟩
      · simp only [U16MSBOperation.constraints, List.Forall, SP1Constraint.toProp]
        exact ⟨by ring, by rw [h_bmsb0]; ring, by simp⟩
      · simp only [U16MSBOperation.constraints, List.Forall, SP1Constraint.toProp]
        exact ⟨by ring, by rw [h_cmsb0]; ring, by simp⟩
      · convert h_lt_unsigned_allHold using 3 <;> rw [h_is_slt] <;>
          ext i <;> fin_cases i <;> rfl
    have h_bit_eq := LtOperationSigned.spec.unsigned h_isU64_b h_isU64_c h_allHold
    rw [← Word.toBitVec64_toNat h_isU64_b, ← Word.toBitVec64_toNat h_isU64_c]
      at h_bit_eq
    rw [RV64.sltu, BitVec.ult]
    exact word_bit_toBitVec64 _ _ h_bit_eq

/-- **Forward** (soundness midpoint): assemble the chip-level structural
`FormalSpec` from the per-sub-circuit Specs returned by `circuit_proof_start`.
The `LtSignedOp` hypothesis is the `Assumptions → Spec` function form;
discharge its `Assumptions` (is_real binary from sum-binary, is_signed
binary from selector-binary, padding-unsigned from selector arithmetic),
apply it, convert the three `x*(x-1)=0` gates to disjunctions, and bundle. -/
lemma formalSpec_of_subcircuit_specs
    (cols : LtCols (ZMod p))
    (_h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_trusted : cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu)
    (h_ltop : SP1Clean.LtSignedOp.AssertionGated.Assumptions
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩ →
      SP1Clean.LtSignedOp.AssertionGated.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_slt + cols.is_sltu⟩)
    (h_alu : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_slt * 9 + cols.is_sltu * 10,
         cols.state.pc,
         #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0],
         cols.adapter,
         cols.is_slt + cols.is_sltu,
         cols.adapter_cols.is_trusted⟩)
    (h_is_slt_bin : cols.is_slt * (cols.is_slt - 1) = 0)
    (h_is_sltu_bin : cols.is_sltu * (cols.is_sltu - 1) = 0)
    (h_sum_bin : (cols.is_slt + cols.is_sltu) *
                    (cols.is_slt + cols.is_sltu - 1) = 0)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    Assertion.FormalSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbin : ∀ x : ZMod p, x * (x - 1) = 0 → (x = 0 ∨ x = 1) := fun x h => by
    binary_iff (by linear_combination h : x * (x + -1) = 0)
  have h_is_slt_or := hbin _ h_is_slt_bin
  have h_is_sltu_or := hbin _ h_is_sltu_bin
  have h_sum_or := hbin _ h_sum_bin
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h2val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2lt
    intro heq; rw [heq, ZMod.val_zero] at h2val; omega
  -- Discharge `LtSignedOp.AssertionGated.Assumptions` (padding-unsigned via 2≠0).
  have h_ltop_assumps : SP1Clean.LtSignedOp.AssertionGated.Assumptions
      ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
       cols.is_slt, cols.lt_operation.result.u16_compare_operation.bit,
       cols.lt_operation.result.u16_flags, cols.lt_operation.result.not_eq_inv,
       cols.lt_operation.result.comparison_limbs, cols.lt_operation.b_msb.msb,
       cols.lt_operation.c_msb.msb, cols.is_slt + cols.is_sltu⟩ :=
    ⟨h_sum_or, h_is_slt_or,
     fun h_ir0 => by
       rcases h_is_slt_or with h | h
       · exact h
       · exfalso
         rcases h_is_sltu_or with h' | h'
         · rw [h, h'] at h_ir0; exact absurd (by linear_combination h_ir0 : (1 : ZMod p) = 0)
              one_ne_zero
         · rw [h, h'] at h_ir0; exact absurd (by linear_combination h_ir0 : (2 : ZMod p) = 0)
              h2ne⟩
  exact ⟨h_ltop h_ltop_assumps, h_cpu, h_alu, h_is_slt_or, h_is_sltu_or,
         h_sum_or, h_op_a_0⟩

/-- **Backward** (completeness midpoint): peel the chip-level structural
`FormalSpec` apart into per-sub-circuit `Spec`s. Trivial now that
`FormalSpec` *is* the bundle — destructure and convert each disjunction
`x = 0 ∨ x = 1` back to `x * (x - 1) = 0`. -/
lemma subcircuit_specs_of_formalSpec
    (cols : LtCols (ZMod p))
    (_h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_trusted : cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu)
    (h_spec : Assertion.FormalSpec cols) :
    SP1Clean.LtSignedOp.AssertionGated.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩ ∧
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_slt + cols.is_sltu⟩ ∧
    SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_slt * 9 + cols.is_sltu * 10,
         cols.state.pc,
         #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0],
         cols.adapter,
         cols.is_slt + cols.is_sltu,
         cols.adapter_cols.is_trusted⟩ ∧
    cols.is_slt * (cols.is_slt - 1) = 0 ∧
    cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
    (cols.is_slt + cols.is_sltu) *
      (cols.is_slt + cols.is_sltu - 1) = 0 ∧
    cols.adapter.op_a_0 = 0 := by
  obtain ⟨h_ltop, h_cpu, h_alu, h_slt_or, h_sltu_or, h_sum_or, h_op_a_0⟩ := h_spec
  refine ⟨h_ltop, h_cpu, h_alu, ?_, ?_, ?_, h_op_a_0⟩
  · rcases h_slt_or with h | h <;> rw [h] <;> ring
  · rcases h_sltu_or with h | h <;> rw [h] <;> ring
  · rcases h_sum_or with h | h <;> rw [h] <;> ring

end SP1Clean.Lt
