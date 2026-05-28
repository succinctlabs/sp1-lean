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
import SP1Clean.Reader.ITypeReaderImmutable
import SP1Clean.Operations.GatedAddOp
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.SP1Lookup
import SP1Clean.TrustMode
import SP1Clean.Chips.Control.BranchChip.Multiplicity.Cols

/-! # `BranchChip` Clean circuit + `FormalAssertion` (multiplicity-aware redesign)

Faithful structural mirror of Rust `BranchChip::eval`
(`sp1/crates/core/machine/src/control_flow/branch/air.rs`). Every
`builder.assert_*` / sub-eval invocation in `air.rs` maps to exactly one
sub-`FormalAssertion` (or one scalar gate) in `main`. Models the
six-variant bundle (BEQ/BNE/BLT/BGE/BLTU/BGEU) via six selector columns
whose sum is the aggregate `is_real`.

Differences from `SP1Clean.Jal.Circuit` / `SP1Clean.Jalr.Circuit`:
- Aggregate `is_real` is the sum of six selectors, not a single bit.
- Two `GatedAddOp.assertion` invocations gate on disjoint subsets of
  `is_real` (`is_branching` for the taken arm, `is_real - is_branching`
  for the not-taken arm), so the branch-taken outcome lives in the
  same `next_pc` column regardless of arm.
- Uses (the non-gated) `ITypeReaderImmutable.assertion` as a stub for
  the not-yet-built `ITypeReaderImmutable.Gated` (see TODOs below).

Sub-circuits composed (in `air.rs` source order):
1. Sum-of-selectors-binary: `(Σ sel) * (Σ sel - 1) === 0`.
2. Six selector booleans: `sel * (sel - 1) === 0` for sel ∈ {is_beq, …, is_bgeu}.
3. `is_branching * (is_branching - 1) === 0`.
4. `SP1Clean.CPUState.assertion`.
5. `SP1Clean.ITypeReaderImmutable.assertion` (program-bus + 2 register
   reads). NOTE: non-gated stub; see TODO (1).
6. `is_branching` outcome equation gated by aggregate `is_real`:
   `Σ * (is_branching - (is_beq*(1-Σu16) + is_bne*Σu16 +
        (is_bge+is_bgeu)*(1-bit) + (is_blt+is_bltu)*bit)) === 0`.
7. `SP1Clean.GatedAddOp.assertion` for `pc + op_c_imm = next_pc`
   (branch-taken arm), `gate := is_branching`.
8. `SP1Clean.GatedAddOp.assertion` for `pc + 4 = next_pc`
   (branch-not-taken arm), `gate := Σ - is_branching`.
9. `SP1Lookup.byteOpcodeGated` — `next_pc[0] * 4⁻¹ ∈ Range14`,
   `mult := Σ`.
10. `SP1Lookup.byteOpcodeGated` — `next_pc[1] ∈ Range16`, `mult := Σ`.
11. `SP1Lookup.byteOpcodeGated` — `next_pc[2] ∈ Range16`, `mult := Σ`.

## Status (2026-05-27 — Phase 2B.5 + 2C + 3B partial)

1. **`SP1Clean.ITypeReaderImmutable.Gated.assertion`** — **LANDED**
   (`SP1Clean/Reader/ITypeReaderImmutable.lean:283-502`). `main` and
   `FormalSpec` here now compose it directly via
   `Gated.Assertion.Spec ⟨…, is_real := sum, is_trusted := sum⟩`.
2. **`LtOperationSigned` gated Clean `FormalAssertion`** — **LANDED**
   as `SP1Clean.LtSignedOp.assertionGated` (Phase 2C,
   `SP1Clean/Operations/LtOperationSigned.lean`). `main` here now
   composes the gated subcircuit + adds the `LtSignedOp.AssertionGated.Spec`
   conjunct to `FormalSpec`, with operands wired from `adapter.op_a_memory.
   prev_value` / `adapter.op_b_memory.prev_value`, witness columns from
   `compare_operation.*`, `is_signed := is_blt + is_bge`, and
   `is_real := sum`.
3. **Soundness / completeness** — **STILL sorry-stubbed.** The blocker is
   discharging `LtSignedOp.AssertionGated.Assumptions` (which requires
   `is_blt + is_bge ∈ {0, 1}` and `sum = 0 → is_blt + is_bge = 0`) from
   the chip-level selector + sum binarity gates. This needs a
   field-characteristic case bash (`(k)(k-1) ≠ 0` in `ZMod p` for
   `k ∈ {2..6}` under `Fact (2 ^ 17 < p)`). Pattern otherwise mirrors
   `Aggregate.lean:384-454`. Tracked as Phase 3B residual work.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Branch

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- Field-characteristic discharge of the non-trivial parts of
`LtSignedOp.AssertionGated.Assumptions`: from the six selector binarity gates
plus the aggregate sum-binarity gate, `is_blt + is_bge ∈ {0,1}` and
`sum = 0 → is_blt + is_bge = 0`. The only obstruction is `is_blt = is_bge = 1`,
which forces the six-selector ℕ-sum into `{2,…,6}`, contradicting
`sum * (sum - 1) = 0` since `k(k-1) ≠ 0` in `ZMod p` for `k ∈ {2,…,6}` under
`Fact (2 ^ 17 < p)`. Proven by a 64-way selector case-bash. -/
lemma selector_binary
    (is_beq is_bne is_blt is_bge is_bltu is_bgeu : ZMod p)
    (h_beq : is_beq * (is_beq - 1) = 0) (h_bne : is_bne * (is_bne - 1) = 0)
    (h_blt : is_blt * (is_blt - 1) = 0) (h_bge : is_bge * (is_bge - 1) = 0)
    (h_bltu : is_bltu * (is_bltu - 1) = 0) (h_bgeu : is_bgeu * (is_bgeu - 1) = 0)
    (h_sum : (is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu) *
        ((is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu) - 1) = 0) :
    (is_blt + is_bge = 0 ∨ is_blt + is_bge = 1) ∧
    ((is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu) = 0 →
      is_blt + is_bge = 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hple : 2 ^ 17 < p := Fact.out
  have hk : ∀ k : ℕ, 0 < k → k < p → (k : ZMod p) ≠ 0 := by
    intro k hk0 hkp heq
    rw [CharP.cast_eq_zero_iff (ZMod p) p k] at heq
    exact absurd (Nat.le_of_dvd hk0 heq) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hk 2 (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast hk 3 (by norm_num) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by exact_mod_cast hk 4 (by norm_num) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := by exact_mod_cast hk 5 (by norm_num) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := by exact_mod_cast hk 6 (by norm_num) (by omega)
  have h12 : (12 : ZMod p) ≠ 0 := by exact_mod_cast hk 12 (by norm_num) (by omega)
  have h20 : (20 : ZMod p) ≠ 0 := by exact_mod_cast hk 20 (by norm_num) (by omega)
  have h30 : (30 : ZMod p) ≠ 0 := by exact_mod_cast hk 30 (by norm_num) (by omega)
  have key : ∀ x : ZMod p, x * (x - 1) = 0 → x = 0 ∨ x = 1 := fun x h => by
    binary_iff (by linear_combination h : x * (x + -1) = 0)
  clear hk hple
  rcases key _ h_beq with h | h <;> rcases key _ h_bne with h' | h' <;>
    rcases key _ h_blt with h'' | h'' <;> rcases key _ h_bge with h₃ | h₃ <;>
    rcases key _ h_bltu with h₄ | h₄ <;> rcases key _ h_bgeu with h₅ | h₅ <;>
    subst_vars
  all_goals exact (by
    first
    | (exfalso; revert h_sum; norm_num; assumption)
    | exact ⟨by norm_num, by norm_num⟩)

namespace Assertion

open Circuit

-- Derive `Fact (p > 512)` from `Fact (2 ^ 17 < p)` for byteOpcodeGated.
instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Clean-side chip circuit. One sub-`FormalAssertion` per Rust
`air.rs` eval invocation; see the file docstring for the 1-to-1 map.

NOTE: this is a multiplicity-aware redesign stub. The
`ITypeReaderImmutable.assertion` line is non-gated (TODO 1 in the file
docstring), and the `LtOperationSigned` comparison subcircuit is
omitted (TODO 2). -/
@[reducible]
def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       is_branching, compare_operation, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  -- (1) Aggregate is_real = Σ selectors is boolean.
  sum * (sum - 1) === 0
  -- (2) Six selector booleans.
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  -- (3) is_branching boolean.
  is_branching * (is_branching - 1) === 0
  -- (4) CPUState clock-fields range bounds.
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- (5) ITypeReaderImmutable.Gated (program-bus + op_a/op_b register reads),
  -- gated by `sum` for both `is_real` and `is_trusted` (Branch is User-mode
  -- unconditionally; both gate together).
  SP1Clean.ITypeReaderImmutable.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, adapter, sum, sum⟩ :
      Var SP1Clean.ITypeReaderImmutable.Gated.Inputs (ZMod p))
  -- (6) is_branching outcome equation. Σu16_flags + bit are the
  -- comparison witnesses surfaced by the `compare_operation` struct.
  let u16_sum := compare_operation.result.u16_flags[0] +
                 compare_operation.result.u16_flags[1] +
                 compare_operation.result.u16_flags[2] +
                 compare_operation.result.u16_flags[3]
  let bit := compare_operation.result.u16_compare_operation.bit
  sum * (is_branching -
    (is_beq * (1 - u16_sum) + is_bne * u16_sum +
     (is_bge + is_bgeu) * (1 - bit) + (is_blt + is_bltu) * bit)) === 0
  -- (6.5) LtSignedOp comparison sub-circuit. Operands are the op_a/op_b
  -- register reads (from adapter); is_signed = is_blt + is_bge (signed
  -- variants only). Multiplicity = sum (aggregate is_real).
  SP1Clean.LtSignedOp.assertionGated
    (⟨adapter.op_a_memory.prev_value, adapter.op_b_memory.prev_value,
       is_blt + is_bge,
       compare_operation.result.u16_compare_operation.bit,
       compare_operation.result.u16_flags,
       compare_operation.result.not_eq_inv,
       compare_operation.result.comparison_limbs,
       compare_operation.b_msb.msb,
       compare_operation.c_msb.msb,
       sum⟩ : Var SP1Clean.LtSignedOp.InputsGated (ZMod p))
  -- (7) Branch-taken arm: pc + op_c_imm = next_pc, gated by is_branching.
  SP1Clean.GatedAddOp.assertion
    (⟨pc.push 0, adapter.op_c_imm, next_pc.push 0, is_branching⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (8) Branch-not-taken arm: pc + 4 = next_pc, gated by Σ - is_branching.
  SP1Clean.GatedAddOp.assertion
    (⟨pc.push 0, #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc.push 0, sum - is_branching⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- (9) PC[0] mod-4 alignment (Range14 over (pc/4)), gated by Σ.
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), next_pc[0] * (4 : ZMod p)⁻¹, 14, 0],
       sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- (10) PC[1] u16 range, gated by Σ.
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), next_pc[1], 16, 0], sum⟩ :
      Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- (11) PC[2] u16 range, gated by Σ.
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), next_pc[2], 16, 0], sum⟩ :
      Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

set_option maxHeartbeats 2000000 in
-- Higher heartbeats: Branch has 13 top-level Cols fields + 5 subcircuit
-- calls + 3 lookups; localLength_eq + subcircuitsConsistent synthesis
-- exceeds the default cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BranchCols unit where
  name := "SP1Clean.Branch"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

def Assumptions (_ : BranchCols (ZMod p)) : Prop := True

/-- Chip-level `FormalSpec`: composes the sub-`Spec`s of each
sub-`FormalAssertion` in `main`. Each conjunct corresponds to one
numbered emission in the docstring (in the same order). The
`LtOperationSigned` comparison-witness equations (TODO 2 in the file
docstring) are intentionally omitted; they remain in the iter-9
baseline's `TraceSpec`. -/
def FormalSpec (cols : BranchCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let sum : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  let u16_sum : ZMod p :=
    cols.compare_operation.result.u16_flags[0] +
    cols.compare_operation.result.u16_flags[1] +
    cols.compare_operation.result.u16_flags[2] +
    cols.compare_operation.result.u16_flags[3]
  let bit : ZMod p := cols.compare_operation.result.u16_compare_operation.bit
  -- (1) Σ binary.
  sum * (sum - 1) = 0 ∧
  -- (2) Six selector booleans.
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  -- (3) is_branching binary.
  cols.is_branching * (cols.is_branching - 1) = 0 ∧
  -- (4) CPUState range bounds.
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  -- (5) ITypeReaderImmutable.Gated Spec (literal-conjunction).
  SP1Clean.ITypeReaderImmutable.Gated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode_e, cols.state.pc, cols.adapter,
     sum, sum⟩ ∧
  -- (6) is_branching outcome equation.
  sum * (cols.is_branching -
    (cols.is_beq * (1 - u16_sum) + cols.is_bne * u16_sum +
     (cols.is_bge + cols.is_bgeu) * (1 - bit) +
     (cols.is_blt + cols.is_bltu) * bit)) = 0 ∧
  -- (6.5) LtSignedOp comparison sub-Spec (implicational on sum = 1).
  SP1Clean.LtSignedOp.AssertionGated.Spec
    ⟨cols.adapter.op_a_memory.prev_value,
     cols.adapter.op_b_memory.prev_value,
     cols.is_blt + cols.is_bge,
     cols.compare_operation.result.u16_compare_operation.bit,
     cols.compare_operation.result.u16_flags,
     cols.compare_operation.result.not_eq_inv,
     cols.compare_operation.result.comparison_limbs,
     cols.compare_operation.b_msb.msb,
     cols.compare_operation.c_msb.msb,
     sum⟩ ∧
  -- (7) Branch-taken sum.
  SP1Clean.GatedAddOp.Assertion.FormalSpec
    ⟨cols.state.pc.push 0, cols.adapter.op_c_imm, cols.next_pc.push 0,
     cols.is_branching⟩ ∧
  -- (8) Branch-not-taken sum.
  SP1Clean.GatedAddOp.Assertion.FormalSpec
    ⟨cols.state.pc.push 0, #v[(4 : ZMod p), 0, 0, 0], cols.next_pc.push 0,
     sum - cols.is_branching⟩ ∧
  -- (9) PC[0] mod-4 alignment.
  SP1Lookup.ByteOpcodeGated.Spec
    ⟨#v[(6 : ZMod p), cols.next_pc[0] * (4 : ZMod p)⁻¹, 14, 0], sum⟩ ∧
  -- (10) PC[1] u16 range.
  SP1Lookup.ByteOpcodeGated.Spec
    ⟨#v[(6 : ZMod p), cols.next_pc[1], 16, 0], sum⟩ ∧
  -- (11) PC[2] u16 range.
  SP1Lookup.ByteOpcodeGated.Spec
    ⟨#v[(6 : ZMod p), cols.next_pc[2], 16, 0], sum⟩

-- STUB (Phase 3B partial — 2026-05-27): the chip-level `main` and
-- `FormalSpec` have been rewired to use the new gated subcircuits
-- (Phase 2B.5: `LtUnsignedOp.AssertionGated`; Phase 2C:
-- `LtSignedOp.AssertionGated`) and `ITypeReaderImmutable.Gated.assertion`
-- (already landed). The soundness/completeness closure remains deferred:
-- discharging `LtSignedOp.AssertionGated.Assumptions` requires proving
-- `is_blt + is_bge ∈ {0, 1}` from the six selector-binarity gates plus
-- the aggregate `sum * (sum - 1) = 0` gate. The proof needs a
-- field-characteristic case bash (showing that `sum * (sum - 1) ≠ 0`
-- when `sum ∈ {2, 3, 4, 5, 6}` in `ZMod p` with `Fact (2 ^ 17 < p)`),
-- plus an analogous discharge for `is_real = 0 → is_signed = 0`. The
-- proof pattern otherwise mirrors `Aggregate.lean:384-454` — destructure
-- `h_holds` / `h_spec`, refine over the new 14-conjunct FormalSpec.
-- The selector-binarity blocker (`selector_binary` above) is PROVEN axiom-clean.
-- With it, 16 of the 17 `FormalSpec` conjuncts close via the standard recipe:
--   circuit_proof_start
--   obtain ⟨⟨e_ch,e_c16,e_c0,e_pc⟩, e_adapter, e_npc, e_beq, e_bne, e_blt,
--           e_bge, e_bltu, e_bgeu, e_br, e_cmp, e_ac⟩ := h_input
--   subst_eqs
--   obtain ⟨h_sum, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_br, h_cpu,
--           h_itr, h_outcome, h_ltsigned, h_gadd1, h_gadd2, h_bo0, h_bo1, h_bo2⟩
--     := h_holds
--   simp only [Vector.map_push, ← sub_eq_add_neg] at h_gadd1 h_gadd2
--   have hsel := selector_binary _ _ _ _ _ _ (by linear_combination h_beq) … (by
--     linear_combination h_sum)
--   refine ⟨…, h_cpu trivial, h_itr trivial, ?_, ?_, h_gadd1 trivial,
--           h_gadd2 trivial, ?_, ?_, ?_⟩
--   · {8 gate conjuncts}  linear_combination h_{sum,beq,…,br}
--   · {LtSignedOp arm}    exact h_ltsigned ⟨by binary_iff h_sum, hsel.1, hsel.2⟩
--   · {byteOpcode arms}   simpa only [Vector.getElem_map] using h_bo{0,1,2} trivial
-- REMAINING (the only open conjunct): the `is_branching` outcome equation.
-- `subst_eqs` of the destructured `compare_operation` generalizes the goal's
-- `u16_flags` to a ZMod `Word` fvar (`input_…_u16_flags[i]`) while `h_outcome`
-- keeps `eval(input_var_…[i])` — equal but ring-distinct atoms (the
-- `Vector.map`/`getElem` link equation is consumed by `subst_eqs`). Neither
-- `linear_combination` (ring, atom-blind) nor `convert` (defeq, no ring) bridges
-- both gaps. Fix: keep `compare_operation` folded (don't `subst_eqs` its
-- equation) so both sides stay in `eval input_var` form, then
-- `simp [Vector.getElem_map]; linear_combination h_outcome`.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The Clean `FormalAssertion` for `BranchChip` rebuilt on the
multiplicity-aware lookup bus. Stub: see file docstring TODOs and the
two `sorry`s in `Assertion.soundness`/`Assertion.completeness`. -/
def assertion : FormalAssertion (ZMod p) BranchCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Branch
