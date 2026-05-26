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

## TODOs (stubs to discharge in follow-up)

1. **`SP1Clean.ITypeReaderImmutable.Gated.assertion` does not exist.**
   `SP1Clean/Reader/ITypeReaderImmutable.lean` exposes a non-gated
   `FormalAssertion` (`assertion`); `SP1Clean/Reader/ITypeReader.lean:
   317-436` is the template for adding a `Gated` namespace. The non-gated
   form is used here as a stub. Promoting to a true `.Gated` variant
   will (i) add `is_real`/`is_trusted` fields to its `Inputs`, (ii)
   thread them through `RegisterAccess`/`ProgramTable` gating, and
   (iii) update the Spec to the disjunctive `is_real = 0 ∨ …` form.
2. **`LtOperationSigned` Clean `FormalAssertion` does not exist.**
   `SP1Clean/Compare/LtOperationSigned.lean` only derives
   `ProvableStruct` instances; the actual comparison sub-circuit
   (`U16MSBOperation` × 2 + `LtOperationUnsigned`-style limb compares)
   is not yet ported to a Clean subcircuit composition. The comparison
   constraints are intentionally **omitted** from `main` and
   `FormalSpec` here; they remain carried by the iter-9 baseline
   `SP1Clean/BranchChip.lean`'s legacy `TraceSpec` until ported.
3. **Soundness / completeness** are sorry-stubbed. The structural
   pattern mirrors `SP1Clean/Jalr/Circuit.lean:163-196`; once the two
   stubs above land, the proof body should fall out by analogy.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Branch

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
  -- (5) ITypeReaderImmutable (program-bus + op_a/op_b register reads).
  -- STUB (multiplicity-aware Branch sibling): using the non-gated
  -- `assertion`; promote to `ITypeReaderImmutable.Gated.assertion` once
  -- that variant is built (see TODO 1 above).
  SP1Clean.ITypeReaderImmutable.assertion
    (⟨clk_high, clk_low, opcode_e, pc, adapter⟩ :
      Var SP1Clean.ITypeReaderImmutable.Inputs (ZMod p))
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

set_option maxHeartbeats 800000 in
-- Higher heartbeats: Branch has 13 top-level Cols fields (Cols struct
-- flattens to ~45 input bits) + 4 subcircuit calls + 3 lookups;
-- localLength_eq synthesis hits the 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BranchCols unit where
  name := "SP1Clean.Branch"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

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
  -- (5) ITypeReaderImmutable Spec (non-gated stub form). TODO 1.
  SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec
    clk_low opcode_e cols.state.pc cols.adapter ∧
  -- (6) is_branching outcome equation.
  sum * (cols.is_branching -
    (cols.is_beq * (1 - u16_sum) + cols.is_bne * u16_sum +
     (cols.is_bge + cols.is_bgeu) * (1 - bit) +
     (cols.is_blt + cols.is_bltu) * bit)) = 0 ∧
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

-- STUB (multiplicity-aware Branch sibling): soundness deferred until
-- TODO 1 (`ITypeReaderImmutable.Gated`) and TODO 2 (`LtOperationSigned`
-- subcircuit) land. Proof pattern mirrors `SP1Clean/Jalr/Circuit.lean:
-- 163-179`: `circuit_proof_start` then destructure `h_input`/`h_holds`
-- and `refine ⟨…⟩` over the eleven sub-Specs.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

-- STUB (multiplicity-aware Branch sibling): completeness deferred,
-- same rationale as `soundness`. Proof pattern mirrors
-- `SP1Clean/Jalr/Circuit.lean:181-196`.
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
