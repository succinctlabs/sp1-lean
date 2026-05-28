import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.MemoryAccess
import SP1Clean.Operations.IsZeroOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

set_option linter.style.setOption false
set_option linter.style.longLine false

/-! # Boundary memory chips: `MemoryGlobalInit` and `MemoryGlobalFinalize`

SP1 emits two boundary memory chips to close the global memory bus:
`MemoryGlobalInit` and `MemoryGlobalFinalize`
(see `/home/dtumad/Documents/sp1/crates/core/machine/src/memory/global.rs:256-298`).
Both share the same column layout (`MemoryInitCols`); they differ only
in the bus they emit on (`MemoryGlobalInitControl` vs.
`MemoryGlobalFinalizeControl`, `InteractionKind` 14 / 15) and in the
direction of the address-monotonicity check.

## Role in the trace-soundness pipeline

The interior chips (Add, Lt, Load*, Store*, ...) emit per-row memory
accesses keyed by `(clk, addr)`. For the offline-consistency theorem
(`Clean.Utils.OfflineMemory`) to close, every accessed address must
have an INIT record (claiming the initial value) and a FINALIZE record
(claiming the final value being read out). The boundary chips supply
these "ghost" first/last records.

## Phase 4 status (iter-8, [[clean-pilot-iter8-table-bridging]])

This file ships the **column struct + ChipRow constructors only**. The
chip's `Spec` is `True` (placeholder); the internal constraint surface
(range checks on `addr`/`prev_addr`/`value`, the `lt_cols` monotonicity
assertion, the two `IsZeroOperation` arms on `is_prev_addr_zero` /
`is_index_zero`) is deferred to a follow-up sub-iter that promotes
`MemoryGlobalCols` to a full `FormalAssertion` analogous to the
interior chips.

The boundary records' contribution to `aggregateMemoryAccesses` is
likewise minimal in Phase 4: both `memInit` and `memFinalize` emit an
empty access list. The full bus closure (concatenating boundary tuples
with interior tuples) is iter-8 Phase 4.5 follow-up work.
-/

namespace SP1Clean.MemoryGlobal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Minimal `Spec` for boundary chips. Phase 4 ships only the
`is_real * (is_real - 1) = 0` binary gate — the gate that SP1's source
emits at `global.rs:313` (`builder.assert_bool(local.is_real)`).
The internal constraints (range checks on addr/prev_addr/value,
monotonicity via `lt_cols`, the two IsZero witnesses) are deferred to a
follow-up sub-iter that lifts `MemoryGlobalCols` to a full
`FormalAssertion`.

The binary gate is included because downstream trace-soundness
infrastructure (`TraceIsRealBinary` in `Soundness/IsRealBinary.lean`)
needs `is_real ∈ {0, 1}` on every chip row — including boundary rows. -/
def Spec (cols : MemoryGlobalCols (ZMod p)) : Prop :=
  cols.is_real * (cols.is_real - 1) = 0

/-! ## Bus-side memoryAccess emission (placeholder for Phase 4)

When fully wired into the trace-soundness pipeline, boundary chips
emit `MemoryAccess` records that close the global memory bus:

- `MemoryGlobalInit`: one access at timestamp `(0, 0)` claiming
  `prev_value = 0` (no previous access) and writing `cols.value`.
- `MemoryGlobalFinalize`: one access at `(cols.clk_high, cols.clk_low)`
  reading `cols.value` as the final value at `cols.addr`.

Phase 4 returns an empty list — the boundary records' contribution to
`aggregateMemoryAccesses` is deferred to a follow-up sub-iter
(Phase 4.5) that:
1. Threads boundary tuples into the trace-level `MemoryAccessList`.
2. Provides the matching `memoryAccessSpec` discharge.
3. Verifies the timestamp-sorted / Notimestampdup properties hold
   across the combined boundary + interior list. -/

/-- Per-chip memory-access list for the `MemoryGlobalInit` chip.
Placeholder: emits empty list in Phase 4. The eventual full emission
is one access at timestamp `(0, 0)` per `cols.addr` writing
`cols.value`. -/
def initMemoryAccesses (_cols : MemoryGlobalCols (ZMod p)) :
    List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p)) :=
  []

/-- Per-chip memory-access list for the `MemoryGlobalFinalize` chip.
Placeholder: emits empty list in Phase 4. The eventual full emission
is one access at `(cols.clk_high, cols.clk_low)` per `cols.addr`
reading `cols.value` as the final value. -/
def finalizeMemoryAccesses (_cols : MemoryGlobalCols (ZMod p)) :
    List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p)) :=
  []

/-! ## `Assertion` — Phase 1 scaffold of the full sub-circuit composition

Promotes `MemoryGlobalCols` from a column-struct stub to a partial
`FormalAssertion`, mirroring the upstream Rust constraint shape
(`crates/core/machine/src/memory/global.rs:300-460`). Composes the
sub-operations whose Clean wrappers exist + whose column layouts fit the
current `MemoryGlobalCols` struct:

- 10 `ByteOpcodeTable` u16 range-check lookups on `value` (4 limbs),
  `prev_addr` (3 limbs), `addr` (3 limbs).
- Inline `assertZero` for the third-limb decomposition
  `value[2] = value_lower + 256 * value_upper`.
- 2 `ByteOpcodeTable` u8 range-check lookups on `value_lower`/`upper`.
- 2× `SP1Clean.IsZeroOp.Assertion.assertion` — one on
  `prev_addr.sum`, one on `index`. Witness columns: `is_prev_addr_zero[0]`
  = inverse, `is_prev_addr_zero[1]` = result (symmetric for `is_index_zero`).
- Inline `assertZero` for the `is_comp` composition equation, the
  `is_comp` binary gate, and the `is_real` binary gate.

**Deferred to Phase 4.5** (struct expansion required, documented in the
soundness sorry):

- `LtUnsignedOp.Assertion.assertion` for `prev_addr < addr` monotonicity.
  Current `lt_cols : Vector T 6` is missing the 2 `comparison_limbs` fields
  that `LtUnsignedOp.Assertion.Inputs` requires (8 columns total). Phase
  4.5 lifts `lt_cols` to 8 fields and threads `prev_addr.push 0` /
  `addr.push 0` (3→4 limb padding) through `LtUnsignedOp.assertion`.
- `when(is_comp).assert_one(lt_cols.u16_compare_operation.bit)` —
  depends on the expanded `lt_cols` layout.
- `when(is_not_comp)`-gated zero asserts on `addr` / `value` for the
  boundary-row x0 special case.

Soundness / completeness are `sorry` placeholders matching the
`LoadByte.AssertionGated` initial-commit pattern. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var MemoryGlobalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, _clk_low, index, prev_addr, addr, _lt_cols, value,
       value_lower, value_upper, is_real, is_comp, _prev_valid,
       is_prev_addr_zero, is_index_zero⟩ := cols
  let one_expr : Expression (ZMod p) := 1
  -- `is_real` binary gate.
  is_real * (is_real - one_expr) === 0
  -- u16 range checks on `value` (4 limbs).
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value[0], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value[1], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value[2], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value[3], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  -- u16 range checks on `prev_addr` (3 limbs).
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), prev_addr[0], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), prev_addr[1], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), prev_addr[2], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  -- u16 range checks on `addr` (3 limbs).
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), addr[0], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), addr[1], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), addr[2], 16, 0] :
    Vector (Expression (ZMod p)) 4)
  -- Third-limb decomposition: `value[2] = value_lower + 256 * value_upper`.
  (value[2] - (value_lower + (256 : Expression (ZMod p)) * value_upper)) === 0
  -- u8 range checks on `value_lower`, `value_upper`.
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value_lower, 8, 0] :
    Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[(6 : Expression (ZMod p)), value_upper, 8, 0] :
    Vector (Expression (ZMod p)) 4)
  -- IsZero check on `prev_addr` (sum of 3 limbs).
  SP1Clean.IsZeroOp.assertion
    (⟨prev_addr[0] + prev_addr[1] + prev_addr[2],
      is_prev_addr_zero[0], is_prev_addr_zero[1]⟩ :
      Var SP1Clean.IsZeroOp.Assertion.Inputs (ZMod p))
  -- IsZero check on `index`.
  SP1Clean.IsZeroOp.assertion
    (⟨index, is_index_zero[0], is_index_zero[1]⟩ :
      Var SP1Clean.IsZeroOp.Assertion.Inputs (ZMod p))
  -- `is_comp = is_real * (1 - is_prev_addr_zero.result * is_index_zero.result)`.
  (is_comp - is_real *
    (one_expr - is_prev_addr_zero[1] * is_index_zero[1])) === 0
  -- `is_comp` binary gate.
  is_comp * (is_comp - one_expr) === 0

set_option maxHeartbeats 800000 in
-- 14 inline gates + 12 lookups + 2 IsZero sub-circuits; default
-- `localLength_eq` synthesis exceeds the 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) MemoryGlobalCols unit where
  name := "SP1Clean.MemoryGlobal"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

def Assumptions (_ : MemoryGlobalCols (ZMod p)) : Prop := True

/-- u8 range bound from a `ByteOpcodeSpec #v[6, x, 8, 0]` (opcode 6 = Range,
bound 8). Specializes `AddOp.Assertion.byteOpcodeSpec_range` from `< 2 ^
(8 : ZMod p).val` to `< 256`. -/
private lemma val_8_eq : (8 : ZMod p).val = 8 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (8 : ZMod p) = ((8 : ℕ) : ZMod p) from by push_cast; rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]

private lemma byteOpcodeSpec_range8
    (x : ZMod p) (h : SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 8, 0])) :
    x.val < 256 := by
  have h' := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range _ _ _ h
  rw [val_8_eq] at h'
  exact h'

private lemma byteOpcodeSpec_range8_of_lt
    (x : ZMod p) (hx : x.val < 256) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 8, 0]) := by
  apply SP1Clean.AddOp.Assertion.byteOpcodeSpec_range_of_lt
  rw [val_8_eq]
  exact hx

/-- Soundness against the Phase-1 `main` (range checks + third-limb
decomposition + the two `IsZeroOp` arms + `is_comp`/`is_real` gates). The
`LtUnsignedOp` monotonicity conjuncts are not part of this `FormalSpec`
(deferred to Phase 4.5). Mirrors the `LoadX0`/`AddressShape` raw-lookup
discharge pattern. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_clk_high, h_clk_low, h_index, h_prev_addr, h_addr, h_lt_cols,
          h_value, h_value_lower, h_value_upper, h_is_real, h_is_comp,
          h_prev_valid, h_is_prev_addr_zero, h_is_index_zero⟩ := h_input
  subst_eqs
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_ir_gate, h_v0, h_v1, h_v2, h_v3, h_pa0, h_pa1, h_pa2,
          h_a0, h_a1, h_a2, h_decomp, h_vl, h_vu, h_isz_pa, h_isz_idx,
          h_iscomp_eq, h_iscomp_bin⟩ := h_holds
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · binary_iff h_ir_gate
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_v0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_v1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_v2
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_v3
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_pa0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_pa1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_pa2
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_a0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_a1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_a2
  · linear_combination h_decomp
  · exact byteOpcodeSpec_range8 _ h_vl
  · exact byteOpcodeSpec_range8 _ h_vu
  · exact h_isz_pa trivial
  · exact h_isz_idx trivial
  · linear_combination h_iscomp_eq
  · binary_iff h_iscomp_bin

/-- Completeness against the Phase-1 `main`. Mirrors soundness; the
`FormalSpec` conjuncts feed each lookup / sub-circuit / gate emission. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_clk_high, h_clk_low, h_index, h_prev_addr, h_addr, h_lt_cols,
          h_value, h_value_lower, h_value_upper, h_is_real, h_is_comp,
          h_prev_valid, h_is_prev_addr_zero, h_is_index_zero⟩ := h_input
  subst_eqs
  simp only [FormalSpec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨h_ir_or, h_v0, h_v1, h_v2, h_v3, h_pa0, h_pa1, h_pa2,
          h_a0, h_a1, h_a2, h_decomp, h_vl, h_vu, h_isz_pa, h_isz_idx,
          h_iscomp_eq, h_iscomp_bin⟩ := h_spec
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h_ir_or with h | h <;> rw [h] <;> ring
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_v0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_v1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_v2
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_v3
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_pa0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_pa1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_pa2
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_a0
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_a1
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_a2
  · linear_combination h_decomp
  · exact byteOpcodeSpec_range8_of_lt _ h_vl
  · exact byteOpcodeSpec_range8_of_lt _ h_vu
  · exact ⟨trivial, h_isz_pa⟩
  · exact ⟨trivial, h_isz_idx⟩
  · linear_combination h_iscomp_eq
  · rcases h_iscomp_bin with h | h <;> rw [h] <;> ring

end Assertion

/-- The Phase 1 scaffold `FormalAssertion` for `MemoryGlobal`. -/
def assertion : FormalAssertion (ZMod p) MemoryGlobalCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.MemoryGlobal
