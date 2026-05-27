import SP1Clean.Chips.ALU.AddiChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `AddiChip` Clean circuit + `FormalAssertion`

Wraps the chip-level constraint surface into a single Clean `FormalAssertion`
whose `Spec` is the unified semantic-and-structural contract:
- `CPUState.Gated.Assertion.Spec` — flag-threaded CPU-state composition.
- `ITypeReader.Gated.Assertion.Spec` — flag-threaded I-type reader.
- `op_a_0 = 0` scalar gate.
- Semantic RV64 conjunct (conditional on `is_real = 1`): the result fits
  in 64 bits AND equals `RV64.addi (signExt12 imm[0]) op_b.toBitVec64`.
  The byte-carry decomposition is the implementation detail of the
  `AddOp` sub-circuit and is reconstructed on demand via
  `SP1Clean.AddOp.iff_sp1_full` (see `Lemmas.lean`).

`Assertion.main` composes four subcircuits — `AddOp.assertion`,
`CPUState.Gated.assertion`, `ITypeReader.Gated.assertion` (the last itself
wrapping `ProgramTable.assertion` + 2 `OperandAccess.assertion` calls) +
the chip-level `op_a_0 === 0` gate — mirroring
`SP1Chips/Addi/Constraints.lean`'s single `ITypeReader.constraints` call
and the upstream Rust `AddiChip::eval`'s `ITypeReader::eval` invocation 1:1.

The per-row Sail-monadic equivalence to `_root_.Addi.spec_addi` is *not*
inside `FormalSpec`; it's derived externally via
`SP1Clean.AddiChip.SailBridge.sail_correct_of_formalSpec`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. Mirrors SP1 Rust's `AddiChip::eval(builder, cols)`
1:1 via flag-threaded `Gated` sub-circuits: one `AddOp.assertion` +
one `CPUState.Gated.assertion` + one `ITypeReader.Gated.assertion`
(which bundles ProgramTable + 2 gated OperandAccess + 4 op_a_0 mask
gates) + chip-level `op_a_0 = 0` gate. The free
`is_real * (is_real - 1) === 0` gate now lives inside both Gated
sub-circuits' first conjuncts. -/
@[reducible]
def main (cols : Var AddiCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, op_a_write_value, is_real, adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨adapter.op_b_memory.prev_value, adapter.op_c_imm, op_a_write_value,
      is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ITypeReader.Gated.assertion
    (⟨clk_high, clk_0_16 + clk_16_24 * 65536, 1, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ITypeReader.Gated.Inputs (ZMod p))
  adapter.op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddiCols unit where
  name := "SP1Clean.Addi"
  main := main
  -- Computed from main; ITypeReader contributes 48 (2 assertionGated × 24).
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- The chip is the `UserMode` variant (`M = UserMode` in upstream Rust),
so its `adapter_cols.is_trusted` payload is structurally equal to `is_real`
(both alias `Main[29]` in the constraint compiler's emission). This is a
type-level / TrustMode-marker fact that the circuit doesn't enforce; it's
needed by `fromMain_toMain` (`Lemmas.lean`) for the cols→Main→cols
round-trip. The chip-level `is_real = 1` precondition is *not* in
Assumptions (unlike AddChip) — Addi's contract is meaningful for both
padding and real rows because the semantic conjunct is gated by
`is_real = 1` internally. -/
def Assumptions (cols : AddiCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_real

/-- The unified chip Spec is defined in `Cols.lean` (`SP1Clean.Addi.FormalSpec`)
so `Lemmas.lean` can reference it. Re-exported here for the
`FormalAssertion` glue. -/
abbrev FormalSpec := @SP1Clean.Addi.FormalSpec p

/-- Soundness collapses to a single application of the structural
mirror lemma `formalSpec_of_subcircuit_specs` (`Lemmas.lean`) once
`circuit_proof_start` peels back the Clean elaboration plumbing. All
sub-circuit composition logic — including the `Word.isU64 op_b`
extraction from `h_itr` via `ITypeReader.Gated.Assertion.isU64_op_b_of_spec`,
the `Word.isU64 op_c_imm` reconstruction from `ProgramSpec`'s byte
range conjunct, and the sign-extension bridge to `RV64.addi` — lives
inside the named lemma. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_itr_sub, h_op_a_0⟩ := h_holds
  unfold id at *
  -- `circuit_proof_start` has already substituted `is_trusted := is_real`
  -- into the goal via `subst_eqs` on `h_input`'s `e_ac` field, so the
  -- chip-level `h_trusted` obligation reduces to `rfl`.
  exact formalSpec_of_subcircuit_specs _ rfl
    h_addop_sub (h_cpu_sub trivial) (h_itr_sub trivial) h_op_a_0

/-- Completeness peels `h_spec` (= `FormalSpec input`) via
`subcircuit_specs_of_formalSpec` into the (AddOp Assumptions ∧ Spec)
pair plus the three remaining sub-circuit `Spec`s, then re-wraps each
as the `(Assumptions, Spec)` pair the corresponding
`FormalAssertion.completeness` expects. The same isU64/signExt bridging
that soundness needs is inside the named lemma. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e_adapter, e_oawv, e_is_real, e_ac⟩ := h_input
  subst_eqs
  unfold id at *
  obtain ⟨h_addop_pair, h_cpu, h_itr, h_op_a_0⟩ :=
    subcircuit_specs_of_formalSpec _ rfl h_spec
  exact ⟨h_addop_pair, ⟨trivial, h_cpu⟩, ⟨trivial, h_itr⟩, h_op_a_0⟩

end Assertion

/-- The full Clean `FormalAssertion` for `AddiChip`. Single subcircuit
composition (`AddOp.assertion + CPUState.assertion + ITypeReader.assertion
+ 2 scalar gates`) backing one unified `Spec` whose last conjunct is the
pure BitVec `RV64.add` semantic (auditable at a glance). Per-row Sail
equivalence is derived externally via `sail_correct_of_formalSpec`
(`SailBridge.lean`). -/
def assertion : FormalAssertion (ZMod p) AddiCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addi
