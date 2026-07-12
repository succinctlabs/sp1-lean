import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Proofs.Chips.DivRemChip.Soundness
import SP1Clean.Proofs.Chips.DivRemChip.Assembly
import SP1Clean.Proofs.Chips.DivRemChip.Soundness.Tail

/-! # `DivRemChip` — reader sub-`Spec` + `is_real`-binary (split for parallel compilation)

The `RTypeReader` register-reader sub-`Spec` (register reads/write, gated by the flag-weighted R-type opcode
and the result `cols.a` as the `op_a` write value) and the proven `is_real`-binary fact — the two
non-arithmetic conjuncts of `DivRemChip.Spec`, proved as a standalone `GeneralFormalCircuit.Soundness` over a
local two-conjunct `Spec`, the same split-for-parallel-compilation shape as the eight per-variant files.
`Formal.lean`'s top-level soundness reuses `.1` from here for the reader + binary conjuncts. The
`h_holds`/`h_own` destructure and the `?_tail` (`Operations.Requirements`) are the verbatim shared pieces from
the per-variant files; only the `?_spec` bullet differs (the reader guarantee `h_rtype` fed the binary gate
`E355`, plus the binary itself). -/

namespace SP1Clean.DivRemChip.SoundReader

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- The `RTypeReader` reader sub-`Spec` ∧ the `is_real`-binary fact, as a standalone spec. -/
def Spec (input : Inputs (ZMod p)) (cols : DivRemCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.RTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc,
      opcode := cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
        + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28,
      wv0 := cols.a[0], wv1 := cols.a[1], wv2 := cols.a[2], wv3 := cols.a[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1)

-- 4.30 fix: `eval_fromElements` at high `circuit_norm` priority reduces the witnessed `cols` output struct
-- (mirrors `Tail.lean`/`Div.lean`; Reader lacked it). Combined with stock `circuit_proof_start` (which
-- reduces the goal, unlike the custom `spec_proof_start`), this collapses the 610K goal that timed out.
attribute [local circuit_norm ↓ 100000] ProvableType.eval_fromElements

set_option maxHeartbeats 128000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
/-- Soundness of the reader sub-`Spec` + `is_real`-binary conjuncts. MIGRATION-DEFERRED (`stop`): the body
below is a **WIP, unverified** restructure — stock `circuit_proof_start` + `requirements_holds.2`, retiring the
custom `soundness_of_specObligation`/`spec_proof_start` path — which type-checks structurally but did NOT finish
within a 45-min build (the goal-side witnessed-`cols` reduction is too heavy for DivRem's circuit on 4.30; see
docs/proposals/consolidation-progress.md). Kept as the documented intended approach; the real unblock is likely
the `DivRemOperation` structural extract. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  stop
  circuit_proof_start
  refine ⟨?_, (requirements_holds i₀ env input_var input h_input h_assumptions h_holds).2⟩
  -- `op_b_val`/`op_c_val` are the raw register reads; `hbU`/`hcU` are their `isU64`.
  have hbU := h_assumptions.1
  have hcU := h_assumptions.2
  -- The `h_holds`/`h_own` constraint conjunctions are destructured in CHUNKS: `obtain` cost is
  -- super-linear (~quadratic) in field count, so splitting the 63-/121-field lists into blocks of
  -- ~32/~41 collapses the elaboration time (the whole-list `obtain` blew past 100M heartbeats). All
  -- names stay bound, so the per-variant arithmetic proofs are unaffected. (see build_timeout_smell_test /
  -- compile_bottlenecks memory: "split the big obtain — surprisingly big win".)
  obtain ⟨h_mul_lo, h_mul_hi, h_ctq0, h_ctq1, h_ctq2, h_ctq3, h_ctq4, h_ctq5,
    h_ctq6, h_ctq7, h_eqb, h_eqc, h_eqb2, h_eqc2, h_isc0, h_addc,
    h_addr, h_lt, h_msb0, h_msb1, h_msb2, h_msb3, h_msb4, h_msb5,
    h_msb6, h_cpu, h_rtype, h_own, hb_e123, hb_e127, hb_e131, hb_e135,
    hrest1⟩ := h_holds
  obtain ⟨hb_e139, hb_e143, hb_e147, hb_e151, hb_absc0, hb_absc1, hb_absc2, hb_absc3,
    hb_absr0, hb_absr1, hb_absr2, hb_absr3, hb_q0, hb_q1, hb_q2, hb_q3,
    hb_r0, hb_r1, hb_r2, hb_r3, hb_ctq0, hb_ctq1, hb_ctq2, hb_ctq3,
    hb_ctq4, hb_ctq5, hb_ctq6, hb_ctq7, hb_e2r1, hb_e2q1, _h_regwrite⟩ := hrest1
  simp only [ownAsserts] at h_own
  obtain ⟨e13, e15, e17, e19, e20, e21, e22, e23,
    e29, e35, e41, e47, e48, e49, e51, e54,
    e57, e59, e61, e64, e67, e69, e70, e71,
    e73, e76, e79, e81, e83, e86, e89, e91,
    e96, e99, e103, e105, e107, e109, e111, e113,
    e115, orest1⟩ := h_own
  obtain ⟨e117, e119, e154, e157, e160, e163, e167, e171,
    e175, e179, e184, e189, e194, e199, e204, e209,
    e214, e219, e225, e228, e230, e232, e234, e236,
    e238, e240, e242, e244, e247, e250, e253, e256,
    e259, e262, e265, e268, e270, e272, e274, e276,
    e278, orest2⟩ := orest1
  obtain ⟨e280, e282, e284, e286, e288, e299, e300, e301,
    e302, e305, e307, e309, e311, e313, e315, e317,
    e319, e321, e323, e325, e327, e329, e331, e333,
    e335, e337, e339, e341, e343, e345, e347, e349,
    e351, e353, e355, e357, e359, e367, eopa0⟩ := orest2
  · -- reader sub-`Spec` (`h_rtype` guarantee, its `circuit.Spec` projection unfolded) ∧ `is_real`-binary
    -- (the gate `E355`, per `Defs.lean`).
    obtain ⟨h_oir, -⟩ := h_input
    have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
      have h := e355; simp only [circuit_norm] at h; rw [h_oir] at h; exact bool_of_mul_pred h
    have hr := h_rtype ⟨h_bin, h_bin⟩
    simp only [Readers.RTypeReader.circuit] at hr
    exact ⟨hr, h_bin⟩


end SP1Clean.DivRemChip.SoundReader
