import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Proofs.Operations.IsZeroWordOperation.Formal
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal
import SP1Clean.Extracted.DivRemChip
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `DivRemCompare` — the DivRem chip's comparison/sign assertion cluster

A structural extract of the `DivRemChip` `main`'s fifteen comparison/sign `assertion` compositions,
as a standalone Clean `FormalAssertion` over the **whole committed row** (`Extracted.DivRemCols`).
The cluster witnesses nothing — every column it constrains is a field of the input `cols` — so its
`localLength` is `0` and its semantic content is exactly the composed sub-operations' `Spec`s:

* `IsEqualWordOperation` ×4 — signed-overflow detection: `op_b` read vs `i64::MIN` and `op_c` read
  vs `-1`, full-word gated by `is_real_not_word` and low-half gated by the word-variant flag sum
  `e2 = is_divw + is_remw + is_divuw + is_remuw`;
* `IsZeroWordOperation` ×1 — divide-by-zero detection on the operand `c`, gated by `is_real`;
* `AddOperation` ×2 — the `|c|` and `|remainder|` two's-complement negations
  (`c + abs_c ≡ c_neg_operation.value`, `remainder_comp + abs_remainder ≡ rem_neg_operation.value`),
  gated by `abs_c_alu_event` / `abs_rem_alu_event`;
* `LtOperationUnsigned` ×1 — the Euclidean range check `|remainder| < max(|c|, 1)`, gated by
  `remainder_check_multiplicity`;
* `U16MSBOperation` ×7 — the `b`/`c`/`remainder` high-u16 sign bits (@ `is_real_not_word`) and the
  `b`/`c`/`remainder`/`quotient` low-half sign bits (@ `e2`).

The assertion arguments are verbatim from `Proofs/Chips/DivRemChip/Defs.lean` `main` (lines
296–309, 337–338, 356–357, 376–382), with each witnessed local replaced by the corresponding
`DivRemCols` field per the chip's cols assembly. The semantic contract is
`DivRemCompare.CompareSpec` (`FormalModel/Contracts/DivRem.lean`); the `FormalAssertion` bundle is
`Proofs/Operations/DivRemOperation/Compare.lean`. -/

namespace SP1Clean.DivRemCompare

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Emit the fifteen comparison/sign assertions of the DivRem row, each a true Clean `assertion`
composition applied to the committed `cols` fields. No witnesses, no direct interactions — all
channel activity (the sub-operations' byte-range pulls) lives inside the composed subcircuits. -/
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let bpv := cols.adapter.op_b_memory.prev_value
  let cpv := cols.adapter.op_c_memory.prev_value
  let irnw := cols.is_real_not_word
  let e2 := cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  -- (1-4) signed-overflow detection: `b` vs `i64::MIN`, `c` vs `-1` — full-word @ `irnw`,
  -- low-half @ `e2` (word variants).
  assertion IsEqualWordOperation.circuit
    ⟨#v[bpv[0], bpv[1], bpv[2], bpv[3]], #v[0, 0, 0, 32768], cols.is_overflow_b, irnw⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[cpv[0], cpv[1], cpv[2], cpv[3]], #v[65535, 65535, 65535, 65535], cols.is_overflow_c, irnw⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[bpv[0], bpv[1], 0, 0], #v[0, 32768, 0, 0], cols.is_overflow_b, e2⟩
  assertion IsEqualWordOperation.circuit
    ⟨#v[cpv[0], cpv[1], 0, 0], #v[65535, 65535, 0, 0], cols.is_overflow_c, e2⟩
  -- (5) divide-by-zero detection on the committed operand `c`.
  assertion IsZeroWordOperation.circuit ⟨cols.c, cols.is_c_0, cols.is_real⟩
  -- (6-7) the `|c|` and `|remainder|` two's-complement negations.
  assertion AddOperation.circuit
    ⟨cols.c, cols.abs_c, ⟨cols.c_neg_operation.value⟩, cols.abs_c_alu_event⟩
  assertion AddOperation.circuit
    ⟨cols.remainder_comp, cols.abs_remainder, ⟨cols.rem_neg_operation.value⟩,
     cols.abs_rem_alu_event⟩
  -- (8) the Euclidean remainder range check `|remainder| < max(|c|, 1)`.
  assertion LtOperationUnsigned.circuit
    ⟨cols.abs_remainder, cols.max_abs_c_or_1, cols.remainder_lt_operation,
     cols.remainder_check_multiplicity⟩
  -- (9-15) sign-bit extractions: b/c/remainder high u16 (@ `irnw`), b/c/remainder/quotient
  -- low-half-high u16 (@ `e2`).
  assertion U16MSBOperation.circuit ⟨bpv[3], cols.b_msb, irnw⟩
  assertion U16MSBOperation.circuit ⟨cpv[3], cols.c_msb, irnw⟩
  assertion U16MSBOperation.circuit ⟨cols.remainder[3], cols.rem_msb, irnw⟩
  assertion U16MSBOperation.circuit ⟨bpv[1], cols.b_msb, e2⟩
  assertion U16MSBOperation.circuit ⟨cpv[1], cols.c_msb, e2⟩
  assertion U16MSBOperation.circuit ⟨cols.remainder[1], cols.rem_msb, e2⟩
  assertion U16MSBOperation.circuit ⟨cols.quotient[1], cols.quot_msb, e2⟩

set_option maxHeartbeats 4000000 in
/-- Clean derives the structural metadata; the cluster contributes no fresh witnesses
(`localLength = 0`) and exposes only the sub-operations' byte-channel guarantees. -/
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var DivRemCols (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.DivRemCompare
