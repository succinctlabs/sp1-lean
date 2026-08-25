import SP1Clean.Proofs.Chips.AluX0Chip.Formal
import ToClean.Circuit.WitgenBridge

/-! # `SP1Clean.AluX0Chip` — honest witness generation (`ComputableWitnesses`)

The degenerate case of the witgen bridge (see `AddChip/Witgen.lean` for the programme note), and
the only chip of the machine for which it is degenerate: `AluX0` **witnesses nothing**. Its row is
its threaded input — the CPUState block, the ALU-type adapter block, the dynamic `opcode` column
and the `is_real` selector — and the chip's `elaborated` instance records that with
`localLength _ := 0`. The result register is `x0`, whose write is discarded, so there is no
arithmetic gadget to run and no result word to generate.

The obligation is therefore one dispatch per composed subcircuit (the `CPUState` reader and the
`ALUTypeReaderImmutable` adapter, both `localLength 0` assertions), with nothing in between. -/

namespace SP1Clean.AluX0Chip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- AluX0's row has computable witnesses, vacuously: the row has no witnessed cells at all. -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := by
  intro n input env env'
  simp only [circuit, main, circuit_norm, Operations.forAllFlat, Operations.forAll]
  refine ⟨FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_,
    FlatOperation.forAll_witnessCongr_of_subcircuit _ _ ?_⟩ <;>
    simp [circuit_norm, Readers.ALUTypeReaderImmutable.circuit]

end SP1Clean.AluX0Chip
