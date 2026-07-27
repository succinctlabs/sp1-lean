import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal
import SP1Clean.Proofs.Operations.U16MSBOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Equality
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `LtOperationSigned` native circuit

The proof-oriented Clean implementation, composed with the native unsigned and MSB gadgets. -/

namespace SP1Clean.LtOperationSigned

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Extracted

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let cc := input.cc
  let cols := input.cols
  let is_signed := input.is_signed
  let is_real := input.is_real
  let E0 := is_signed - 1
  let E1 := is_signed * E0
  let E2 := is_real - 1
  let E3 := is_real * E2
  let E4 := is_real - 1
  let E5 := E4 * is_signed
  let E6 := is_signed - 1
  let E7 := E6 * cols.b_msb.msb
  let E8 := is_signed - 1
  let E9 := E8 * cols.c_msb.msb
  let E10 := is_signed * 32768
  let E11 := b[3] + E10
  let E12 := 65536 * cols.b_msb.msb
  let E13 := E11 - E12
  let E14 := is_signed * 32768
  let E15 := cc[3] + E14
  let E16 := 65536 * cols.c_msb.msb
  let E17 := E15 - E16
  assertion U16MSBOperation.circuit ⟨b[3], { msb := cols.b_msb.msb }, is_signed⟩
  assertion U16MSBOperation.circuit ⟨cc[3], { msb := cols.c_msb.msb }, is_signed⟩
  assertion LtOperationUnsigned.circuit ⟨#v[b[0], b[1], b[2], E13], #v[cc[0], cc[1], cc[2], E17], { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }, u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1], cols.result.u16_flags[2], cols.result.u16_flags[3]], not_eq_inv := cols.result.not_eq_inv, comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] }, is_real⟩
  E1 === 0
  E3 === 0
  E5 === 0
  E7 === 0
  E9 === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- Keep the signed-compare interaction boundary folded for enclosing whole-chip proofs.  The gadget
emits only the byte interactions of its two MSB checks and unsigned comparison; its five local
equalities emit none. -/
theorem interactionsWith_byte_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      ((U16MSBOperation.main
        ⟨input.b[3], { msb := input.cols.b_msb.msb },
          input.is_signed⟩).operations offset).interactionsWith
            byteChannel.toRaw ++
      ((U16MSBOperation.main
        ⟨input.cc[3], { msb := input.cols.c_msb.msb },
          input.is_signed⟩).operations offset).interactionsWith
            byteChannel.toRaw ++
      ((LtOperationUnsigned.main
        ⟨#v[input.b[0], input.b[1], input.b[2],
              input.b[3] + input.is_signed * 32768 -
                65536 * input.cols.b_msb.msb],
          #v[input.cc[0], input.cc[1], input.cc[2],
              input.cc[3] + input.is_signed * 32768 -
                65536 * input.cols.c_msb.msb],
          { u16_compare_operation :=
              { bit := input.cols.result.u16_compare_operation.bit }
            u16_flags :=
              #v[input.cols.result.u16_flags[0],
                input.cols.result.u16_flags[1],
                input.cols.result.u16_flags[2],
                input.cols.result.u16_flags[3]]
            not_eq_inv := input.cols.result.not_eq_inv
            comparison_limbs :=
              #v[input.cols.result.comparison_limbs[0],
                input.cols.result.comparison_limbs[1]] },
          input.is_real⟩).operations offset).interactionsWith
            byteChannel.toRaw := by
  simp only [main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    U16MSBOperation.circuit, LtOperationUnsigned.circuit,
    Gadgets.Equality.main, List.filter_nil, List.append_nil]
  rfl

end SP1Clean.LtOperationSigned
