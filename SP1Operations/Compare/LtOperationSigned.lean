import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Compare.LtOperationSigned.Constraints

namespace LtOperationSigned

def spec_for_branch
  (b : (Word (Fin BB)))
  (cc : (Word (Fin BB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin BB))
  : Prop :=
  let bv := b.toBitVec64
  let cv := cc.toBitVec64
  (is_signed = 0 → 
    (bv = cv
      ↔ (cols.result.u16_flags[0] = 0
        ∧ cols.result.u16_flags[1] = 0
        ∧ cols.result.u16_flags[2] = 0
        ∧ cols.result.u16_flags[3] = 0))
    ∧ (bv ≠ cv
        ↔ cols.result.u16_flags[0]
          + cols.result.u16_flags[1]
          + cols.result.u16_flags[2]
          + cols.result.u16_flags[3] = 1)
    ∧ if BitVec.ult bv cv
      then (cols.result.u16_compare_operation.bit = 1)
      else (cols.result.u16_compare_operation.bit = 0))
  ∧ (is_signed = 1 →
      (bv = cv
        ↔ (cols.result.u16_flags[0] = 0
          ∧ cols.result.u16_flags[1] = 0
          ∧ cols.result.u16_flags[2] = 0
          ∧ cols.result.u16_flags[3] = 0))
      ∧ (bv ≠ cv
          ↔ cols.result.u16_flags[0]
            + cols.result.u16_flags[1]
            + cols.result.u16_flags[2]
            + cols.result.u16_flags[3] = 1)
      ∧ if BitVec.slt bv cv
        then (cols.result.u16_compare_operation.bit = 1)
        else (cols.result.u16_compare_operation.bit = 0))

axiom correct_for_branch
  (b : (Word (Fin BB)))
  (cc : (Word (Fin BB)))
  (cols : LtOperationSigned)
  (is_signed : (Fin BB))
  (is_real : Fin BB)
  (cstrs : (constraints b cc cols is_signed is_real).allHold)
  (h_is_real : is_real = 1)
  : b.isU64 → cc.isU64 → spec_for_branch b cc cols is_signed

end LtOperationSigned
