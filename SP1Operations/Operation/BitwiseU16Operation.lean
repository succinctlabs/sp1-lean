import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.BitwiseOperation
import SP1Operations.Operation.BitwiseU16Operation.Operation
import SP1Operations.Operation.BitwiseU16Operation.Constraints

set_option maxHeartbeats 10000000

namespace BitwiseU16Operation

lemma spec.and
  (b cc : Word (Fin BB))
  (cols : BitwiseU16Operation)
  (opcode : Fin BB)
  (is_real : Fin BB) :
    opcode = 0 → is_real = 1 →
    List.Forall SP1Constraint.toProp (constraints b cc cols opcode is_real).2 →
    b.isU64 → cc.isU64 →
    Word.toBitVec64 (constraints b cc cols 1 is_real).1 = execute_RTYPE_pure_w b cc .AND
      := by
    intro op_and real cstrs is_U64_b is_U64_cc; subst_eqs
    have h_bw_b := U16toU8OperationSafe.spec.unsafe.return b { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1], cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    have h_bw_c := U16toU8OperationSafe.spec.unsafe.return cc { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1], cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    rotate_left
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [U16toU8OperationUnsafe.constraints, Word.toBWord] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := h_bw_b
      obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7 ⟩ := h_bw_c
      simp_all [constraints, U16toU8OperationUnsafe.constraints]
      simp [BitwiseOperation.constraints] at cstrs
      have ⟨ ⟨ ⟨ hr0, hb0, hc0 ⟩, heq_0 ⟩, ⟨ ⟨ hr1, hb1, hc1 ⟩, heq_1 ⟩, ⟨ ⟨ hr2, hb2, hc2 ⟩, heq_2 ⟩,  ⟨ ⟨ hr3, hb3, hc3 ⟩, heq_3 ⟩,
             ⟨ ⟨ hr4, hb4, hc4 ⟩, heq_4 ⟩, ⟨ ⟨ hr5, hb5, hc5 ⟩, heq_5 ⟩, ⟨ ⟨ hr6, hb6, hc6 ⟩, heq_6 ⟩,  ⟨ ⟨ hr7, hb7, hc7 ⟩, heq_7 ⟩  ⟩ := cstrs
      rw [Word.and_toBWord is_U64_b is_U64_cc]
      simp [Word.toBitVec64, Word.toNat, Word.toBWord, BWord.toBitVec64, BWord.toNat]
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      rw [Fin.lt_iff_val_lt_val, Fin.mod_val] at hb0 hc0 hb2 hc2 hb4 hc4 hb6 hc6
      rw [Fin.lt_iff_val_lt_val, Fin.div_val] at hb1 hc1 hb3 hc3 hb5 hc5 hb7 hc7
      simp_all
      set b0 := b[0].val % 256; set b1 := b[0].val / 256; set b2 := b[1].val % 256; set b3 := b[1].val / 256
      set b4 := b[2].val % 256; set b5 := b[2].val / 256; set b6 := b[3].val % 256; set b7 := b[3].val / 256
      set c0 := cc[0].val % 256; set c1 := cc[0].val / 256; set c2 := cc[1].val % 256; set c3 := cc[1].val / 256
      set c4 := cc[2].val % 256; set c5 := cc[2].val / 256; set c6 := cc[3].val % 256; set c7 := cc[3].val / 256
      simp [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_and]
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      bv_decide

lemma spec.or
  (b cc : Word (Fin BB))
  (cols : BitwiseU16Operation)
  (opcode : Fin BB)
  (is_real : Fin BB) :
    opcode = 1 → is_real = 1 →
    List.Forall SP1Constraint.toProp (constraints b cc cols opcode is_real).2 →
    b.isU64 → cc.isU64 →
    Word.toBitVec64 (constraints b cc cols 1 is_real).1 = execute_RTYPE_pure_w b cc .OR
      := by
    intro op_or real cstrs is_U64_b is_U64_cc; subst_eqs
    have h_bw_b := U16toU8OperationSafe.spec.unsafe.return b { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1], cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    have h_bw_c := U16toU8OperationSafe.spec.unsafe.return cc { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1], cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    rotate_left
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [U16toU8OperationUnsafe.constraints, Word.toBWord] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := h_bw_b
      obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7 ⟩ := h_bw_c
      simp_all [constraints, U16toU8OperationUnsafe.constraints]
      simp [BitwiseOperation.constraints] at cstrs
      have ⟨ ⟨ ⟨ hr0, hb0, hc0 ⟩, heq_0 ⟩, ⟨ ⟨ hr1, hb1, hc1 ⟩, heq_1 ⟩, ⟨ ⟨ hr2, hb2, hc2 ⟩, heq_2 ⟩,  ⟨ ⟨ hr3, hb3, hc3 ⟩, heq_3 ⟩,
             ⟨ ⟨ hr4, hb4, hc4 ⟩, heq_4 ⟩, ⟨ ⟨ hr5, hb5, hc5 ⟩, heq_5 ⟩, ⟨ ⟨ hr6, hb6, hc6 ⟩, heq_6 ⟩,  ⟨ ⟨ hr7, hb7, hc7 ⟩, heq_7 ⟩  ⟩ := cstrs
      rw [Word.or_toBWord is_U64_b is_U64_cc]
      simp [Word.toBitVec64, Word.toNat, Word.toBWord, BWord.toBitVec64, BWord.toNat]
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      rw [Fin.lt_iff_val_lt_val, Fin.mod_val] at hb0 hc0 hb2 hc2 hb4 hc4 hb6 hc6
      rw [Fin.lt_iff_val_lt_val, Fin.div_val] at hb1 hc1 hb3 hc3 hb5 hc5 hb7 hc7
      simp_all
      set b0 := b[0].val % 256; set b1 := b[0].val / 256; set b2 := b[1].val % 256; set b3 := b[1].val / 256
      set b4 := b[2].val % 256; set b5 := b[2].val / 256; set b6 := b[3].val % 256; set b7 := b[3].val / 256
      set c0 := cc[0].val % 256; set c1 := cc[0].val / 256; set c2 := cc[1].val % 256; set c3 := cc[1].val / 256
      set c4 := cc[2].val % 256; set c5 := cc[2].val / 256; set c6 := cc[3].val % 256; set c7 := cc[3].val / 256
      simp [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_or]
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      bv_decide

lemma spec.xor
  (b cc : Word (Fin BB))
  (cols : BitwiseU16Operation)
  (opcode : Fin BB)
  (is_real : Fin BB) :
    opcode = 2 → is_real = 1 →
    List.Forall SP1Constraint.toProp (constraints b cc cols opcode is_real).2 →
    b.isU64 → cc.isU64 →
    Word.toBitVec64 (constraints b cc cols 1 is_real).1 = execute_RTYPE_pure_w b cc .XOR
      := by
    intro op_xor real cstrs is_U64_b is_U64_cc; subst_eqs
    have h_bw_b := U16toU8OperationSafe.spec.unsafe.return b { low_bytes := #v[cols.b_low_bytes.low_bytes[0], cols.b_low_bytes.low_bytes[1], cols.b_low_bytes.low_bytes[2], cols.b_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    have h_bw_c := U16toU8OperationSafe.spec.unsafe.return cc { low_bytes := #v[cols.c_low_bytes.low_bytes[0], cols.c_low_bytes.low_bytes[1], cols.c_low_bytes.low_bytes[2], cols.c_low_bytes.low_bytes[3]] } 1 ?_ (by trivial)
    rotate_left
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [constraints, U16toU8OperationUnsafe.constraints, U16toU8OperationSafe.constraints] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := cstrs
      norm_num at *
      aesop
    . simp [U16toU8OperationUnsafe.constraints, Word.toBWord] at *
      obtain ⟨ b0, b1, b2, b3, b4, b5, b6, b7 ⟩ := h_bw_b
      obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7 ⟩ := h_bw_c
      simp_all [constraints, U16toU8OperationUnsafe.constraints]
      simp [BitwiseOperation.constraints] at cstrs
      have ⟨ ⟨ ⟨ hr0, hb0, hc0 ⟩, heq_0 ⟩, ⟨ ⟨ hr1, hb1, hc1 ⟩, heq_1 ⟩, ⟨ ⟨ hr2, hb2, hc2 ⟩, heq_2 ⟩,  ⟨ ⟨ hr3, hb3, hc3 ⟩, heq_3 ⟩,
             ⟨ ⟨ hr4, hb4, hc4 ⟩, heq_4 ⟩, ⟨ ⟨ hr5, hb5, hc5 ⟩, heq_5 ⟩, ⟨ ⟨ hr6, hb6, hc6 ⟩, heq_6 ⟩,  ⟨ ⟨ hr7, hb7, hc7 ⟩, heq_7 ⟩  ⟩ := cstrs
      rw [Word.xor_toBWord is_U64_b is_U64_cc]
      simp [Word.toBitVec64, Word.toNat, Word.toBWord, BWord.toBitVec64, BWord.toNat]
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      rw [Fin.lt_iff_val_lt_val, Fin.mod_val] at hb0 hc0 hb2 hc2 hb4 hc4 hb6 hc6
      rw [Fin.lt_iff_val_lt_val, Fin.div_val] at hb1 hc1 hb3 hc3 hb5 hc5 hb7 hc7
      simp_all
      set b0 := b[0].val % 256; set b1 := b[0].val / 256; set b2 := b[1].val % 256; set b3 := b[1].val / 256
      set b4 := b[2].val % 256; set b5 := b[2].val / 256; set b6 := b[3].val % 256; set b7 := b[3].val / 256
      set c0 := cc[0].val % 256; set c1 := cc[0].val / 256; set c2 := cc[1].val % 256; set c3 := cc[1].val / 256
      set c4 := cc[2].val % 256; set c5 := cc[2].val / 256; set c6 := cc[3].val % 256; set c7 := cc[3].val / 256
      simp [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_xor]
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      rw [Nat.lift_lt 64 (by omega) (by omega)] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      bv_decide
