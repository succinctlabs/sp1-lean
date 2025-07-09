-- import SP1Foundations
-- import LeanRV32IM.RiscvRegs

-- open LeanRV32IM.Functions

-- @[ext] structure BitwiseOperation where
--   result : ByteWord (Fin BB)

-- namespace BitwiseOperation

-- @[ext] lemma ext_forall (op op' : BitwiseOperation)
--     (h : ∀ i : Fin WORD_BYTE_SIZE, op.result[i] = op'.result[i]) : op = op' := by
--   refine BitwiseOperation.ext ?_
--   exact ByteWord.ext_forall h

-- @[ext] lemma ext_cases (op op' : BitwiseOperation)
--     (h0 : op.result[0] = op'.result[0]) (h1 : op.result[1] = op'.result[1])
--     (h2 : op.result[2] = op'.result[2]) (h3 : op.result[3] = op'.result[3]) : op = op' := by
--   refine BitwiseOperation.ext ?_
--   exact ByteWord.ext_cases h0 h1 h2 h3

-- open ByteOpcode

-- def constraints
--   (a : ByteWord (Fin BB))
--   (b : ByteWord (Fin BB))
--   (cols : BitwiseOperation)
--   (opcode : Fin BB)
--   (is_real : Fin BB)
--   : SP1ConstraintList :=
--   [
--     .send (.byte (ByteOpcode.ofNat opcode) cols.result[0] a[0] b[0]) is_real,
--     .send (.byte (ByteOpcode.ofNat opcode) cols.result[1] a[1] b[1]) is_real,
--     .send (.byte (ByteOpcode.ofNat opcode) cols.result[2] a[2] b[2]) is_real,
--     .send (.byte (ByteOpcode.ofNat opcode) cols.result[3] a[3] b[3]) is_real
--   ]

-- def spec (a b : ByteWord (Fin BB))
--     (cols : BitwiseOperation) (opcode : Fin BB) : Prop :=
--   if ByteOpcode.ofNat opcode = .AND then (
--     ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) ∧ cols.result[0] = a[0] &&& b[0]) ∧
--     ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) ∧ cols.result[1] = a[1] &&& b[1]) ∧
--     ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) ∧ cols.result[2] = a[2] &&& b[2]) ∧
--     ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) ∧ cols.result[3] = a[3] &&& b[3])
--   ) else if ByteOpcode.ofNat opcode = .OR then (
--     ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) ∧ cols.result[0] = a[0] ||| b[0]) ∧
--     ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) ∧ cols.result[1] = a[1] ||| b[1]) ∧
--     ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) ∧ cols.result[2] = a[2] ||| b[2]) ∧
--     ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) ∧ cols.result[3] = a[3] ||| b[3])
--   ) else if ByteOpcode.ofNat opcode = .XOR then (
--     ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) ∧ cols.result[0] = a[0] ^^^ b[0]) ∧
--     ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) ∧ cols.result[1] = a[1] ^^^ b[1]) ∧
--     ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) ∧ cols.result[2] = a[2] ^^^ b[2]) ∧
--     ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) ∧ cols.result[3] = a[3] ^^^ b[3])
--   ) else True

-- lemma constraints_imp_spec (a b : ByteWord (Fin BB))
--     (cols : BitwiseOperation) (opcode is_real : Fin BB)
--     (h0 : is_real ≠ 0)
--     (h : (cols.constraints a b opcode is_real).allHold) :
--     cols.spec a b opcode := by
--   simp only [spec, constraints] at ⊢ h
--   by_cases h1 : ByteOpcode.ofNat opcode = .AND
--   · simpa [h0, h1] using h
--   by_cases h2 : ByteOpcode.ofNat opcode = .OR
--   · simpa [h0, h2] using h
--   by_cases h3 : ByteOpcode.ofNat opcode = .XOR
--   · simpa [h0, h3] using h
--   simp [h1, h2, h3]

-- lemma eq_and_of_constraints (a b : ByteWord (Fin BB)) (cols : BitwiseOperation)
--     (i : Fin WORD_BYTE_SIZE) (h : (cols.constraints a b 0 1).allHold) :
--     cols.result[i] = a[i] &&& b[i] := by
--   have := constraints_imp_spec a b cols _ _ one_ne_zero h
--   simp [spec] at this
--   match i with | 0 => aesop | 1 => aesop | 2 => aesop | 3 => aesop

-- lemma eq_or_of_constraints (a b : ByteWord (Fin BB)) (cols : BitwiseOperation)
--     (i : Fin WORD_BYTE_SIZE) (h : (cols.constraints a b 1 1).allHold) :
--     cols.result[i] = a[i] ||| b[i] := by
--   have := constraints_imp_spec a b cols _ _ one_ne_zero h
--   simp [spec] at this
--   match i with | 0 => aesop | 1 => aesop | 2 => aesop | 3 => aesop

-- lemma eq_xor_of_constraints (a b : ByteWord (Fin BB)) (cols : BitwiseOperation)
--     (i : Fin WORD_BYTE_SIZE) (h : (cols.constraints a b 2 1).allHold) :
--     cols.result[i] = a[i] ^^^ b[i] := by
--   have := constraints_imp_spec a b cols _ _ one_ne_zero h
--   simp [spec] at this
--   match i with | 0 => aesop | 1 => aesop | 2 => aesop | 3 => aesop

-- /-- Constraints on `BitwiseOperation` imply that the result is `op.toBitwise` applied to the inputs. -/
-- lemma eq_toBitwise_of_constraints (a b : ByteWord (Fin BB)) (cols : BitwiseOperation)
--     (i : Fin WORD_BYTE_SIZE) (op : ByteOpcode) (hop : op = AND ∨ op = OR ∨ op = XOR)
--     (h : (cols.constraints a b op.toBB 1).allHold) :
--     cols.result[i] = op.toBitwise a[i] b[i] := by
--   induction op using ByteOpcode.bitwise_induction with
--   | and => exact eq_and_of_constraints _ _ _ _ h
--   | or => exact eq_or_of_constraints _ _ _ _ h
--   | xor => exact eq_xor_of_constraints _ _ _ _ h
--   | other h h' => aesop

-- lemma lt_of_constraints (a b : ByteWord (Fin BB)) (cols : BitwiseOperation)
--     (i : Fin WORD_BYTE_SIZE) (op : ByteOpcode) (hop : op = AND ∨ op = OR ∨ op = XOR)
--     (h : (cols.constraints a b op.toBB 1).allHold) :
--     cols.result[i] < 256 ∧ a[i] < 256 ∧ b[i] < 256 := by
--   have := constraints_imp_spec a b cols _ _ one_ne_zero h
--   rw [spec] at this
--   match i with | 0 => aesop | 1 => aesop | 2 => aesop | 3 => aesop

-- end BitwiseOperation
