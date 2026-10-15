import SP1Clean.Proofs.Sail.InstructionDecode.Tactic

/-! # Official Sail decoding of the supported integer encoding families

Every lemma leaves the instruction word, operand fields, and configured Sail state symbolic.
The whole-parser agreement theorem consumes these internal encoding cases; Program providers
and machine-theorem callers do not need to dispatch on them.
-/

namespace SP1Clean.SailDecode.Symbolic

open LeanRV64D.Defs LeanRV64D.Functions Sail SP1Clean.Soundness.Target
open SP1Clean.Model.Core.InstructionDecode

theorem decode_ADD (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADD)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADD))

theorem decode_SLL (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 1#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLL)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLL))

theorem decode_SLT (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 2#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLT)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLT))

theorem decode_SLTU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 3#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTU)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTU))

theorem decode_XOR (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 4#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .XOR)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .XOR))

theorem decode_SRL (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRL)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRL))

theorem decode_OR (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 6#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .OR)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .OR))

theorem decode_AND (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 7#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .AND)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .AND))

theorem decode_SUB (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 32#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SUB)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SUB))

theorem decode_SRA (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 32#7) :
    (ext_decode word).run s = .ok (.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRA)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPE (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRA))

theorem decode_ADDW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADDW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADDW))

theorem decode_SLLW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 1#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLW))

theorem decode_SRLW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLW))

theorem decode_SUBW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 32#7) :
    (ext_decode word).run s = .ok (.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SUBW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SUBW))

theorem decode_SRAW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 32#7) :
    (ext_decode word).run s = .ok (.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.RTYPEW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAW))

theorem decode_MUL (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.Low, .Signed, .Signed⟩)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.Low, .Signed, .Signed⟩))

theorem decode_MULH (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 1#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Signed, .Signed⟩)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Signed, .Signed⟩))

theorem decode_MULHSU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 2#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Signed, .Unsigned⟩)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Signed, .Unsigned⟩))

theorem decode_MULHU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 3#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Unsigned, .Unsigned⟩)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.MUL (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), ⟨.High, .Unsigned, .Unsigned⟩))

theorem decode_DIV (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 4#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.DIV (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false)) s := by
  have hUnsigned : bits word 12 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.DIV (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false))

theorem decode_DIVU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.DIV (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true)) s := by
  have hUnsigned : bits word 12 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.DIV (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true))

theorem decode_REM (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 6#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.REM (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false)) s := by
  have hUnsigned : bits word 12 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.REM (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false))

theorem decode_REMU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 51#7)
    (h1 : bits word 12 3 = 7#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.REM (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true)) s := by
  have hUnsigned : bits word 12 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.REM (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true))

theorem decode_MULW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 0#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.MULW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5))) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.MULW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5)))

theorem decode_DIVW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 4#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.DIVW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false)) s := by
  have hUnsigned : bits word 12 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.DIVW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false))

theorem decode_DIVUW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.DIVW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true)) s := by
  have hUnsigned : bits word 12 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.DIVW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true))

theorem decode_REMW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 6#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.REMW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false)) s := by
  have hUnsigned : bits word 12 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.REMW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false))

theorem decode_REMUW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 59#7)
    (h1 : bits word 12 3 = 7#3)
    (h2 : bits word 25 7 = 1#7) :
    (ext_decode word).run s = .ok (.REMW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true)) s := by
  have hUnsigned : bits word 12 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.REMW (.Regidx (bits word 20 5),
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true))

theorem decode_ADDI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADDI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ADDI))

theorem decode_SLTI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 2#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTI))

theorem decode_SLTIU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 3#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTIU)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLTIU))

theorem decode_XORI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 4#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .XORI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .XORI))

theorem decode_ORI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 6#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ORI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ORI))

theorem decode_ANDI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 7#3) :
    (ext_decode word).run s = .ok (.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ANDI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ITYPE (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .ANDI))

theorem decode_ADDIW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 27#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.ADDIW (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5))) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.ADDIW (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5)))

theorem decode_SLLI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 1#3)
    (h2 : bits word 26 6 = 0#6) :
    (ext_decode word).run s = .ok (.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLI))

theorem decode_SRLI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 26 6 = 0#6) :
    (ext_decode word).run s = .ok (.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLI))

theorem decode_SRAI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 19#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 26 6 = 16#6) :
    (ext_decode word).run s = .ok (.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIOP (bits word 20 6,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAI))

theorem decode_SLLIW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 27#7)
    (h1 : bits word 12 3 = 1#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLIW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SLLIW))

theorem decode_SRLIW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 27#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 0#7) :
    (ext_decode word).run s = .ok (.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLIW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRLIW))

theorem decode_SRAIW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 27#7)
    (h1 : bits word 12 3 = 5#3)
    (h2 : bits word 25 7 = 32#7) :
    (ext_decode word).run s = .ok (.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAIW)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.SHIFTIWOP (bits word 20 5,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), .SRAIW))

theorem decode_LUI (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 55#7) :
    (ext_decode word).run s = .ok (.UTYPE (bits word 12 20,
      .Regidx (bits word 7 5), .LUI)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.UTYPE (bits word 12 20,
      .Regidx (bits word 7 5), .LUI))

theorem decode_AUIPC (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 23#7) :
    (ext_decode word).run s = .ok (.UTYPE (bits word 12 20,
      .Regidx (bits word 7 5), .AUIPC)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.UTYPE (bits word 12 20,
      .Regidx (bits word 7 5), .AUIPC))

theorem decode_JAL (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 111#7) :
    (ext_decode word).run s = .ok (.JAL (bits word 31 1 ++ bits word 12 8 ++ bits word 20 1 ++ bits word 21 10 ++ 0#1,
      .Regidx (bits word 7 5))) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.JAL (bits word 31 1 ++ bits word 12 8 ++ bits word 20 1 ++ bits word 21 10 ++ 0#1,
      .Regidx (bits word 7 5)))

theorem decode_JALR (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 103#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.JALR (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5))) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.JALR (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5)))

theorem decode_BEQ (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BEQ)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BEQ))

theorem decode_BNE (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 1#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BNE)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BNE))

theorem decode_BLT (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 4#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BLT)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BLT))

theorem decode_BGE (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 5#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BGE)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BGE))

theorem decode_BLTU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 6#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BLTU)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BLTU))

theorem decode_BGEU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 99#7)
    (h1 : bits word 12 3 = 7#3) :
    (ext_decode word).run s = .ok (.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BGEU)) s := by
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.BTYPE (bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), .BGEU))

theorem decode_LB (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 1)) s := by
  have hWidth : bits word 12 2 = 0#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 1))

theorem decode_LH (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 1#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 2)) s := by
  have hWidth : bits word 12 2 = 1#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 2))

theorem decode_LW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 2#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 4)) s := by
  have hWidth : bits word 12 2 = 2#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 4))

theorem decode_LD (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 3#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 8)) s := by
  have hWidth : bits word 12 2 = 3#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), false, 8))

theorem decode_LBU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 4#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 1)) s := by
  have hWidth : bits word 12 2 = 0#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 1))

theorem decode_LHU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 5#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 2)) s := by
  have hWidth : bits word 12 2 = 1#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 2))

theorem decode_LWU (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 3#7)
    (h1 : bits word 12 3 = 6#3) :
    (ext_decode word).run s = .ok (.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 4)) s := by
  have hWidth : bits word 12 2 = 2#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 1#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.LOAD (bits word 20 12,
      .Regidx (bits word 15 5),
      .Regidx (bits word 7 5), true, 4))

theorem decode_SB (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 35#7)
    (h1 : bits word 12 3 = 0#3) :
    (ext_decode word).run s = .ok (.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 1)) s := by
  have hWidth : bits word 12 2 = 0#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 1))

theorem decode_SH (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 35#7)
    (h1 : bits word 12 3 = 1#3) :
    (ext_decode word).run s = .ok (.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 2)) s := by
  have hWidth : bits word 12 2 = 1#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 2))

theorem decode_SW (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 35#7)
    (h1 : bits word 12 3 = 2#3) :
    (ext_decode word).run s = .ok (.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 4)) s := by
  have hWidth : bits word 12 2 = 2#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 4))

theorem decode_SD (word : BitVec 32) (s : SailState) (cfg : SailConfigured s)
    (hints : reservedHint word = false)
    (h0 : bits word 0 7 = 35#7)
    (h1 : bits word 12 3 = 3#3) :
    (ext_decode word).run s = .ok (.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 8)) s := by
  have hWidth : bits word 12 2 = 3#2 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have hSign : bits word 14 1 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    have hf := congrArg BitVec.toNat h1
    simp only [SP1Clean.Model.Core.InstructionDecode.bits, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at hf ⊢
    omega
  have noHint := hints
  sail_decode_walk s, cfg, (instruction.STORE (bits word 25 7 ++ bits word 7 5,
      .Regidx (bits word 20 5),
      .Regidx (bits word 15 5), 8))

end SP1Clean.SailDecode.Symbolic
