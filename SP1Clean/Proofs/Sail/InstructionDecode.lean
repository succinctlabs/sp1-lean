import SP1Clean.Proofs.Sail.InstructionDecode.Families

/-! # Agreement of the executable native decoder with official Sail

Successful parsing gives the exact instruction returned by the pinned Sail decoder in every
configured state. The checked program image therefore requires no caller-provided decoder
certificate. The hint-extension aliases excluded by the parser have distinct Sail constructors.
-/

namespace SP1Clean.SailDecode

open SP1Clean.Model.Core SP1Clean.Soundness.Target

/-- The executable decoder agrees with official Sail throughout its accepted domain. -/
theorem instructionDecode_agrees : InstructionDecode.AgreesWithSail := by
  intro word i decoded s cfg
  have noHint := InstructionDecode.decode_reservedHint decoded
  unfold InstructionDecode.decode InstructionDecode.register InstructionDecode.immediate at decoded
  repeat' first
    | contradiction
    | dsimp only [Bind.bind, Option.bind] at decoded
    | split at decoded
  all_goals
    first
    | contradiction
    | cases Option.some.inj decoded
      first
      | apply Symbolic.decode_ADD word s cfg noHint
      | apply Symbolic.decode_SLL word s cfg noHint
      | apply Symbolic.decode_SLT word s cfg noHint
      | apply Symbolic.decode_SLTU word s cfg noHint
      | apply Symbolic.decode_XOR word s cfg noHint
      | apply Symbolic.decode_SRL word s cfg noHint
      | apply Symbolic.decode_OR word s cfg noHint
      | apply Symbolic.decode_AND word s cfg noHint
      | apply Symbolic.decode_SUB word s cfg noHint
      | apply Symbolic.decode_SRA word s cfg noHint
      | apply Symbolic.decode_ADDW word s cfg noHint
      | apply Symbolic.decode_SLLW word s cfg noHint
      | apply Symbolic.decode_SRLW word s cfg noHint
      | apply Symbolic.decode_SUBW word s cfg noHint
      | apply Symbolic.decode_SRAW word s cfg noHint
      | apply Symbolic.decode_MUL word s cfg noHint
      | apply Symbolic.decode_MULH word s cfg noHint
      | apply Symbolic.decode_MULHSU word s cfg noHint
      | apply Symbolic.decode_MULHU word s cfg noHint
      | apply Symbolic.decode_DIV word s cfg noHint
      | apply Symbolic.decode_DIVU word s cfg noHint
      | apply Symbolic.decode_REM word s cfg noHint
      | apply Symbolic.decode_REMU word s cfg noHint
      | apply Symbolic.decode_MULW word s cfg noHint
      | apply Symbolic.decode_DIVW word s cfg noHint
      | apply Symbolic.decode_DIVUW word s cfg noHint
      | apply Symbolic.decode_REMW word s cfg noHint
      | apply Symbolic.decode_REMUW word s cfg noHint
      | apply Symbolic.decode_ADDI word s cfg noHint
      | apply Symbolic.decode_SLTI word s cfg noHint
      | apply Symbolic.decode_SLTIU word s cfg noHint
      | apply Symbolic.decode_XORI word s cfg noHint
      | apply Symbolic.decode_ORI word s cfg noHint
      | apply Symbolic.decode_ANDI word s cfg noHint
      | apply Symbolic.decode_ADDIW word s cfg noHint
      | apply Symbolic.decode_SLLI word s cfg noHint
      | apply Symbolic.decode_SRLI word s cfg noHint
      | apply Symbolic.decode_SRAI word s cfg noHint
      | apply Symbolic.decode_SLLIW word s cfg noHint
      | apply Symbolic.decode_SRLIW word s cfg noHint
      | apply Symbolic.decode_SRAIW word s cfg noHint
      | apply Symbolic.decode_LUI word s cfg noHint
      | apply Symbolic.decode_AUIPC word s cfg noHint
      | apply Symbolic.decode_JAL word s cfg noHint
      | apply Symbolic.decode_JALR word s cfg noHint
      | apply Symbolic.decode_BEQ word s cfg noHint
      | apply Symbolic.decode_BNE word s cfg noHint
      | apply Symbolic.decode_BLT word s cfg noHint
      | apply Symbolic.decode_BGE word s cfg noHint
      | apply Symbolic.decode_BLTU word s cfg noHint
      | apply Symbolic.decode_BGEU word s cfg noHint
      | apply Symbolic.decode_LB word s cfg noHint
      | apply Symbolic.decode_LH word s cfg noHint
      | apply Symbolic.decode_LW word s cfg noHint
      | apply Symbolic.decode_LD word s cfg noHint
      | apply Symbolic.decode_LBU word s cfg noHint
      | apply Symbolic.decode_LHU word s cfg noHint
      | apply Symbolic.decode_LWU word s cfg noHint
      | apply Symbolic.decode_SB word s cfg noHint
      | apply Symbolic.decode_SH word s cfg noHint
      | apply Symbolic.decode_SW word s cfg noHint
      | apply Symbolic.decode_SD word s cfg noHint
      | subst word
        exact decode_ECALL s cfg.init cfg.priv cfg.mseccfg_disabled
  all_goals
    simp_all only [BitVec.toNat_eq, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.zero_mod]

end SP1Clean.SailDecode
