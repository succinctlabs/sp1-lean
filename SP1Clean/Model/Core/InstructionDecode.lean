import SP1Clean.Model.Semantics.Decode

/-! # Executable RV64IM instruction decoding

A finite decoder for the native instruction profile, including the exact ECALL encoding. It
rejects compressed instructions, reserved function fields, and extensions outside RV64IM. The
result uses the existing Sail instruction vocabulary and guarded Program-row projection.

`Proofs/Sail/InstructionDecode.lean` proves that successful parsing agrees with the official,
stateful Sail decoder in every configured state. Enabled hint-extension aliases are rejected:
their distinct Sail constructors need separate semantic bridges before they can join this profile.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs

namespace InstructionDecode

/-- Extract an unsigned instruction field without a field-modulus dependency. -/
def bits (word : BitVec 32) (start width : ℕ) : BitVec width :=
  BitVec.ofNat width (word.toNat >>> start)

/-- Encodings claimed by enabled Sail hint extensions before the base-integer decoder.

Zicbop claims three ORI-to-x0 immediate patterns; Zihintntl claims four ADD-to-x0 words.
Although their base-integer interpretations are no-ops, literal agreement with the pinned
official decoder requires excluding them until the hint constructors have semantic bridges.
This check deliberately preserves other instructions with `rd = x0`.
-/
def reservedHint (word : BitVec 32) : Bool :=
  let selector := (bits word 20 5).toNat
  ((bits word 0 15 == 0x6013#15) && (selector == 0 || selector == 1 || selector == 3)) ||
    ((bits word 0 20 == 0x00033#20) && (bits word 25 7 == 0#7) &&
      (selector == 2 || selector == 3 || selector == 4 || selector == 5))

/-- Register-register integer and multiplication/division instructions. -/
def register (word : BitVec 32) (wordOp : Bool) : Option instruction := do
  let rs2 := regidx.Regidx (bits word 20 5)
  let rs1 := regidx.Regidx (bits word 15 5)
  let rd := regidx.Regidx (bits word 7 5)
  let function := (bits word 12 3).toNat
  match (bits word 25 7).toNat with
  | 0 =>
    if wordOp then
      let op ← match function with
        | 0 => some ropw.ADDW | 1 => some .SLLW | 5 => some .SRLW | _ => none
      some (.RTYPEW (rs2, rs1, rd, op))
    else
      let op ← match function with
        | 0 => some rop.ADD | 1 => some .SLL | 2 => some .SLT | 3 => some .SLTU
        | 4 => some .XOR | 5 => some .SRL | 6 => some .OR | 7 => some .AND | _ => none
      some (.RTYPE (rs2, rs1, rd, op))
  | 32 =>
    if wordOp then
      let op ← match function with | 0 => some ropw.SUBW | 5 => some .SRAW | _ => none
      some (.RTYPEW (rs2, rs1, rd, op))
    else
      let op ← match function with | 0 => some rop.SUB | 5 => some .SRA | _ => none
      some (.RTYPE (rs2, rs1, rd, op))
  | 1 =>
    if wordOp then
      match function with
      | 0 => some (.MULW (rs2, rs1, rd))
      | 4 => some (.DIVW (rs2, rs1, rd, false))
      | 5 => some (.DIVW (rs2, rs1, rd, true))
      | 6 => some (.REMW (rs2, rs1, rd, false))
      | 7 => some (.REMW (rs2, rs1, rd, true))
      | _ => none
    else
      match function with
      | 0 => some (.MUL (rs2, rs1, rd, ⟨.Low, .Signed, .Signed⟩))
      | 1 => some (.MUL (rs2, rs1, rd, ⟨.High, .Signed, .Signed⟩))
      | 2 => some (.MUL (rs2, rs1, rd, ⟨.High, .Signed, .Unsigned⟩))
      | 3 => some (.MUL (rs2, rs1, rd, ⟨.High, .Unsigned, .Unsigned⟩))
      | 4 => some (.DIV (rs2, rs1, rd, false))
      | 5 => some (.DIV (rs2, rs1, rd, true))
      | 6 => some (.REM (rs2, rs1, rd, false))
      | 7 => some (.REM (rs2, rs1, rd, true))
      | _ => none
  | _ => none

/-- Immediate integer instructions, with distinct RV64 and word-shift reserved-bit checks. -/
def immediate (word : BitVec 32) (wordOp : Bool) : Option instruction := do
  let rs1 := regidx.Regidx (bits word 15 5)
  let rd := regidx.Regidx (bits word 7 5)
  let imm := bits word 20 12
  let function := (bits word 12 3).toNat
  if wordOp then
    match function with
    | 0 => some (.ADDIW (imm, rs1, rd))
    | 1 => if bits word 25 7 = 0 then
        some (.SHIFTIWOP (bits word 20 5, rs1, rd, .SLLIW)) else none
    | 5 =>
      let op ← match (bits word 25 7).toNat with
        | 0 => some sopw.SRLIW | 32 => some .SRAIW | _ => none
      some (.SHIFTIWOP (bits word 20 5, rs1, rd, op))
    | _ => none
  else
    match function with
    | 1 => if bits word 26 6 = 0 then
        some (.SHIFTIOP (bits word 20 6, rs1, rd, .SLLI)) else none
    | 5 =>
      let op ← match (bits word 26 6).toNat with
        | 0 => some sop.SRLI | 16 => some .SRAI | _ => none
      some (.SHIFTIOP (bits word 20 6, rs1, rd, op))
    | _ =>
      let op ← match function with
        | 0 => some iop.ADDI | 2 => some .SLTI | 3 => some .SLTIU | 4 => some .XORI
        | 6 => some .ORI | 7 => some .ANDI | _ => none
      some (.ITYPE (imm, rs1, rd, op))

/-- Decode the supported base instruction word; no state, hints, or proof fields are inputs. -/
def decode (word : BitVec 32) : Option instruction := do
  if reservedHint word then none else do
    let rd := regidx.Regidx (bits word 7 5)
    let rs1 := regidx.Regidx (bits word 15 5)
    let rs2 := regidx.Regidx (bits word 20 5)
    let function := (bits word 12 3).toNat
    match (bits word 0 7).toNat with
    | 0x33 => register word false
    | 0x3b => register word true
    | 0x13 => immediate word false
    | 0x1b => immediate word true
    | 0x37 => some (.UTYPE (bits word 12 20, rd, .LUI))
    | 0x17 => some (.UTYPE (bits word 12 20, rd, .AUIPC))
    | 0x6f =>
      let imm := bits word 31 1 ++ bits word 12 8 ++ bits word 20 1 ++ bits word 21 10 ++ 0#1
      some (.JAL (imm, rd))
    | 0x67 => if function = 0 then some (.JALR (bits word 20 12, rs1, rd)) else none
    | 0x63 =>
      let op ← match function with
        | 0 => some bop.BEQ | 1 => some .BNE | 4 => some .BLT | 5 => some .BGE
        | 6 => some .BLTU | 7 => some .BGEU | _ => none
      let imm := bits word 31 1 ++ bits word 7 1 ++ bits word 25 6 ++ bits word 8 4 ++ 0#1
      some (.BTYPE (imm, rs2, rs1, op))
    | 0x03 =>
      let (width, unsigned) ← match function with
        | 0 => some (1, false) | 1 => some (2, false) | 2 => some (4, false)
        | 3 => some (8, false) | 4 => some (1, true) | 5 => some (2, true)
        | 6 => some (4, true) | _ => none
      some (.LOAD (bits word 20 12, rs1, rd, unsigned, width))
    | 0x23 =>
      let width ← match function with
        | 0 => some 1 | 1 => some 2 | 2 => some 4 | 3 => some 8 | _ => none
      some (.STORE (bits word 25 7 ++ bits word 7 5, rs2, rs1, width))
    | 0x73 => if word = 0x00000073 then some (.ECALL ()) else none
    | _ => none

/-- Every accepted instruction avoids the enabled hint-extension aliases. -/
theorem decode_reservedHint {word : BitVec 32} {i : instruction}
    (decoded : decode word = some i) : reservedHint word = false := by
  unfold decode at decoded
  split at decoded
  · contradiction
  · simpa using ‹¬reservedHint word = true›

/-- Every successful parse belongs to the existing routed instruction image or is ECALL. -/
theorem decode_supported {word : BitVec 32} {i : instruction} (decoded : decode word = some i) :
    (word = SP1Clean.Soundness.Target.ECALL_ENC ∧ i = .ECALL ()) ∨
      SP1Clean.Soundness.Target.instructionImageOK i = true ∧
        (SP1Clean.Soundness.Target.instructionRouteKey i).isSome = true := by
  unfold decode register immediate at decoded
  repeat' first
    | contradiction
    | dsimp only [Bind.bind, Option.bind] at decoded
    | split at decoded
  all_goals
    first
    | contradiction
    | cases Option.some.inj decoded
      first
      | exact Or.inl ⟨by assumption, rfl⟩
      | apply Or.inr
        simp [SP1Clean.Soundness.Target.instructionImageOK,
        SP1Clean.Soundness.Target.instructionRouteKey, SP1Clean.Soundness.Target.mulOpCanonical,
        SP1Clean.Soundness.Target.loadWidthOK, SP1Clean.Soundness.Target.storeWidthOK]

/-- Uniform parser/Sail agreement, proved by `SailDecode.instructionDecode_agrees`.
This proposition is not an axiom or a field of checked program inputs. -/
def AgreesWithSail : Prop :=
  ∀ word i, decode word = some i → SP1Clean.Soundness.Target.ConfiguredDecode word i

end InstructionDecode
end SP1Clean.Model.Core
