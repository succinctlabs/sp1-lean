import SP1Clean.Model.Core.InstructionDecode
import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Model.BusMessages
import ToClean.Circuit.StaticTable
import Mathlib.Tactic.IntervalCases

/-! # Fixed Program rows computed from the finite image

The table contains complete messages produced by the executable decoder, independently of all
trace rows and prover data. Validation fails if any ROM word cannot be projected. Local range
facts follow from the projection; no row-validity proof is supplied with the image.

Membership here certifies agreement with `InstructionDecode.decode`; the separate proof in
`Proofs/Sail/InstructionDecode.lean` identifies its results with Sail's configured decoder.
This table is not yet wired into the released machine theorem.
-/

namespace SP1Clean.Model.Core

open SP1Clean.Soundness.Target SP1Clean.ProgramChip SP1Clean.Channels

deriving instance DecidableEq for ProgramMsg

namespace ProgramTable

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Canonical three-limb PC encoding. Input validation rules out truncation above bit 47. -/
def pcLimbs (pc : BitVec 64) : Vector (ZMod p) 3 :=
  #v[(bitVecToWord pc)[0], (bitVecToWord pc)[1], (bitVecToWord pc)[2]]

/-- Translate the semantic projection into the exact Program-channel payload order. -/
def message (row : ProgramRow (ZMod p)) : ProgramMsg (ZMod p) where
  pc0 := row.pc0
  pc1 := row.pc1
  pc2 := row.pc2
  opcode := row.opcode
  op_a := row.op_a
  op_b := row.op_b
  op_c := row.op_c
  op_a_0 := row.op_a_0
  imm_b := row.imm_b
  imm_c := row.imm_c

/-- Decode one ROM word, handling the encoding-pinned ECALL operand convention explicitly. -/
def row? (entry : BitVec 64 × BitVec 32) : Option (ProgramRow (ZMod p)) :=
  if entry.2 = ECALL_ENC then some (ecallProgramRow (pcLimbs entry.1))
  else (InstructionDecode.decode entry.2).bind (instrToProgramRow' (pcLimbs entry.1))

/-- The executable field payload of a supported ROM entry. -/
def message? (entry : BitVec 64 × BitVec 32) : Option (ProgramMsg (ZMod p)) :=
  (row? entry).map message

omit [Fact (2 ^ 17 < p)] in
private theorem projected_pc {pc : Vector (ZMod p) 3} {i : LeanRV64D.Defs.instruction}
    {row : ProgramRow (ZMod p)} (projected : instrToProgramRow pc i = some row) :
    rowPcVec row = pc := by
  cases i <;> simp only [instrToProgramRow] at projected
  all_goals first | contradiction | cases Option.some.inj projected
  all_goals
    apply Vector.ext
    intro j hj
    interval_cases j <;> rfl

omit [Fact (2 ^ 17 < p)] in
/-- Successful projection keeps exactly the PC supplied by the ROM entry. -/
theorem row_pc {entry : BitVec 64 × BitVec 32} {row : ProgramRow (ZMod p)}
    (decoded : row? entry = some row) : rowPcVec row = pcLimbs entry.1 := by
  unfold row? at decoded
  split at decoded
  · cases Option.some.inj decoded
    exact Vector.ext fun j hj => by interval_cases j <;> rfl
  · obtain ⟨i, _, projected⟩ := Option.bind_eq_some_iff.mp decoded
    exact projected_pc (instrToProgramRow'_some projected)

/-- In the native address window, the three PC limbs recover the full byte address exactly. -/
theorem row_address {entry : BitVec 64 × BitVec 32} {row : ProgramRow (ZMod p)}
    (decoded : row? entry = some row) (bound : entry.1.toNat < 2 ^ 48) :
    pcBitsOfRow row = entry.1 := by
  have high : (BitVec.extractLsb' 48 16 entry.1).toNat = 0 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt bound, Nat.zero_mod]
  have wordHigh : (bitVecToWord (p := p) entry.1)[3] = 0 := by
    simp [bitVecToWord, high]
  have full := toBitVec64_bitVecToWord (p := p) entry.1
  rw [Word.toBitVec64, Word.toNat, wordHigh, ZMod.val_zero, zero_mul, add_zero] at full
  have pc := row_pc decoded
  have pc0 := congrArg (fun v : Vector (ZMod p) 3 => v[0]) pc
  have pc1 := congrArg (fun v : Vector (ZMod p) 3 => v[1]) pc
  have pc2 := congrArg (fun v : Vector (ZMod p) 3 => v[2]) pc
  change row.pc0 = (bitVecToWord (p := p) entry.1)[0] at pc0
  change row.pc1 = (bitVecToWord (p := p) entry.1)[1] at pc1
  change row.pc2 = (bitVecToWord (p := p) entry.1)[2] at pc2
  unfold pcBitsOfRow pcBitsOfVals
  rw [pc0, pc1, pc2]
  exact full

/-- The computed rows satisfy every structural guarantee required by the Program channel. -/
theorem message_rowSpec {entry : BitVec 64 × BitVec 32} {msg : ProgramMsg (ZMod p)}
    (decoded : message? entry = some msg) : ProgramMsg.RowSpec msg := by
  obtain ⟨row, decodedRow, rfl⟩ := Option.map_eq_some_iff.mp decoded
  have pc := row_pc decodedRow
  have limbs := isU64_bitVecToWord (p := p) entry.1
  have pc0 := congrArg (fun v : Vector (ZMod p) 3 => v[0]) pc
  have pc1 := congrArg (fun v : Vector (ZMod p) 3 => v[1]) pc
  have pc2 := congrArg (fun v : Vector (ZMod p) 3 => v[2]) pc
  change row.pc0 = (bitVecToWord entry.1)[0] at pc0
  change row.pc1 = (bitVecToWord entry.1)[1] at pc1
  change row.pc2 = (bitVecToWord entry.1)[2] at pc2
  change row.op_a.val < 32 ∧ row.pc0.val < 2 ^ 16 ∧ row.pc1.val < 2 ^ 16 ∧
    row.pc2.val < 2 ^ 16 ∧ (row.op_a_0 = 0 ∨ row.op_a_0 = 1)
  refine ⟨?_, (by rw [pc0]; exact limbs 0),
    (by rw [pc1]; exact limbs 1), (by rw [pc2]; exact limbs 2), ?_⟩
  all_goals
    unfold row? at decodedRow
    split at decodedRow
    · cases Option.some.inj decodedRow
      norm_num [message, ecallProgramRow, ZMod.val_natCast, Nat.mod_eq_of_lt
        (show 5 < p by have := Fact.out (p := 2 ^ 17 < p); omega)]
    · obtain ⟨i, _, projected⟩ := Option.bind_eq_some_iff.mp decodedRow
      have plain := instrToProgramRow'_some projected
      first
      | exact (instrToProgramRow_register_bounds plain).1
      | change row.op_a_0 = 0 ∨ row.op_a_0 = 1
        rw [instrToProgramRow_op_a_0 plain]
        split <;> simp

omit [Fact (2 ^ 17 < p)] in
/-- The guarded projection is total on the routed, canonical instruction image. -/
private theorem projection_isSome (pc : Vector (ZMod p) 3) (i : LeanRV64D.Defs.instruction)
    (canonical : instructionImageOK i = true) (routed : (instructionRouteKey i).isSome = true) :
    (instrToProgramRow' pc i).isSome = true := by
  cases i <;> simp_all [instructionImageOK, instructionRouteKey, instrToProgramRow', instrToProgramRow]

omit [Fact (2 ^ 17 < p)] in
/-- Program-row construction accepts exactly the parser's domain; there is no extra readiness check. -/
theorem row_isSome_iff (entry : BitVec 64 × BitVec 32) :
    (row? (p := p) entry).isSome = true ↔ (InstructionDecode.decode entry.2).isSome = true := by
  by_cases ecall : entry.2 = ECALL_ENC
  · simp only [row?, ecall, if_pos, Option.isSome_some]
    exact iff_of_true trivial rfl
  · simp only [row?, ecall, if_false]
    cases parsed : InstructionDecode.decode entry.2 with
    | none => simp
    | some i =>
      simp only [Option.bind_some, Option.isSome_some, iff_true]
      obtain ⟨wordEq, _⟩ | ⟨canonical, routed⟩ := InstructionDecode.decode_supported parsed
      · exact (ecall wordEq).elim
      · exact projection_isSome _ i canonical routed

/-- Transport uniform decoder agreement to the existing committed-ROM contract.
The proof layer supplies the closed parser theorem; instruction-family distinctions remain internal. -/
theorem row_committed_of_decode (decoder : InstructionDecode.AgreesWithSail)
    {program : GuestProgram} {entry : BitVec 64 × BitVec 32} {row : ProgramRow (ZMod p)}
    (fetch : program.fetchWord entry.1 = some entry.2) (bound : entry.1.toNat < 2 ^ 48)
    (decoded : row? entry = some row) : committedInROM program row := by
  have address := row_address decoded bound
  have pc := row_pc decoded
  unfold row? at decoded
  split at decoded
  · rename_i ecall
    exact Or.inr ⟨by rw [address, fetch, ecall], by rw [pc]; exact (Option.some.inj decoded).symm⟩
  · obtain ⟨i, parsed, projected⟩ := Option.bind_eq_some_iff.mp decoded
    exact Or.inl ⟨entry.2, i, by rw [address]; exact fetch,
      decoder entry.2 i parsed, by rw [pc]; exact projected⟩

end ProgramTable

namespace ProgramImage

/-- Complete fixed messages. `checkProgram` below rejects images for which filtering omits a word. -/
def programRows (image : ProgramImage) {p : ℕ} [Fact p.Prime] : List (ProgramMsg (ZMod p)) :=
  image.rom.filterMap ProgramTable.message?

/-- Every listed word is accepted by the native parser and guarded instruction projection. -/
def Decodable (image : ProgramImage) : Prop :=
  ∀ entry ∈ image.rom, (InstructionDecode.decode entry.2).isSome = true

instance (image : ProgramImage) : Decidable image.Decodable :=
  decidable_of_iff (image.rom.all (fun entry => (InstructionDecode.decode entry.2).isSome) = true)
    (by simp only [Decodable, List.all_eq_true])

/-- Check both the finite loader inputs and every instruction word. -/
def checkProgram (image : ProgramImage) :
    Option {input : ProgramImage // input.Valid ∧ input.Decodable} :=
  if valid : image.Valid ∧ image.Decodable then some ⟨image, valid⟩ else none

/-- The input checker succeeds on exactly its stated finite domain. -/
theorem checkProgram_isSome_iff (image : ProgramImage) :
    (image.checkProgram).isSome = true ↔ image.Valid ∧ image.Decodable := by
  simp only [checkProgram]
  split <;> simp_all

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- Exact membership includes both the source ROM entry and its full computed message. -/
theorem mem_programRows (image : ProgramImage) (msg : ProgramMsg (ZMod p)) :
    msg ∈ image.programRows ↔ ∃ entry ∈ image.rom, ProgramTable.message? entry = some msg :=
  List.mem_filterMap

/-- Fixed messages have structural range guarantees without caller-supplied row facts. -/
theorem programRows_rowSpec (image : ProgramImage) (msg : ProgramMsg (ZMod p))
    (member : msg ∈ image.programRows) : ProgramMsg.RowSpec msg := by
  obtain ⟨_, _, decoded⟩ := (image.mem_programRows msg).mp member
  exact ProgramTable.message_rowSpec decoded

omit [Fact (2 ^ 17 < p)] in
/-- Successful validation retains one row for every ROM entry, including unused entries. -/
theorem programRows_length (image : ProgramImage) (valid : image.Decodable) :
    (image.programRows (p := p)).length = image.rom.length := by
  unfold programRows
  have all : ∀ entry ∈ image.rom, (ProgramTable.message? (p := p) entry).isSome = true := by
    intro entry member
    simpa only [ProgramTable.message?, Option.isSome_map, ProgramTable.row_isSome_iff] using valid entry member
  generalize image.rom = entries at all ⊢
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨msg, decoded⟩ := Option.isSome_iff_exists.mp (all entry (by simp))
    simp only [List.filterMap_cons, decoded, List.length_cons]
    exact congrArg (· + 1) (ih (fun entry member => all entry (by simp [member])))

/-- A fixed lookup whose rows are computed entirely from the program image. -/
@[irreducible] def programTable (image : ProgramImage) : StaticTable (ZMod p) ProgramMsg :=
  StaticTable.ofRows "sp1.native.program" image.programRows

omit [Fact (2 ^ 17 < p)] in
/-- The lookup predicate is exact computed membership, including opcode and every operand limb. -/
theorem programTable_spec (image : ProgramImage) (msg : ProgramMsg (ZMod p)) :
    image.programTable.Spec msg ↔
      ∃ entry ∈ image.rom, ProgramTable.message? entry = some msg := by
  simpa only [programTable, StaticTable.ofRows] using image.mem_programRows msg

/-- Complete-message lookup membership supplies the Program channel's structural guarantees. -/
theorem programTable_rowSpec (image : ProgramImage) (msg : ProgramMsg (ZMod p))
    (member : image.programTable.Spec msg) : ProgramMsg.RowSpec msg := by
  obtain ⟨_, _, decoded⟩ := (image.programTable_spec msg).mp member
  exact ProgramTable.message_rowSpec decoded

end ProgramImage
end SP1Clean.Model.Core
