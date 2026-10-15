import SP1Clean.Model.Semantics.InstructionPlan
import SP1Clean.Model.Core.Memory
import SP1Clean.Model.Core.MemorySpan

/-! # Ordinary instruction write permissions

The write inventory is computed from the decoded Sail instruction and incoming registers, not
from differences between memory states. In particular, storing the existing value still requires
permission for every written byte. The effective address uses the same RV64 wrapping addition
as the instruction access plan; the interval uses the store width, not its enclosing RAM cell.

This is the ordinary supported-instruction policy component. It rejects unsupported constructors,
invalid widths and missing base registers. It does not check fetch, alignment, address bounds,
normal retirement or resources. `ExecutionWritePolicy` lifts it to occurrences in the existing path.
-/

namespace SP1Clean.Model.Core.InstructionWrite

open LeanRV64D.Defs SP1Clean.Semantics SP1Clean.Soundness.Target

/-- The exact write spans of a supported ordinary instruction, including same-value stores.
Successful non-store instructions have an empty inventory; failure is distinct from no writes. -/
def spans? (register : BitVec 5 → Option (BitVec 64)) (decoded : instruction) :
    Option (List MemorySpan) := do
  if instructionImageOK decoded && (instructionRouteId decoded).isSome then
    match decoded with
    | .STORE (offset, _, rs1, width) => do
        let base ← register (regidxBits rs1)
        some [⟨(memoryEffectiveAddress base offset).toNat, width.toNat⟩]
    | _ => some []
  else none

/-- Check every byte in the write inventory against the immutable-code mask. -/
def check (readOnly : ℕ → Bool) (register : BitVec 5 → Option (BitVec 64))
    (decoded : instruction) : Bool :=
  match spans? register decoded with
  | none => false
  | some spans => spans.all fun span =>
      (List.range span.length).all fun offset => !readOnly (span.address + offset)

/-- A successful permission check certifies that the decoded instruction is supported. -/
theorem check_supported (readOnly : ℕ → Bool) (register : BitVec 5 → Option (BitVec 64))
    (decoded : instruction) (checked : check readOnly register decoded = true) :
    instructionImageOK decoded = true ∧ (instructionRouteId decoded).isSome = true := by
  by_cases supported : (instructionImageOK decoded && (instructionRouteId decoded).isSome) = true
  · simpa only [Bool.and_eq_true] using supported
  · simp [check, spans?, supported] at checked

/-- A supported non-store has no memory writes and needs no register observations for permission. -/
theorem check_of_nonstore (readOnly : ℕ → Bool) (register : BitVec 5 → Option (BitVec 64))
    (decoded : instruction) (valid : instructionImageOK decoded = true)
    (routed : (instructionRouteId decoded).isSome = true)
    (nonstore : ∀ offset rs2 rs1 width, decoded ≠ .STORE (offset, rs2, rs1, width)) :
    check readOnly register decoded = true := by
  unfold check spans?
  simp only [valid, routed, Bool.and_self, ↓reduceIte]
  rfl

/-- Permission is exactly successful footprint extraction plus byte-level exclusion. -/
theorem check_iff (readOnly : ℕ → Bool) (register : BitVec 5 → Option (BitVec 64))
    (decoded : instruction) :
    check readOnly register decoded = true ↔
      ∃ spans, spans? register decoded = some spans ∧
        ∀ span ∈ spans, ByteMemory.Avoids readOnly span.address span.length := by
  cases found : spans? register decoded <;>
    simp [check, found, ByteMemory.Avoids, List.all_eq_true]

/-- A decoded store always requests its full width, irrespective of its source data register. -/
theorem spans?_store (register : BitVec 5 → Option (BitVec 64))
    (offset : BitVec 12) (rs2 rs1 : regidx) (width : word_width)
    (validWidth : storeWidthOK width = true) :
    spans? register (.STORE (offset, rs2, rs1, width)) =
      (register (regidxBits rs1)).map fun base =>
        [⟨(memoryEffectiveAddress base offset).toNat, width.toNat⟩] := by
  have routed : (instructionRouteId (.STORE (offset, rs2, rs1, width))).isSome = true := by
    simp only [instructionRouteId, instructionRouteKey, Option.bind_some, SP1Clean.routeId_isSome]
    unfold storeOpcode
    split_ifs <;> decide
  simp [spans?, instructionImageOK, validWidth, routed]
  cases register (regidxBits rs1) <;> rfl

/-- The store check reads the base register and requires permission for all addressed bytes. -/
theorem check_store_iff (readOnly : ℕ → Bool) (register : BitVec 5 → Option (BitVec 64))
    (offset : BitVec 12) (rs2 rs1 : regidx) (width : word_width)
    (validWidth : storeWidthOK width = true) :
    check readOnly register (.STORE (offset, rs2, rs1, width)) = true ↔
      ∃ base, register (regidxBits rs1) = some base ∧
        ByteMemory.Avoids readOnly (memoryEffectiveAddress base offset).toNat width.toNat := by
  rw [check_iff, spans?_store register offset rs2 rs1 width validWidth]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨spans, ⟨base, observed, rfl⟩, allowed⟩
    exact ⟨base, observed, allowed _ (List.mem_singleton_self _)⟩
  · rintro ⟨base, observed, allowed⟩
    exact ⟨_, ⟨base, observed, rfl⟩, by simpa only [List.mem_singleton, forall_eq] using allowed⟩

/-- The ordinary instruction at the actual PC has a supported, permitted write footprint.
The fetch and official decoder bindings are semantic facts, with no AIR or compiler inputs. -/
def PermittedAt (readOnly : ℕ → Bool) (program : GuestProgram) (source : SailState) : Prop :=
  ∃ pc word decoded, source.regs.get? Register.PC = some pc ∧
    program.fetchWord pc = some word ∧ ConfiguredDecode word decoded ∧
    check readOnly source.get_reg? decoded = true

/-- On a configured source, any authenticated decode observes the same permitted instruction.
Existential witnesses cannot evade a denied store by choosing another word or decoding. -/
theorem PermittedAt.check {readOnly : ℕ → Bool} {program : GuestProgram} {source : SailState}
    (permitted : PermittedAt readOnly program source) (configured : SailConfigured source)
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded) :
    check readOnly source.get_reg? decoded = true := by
  obtain ⟨actualPc, actualWord, actual, pcEq, wordEq, decodedEq, allowed⟩ := permitted
  obtain rfl := Option.some.inj (pcEq.symm.trans atPc)
  obtain rfl := Option.some.inj (wordEq.symm.trans fetched)
  have same := (decodedEq source configured).symm.trans (decode source configured)
  cases same
  exact allowed

end SP1Clean.Model.Core.InstructionWrite
