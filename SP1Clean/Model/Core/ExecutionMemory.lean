import SP1Clean.Model.Core.ExecutionFrame
import SP1Clean.Model.Core.ExecutionSnapshot
import SP1Clean.Model.Core.ExecutionEncoding

/-! # Memory presence throughout the independent execution path

The complete snapshot materializes every byte below the native Sail limit. Actual Sail stores
and concrete host writes never delete a byte. These facts establish memory availability at every
cut without using an AIR witness or the final-memory grounding conclusion.
-/

namespace SP1Clean.Model.Core
open Machine Soundness.Target

/-- Native memory encodings cannot write outside the represented Sail memory domain. -/
theorem instructionMemoryEncoded.outside_permission {decoded : LeanRV64D.Defs.instruction}
    {register : BitVec 5 → Option (BitVec 64)} (encoded : instructionMemoryEncoded register decoded)
    (image : instructionImageOK decoded = true) (routed : (instructionRouteId decoded).isSome) :
    InstructionWrite.check (fun address => decide (NativeLayout.sailMemory.upper ≤ address))
      register decoded = true := by
  by_cases store : ∃ offset rs2 rs1 width, decoded = .STORE (offset, rs2, rs1, width)
  · obtain ⟨offset, rs2, rs1, width, rfl⟩ := store
    obtain ⟨base, observed, inside, _⟩ := encoded
    apply (InstructionWrite.check_store_iff _ _ _ _ _ _ image).mpr
    refine ⟨base, observed, ?_⟩
    intro index small
    simp only [decide_eq_false_iff_not, not_le]
    have upper := inside.2
    change _ < 2 ^ 48
    change _ ≤ 2 ^ 48 at upper
    omega
  · exact InstructionWrite.check_of_nonstore _ _ decoded image routed
      (fun offset rs2 rs1 width same => store ⟨offset, rs2, rs1, width, same⟩)

/-- The same authenticated decode certifies the outside-domain frame mask. -/
theorem ordinaryEncodedAt.outside_permission {program : GuestProgram} {source : SailState}
    (encoded : ordinaryEncodedAt program source) :
    InstructionWrite.PermittedAt (fun address => decide (NativeLayout.sailMemory.upper ≤ address))
      program source := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, image, routed, memory⟩ := encoded
  exact ⟨pc, word, decoded, atPc, fetched, decode, memory.outside_permission image routed⟩

/-- Actual encoded steps preserve all keys outside the finite Sail memory domain. -/
theorem ExecutionStep.memory_outside {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (encoded : eventEncodedAt program source event)
    (hostBound : policy.memory.upper ≤ NativeLayout.sailMemory.upper)
    (address : ℕ) (outside : NativeLayout.sailMemory.upper ≤ address) :
    target.sail.mem.get? address = source.sail.mem.get? address := by
  cases step with
  | ordinary _ _ normal =>
    exact (Advance.ordinary_normal_frame configured loaded (encoded.2 rfl).outside_permission normal).2
      address (by simpa using outside)
  | syscall success =>
    obtain ⟨pc, execution, _, _, run, _, targetEq, _⟩ := HostState.step_observations success
    rw [targetEq]
    exact HostExecution.preserves_memory_outside run pc address (Or.inr (by omega))

/-- Both semantic step constructors retain every byte present before the step. -/
theorem ExecutionStep.memory_present {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (permitted : event = .ordinary → InstructionWrite.PermittedAt policy.memory.readOnly program source.sail) :
    ∀ address, (source.sail.mem.get? address).isSome → (target.sail.mem.get? address).isSome := by
  cases step with
  | ordinary _ _ normal =>
    exact (Advance.ordinary_normal_memory_frame configured loaded (permitted rfl) normal).2.2
  | syscall success =>
    obtain ⟨pc, execution, _, _, _, _, targetEq, _⟩ := HostState.step_observations success
    rw [targetEq]
    exact execution.effect.preserves_present source.sail.mem

/-- Presence is preserved along the same mixed path that supplies ROM and configuration. -/
theorem ExecutionPath.memory_present {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy (image.toGuestProgram valid) source events target)
    (permitted : ExecutionPath.WritesPermitted policy (image.toGuestProgram valid) source events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail) :
    ∀ address, (source.sail.mem.get? address).isSome → (target.sail.mem.get? address).isSome := by
  induction path with
  | nil => exact fun _ present => present
  | cons step _ ih =>
    have permission := (ExecutionPath.writesPermitted_cons_iff step).mp permitted
    have next := step.frame configured loaded permission.1
    have rom := image.romLoaded_of_readOnly valid
      (fun address selected => next.2 address (protectsRom address selected)) loaded
    intro address present
    exact ih permission.2 next.1 rom address (step.memory_present configured loaded permission.1 address present)

/-- Every finite boundary represents a present byte throughout its declared Sail memory domain. -/
theorem ExecutionSnapshot.memory_present (snapshot : ExecutionSnapshot) (address : ℕ)
    (inside : address < NativeLayout.sailMemory.upper) :
    (snapshot.realize.sail.mem.get? address).isSome := by
  change ((snapshot.sail.memory.toSailMemory _).get? address).isSome = true
  rw [ByteMemory.toSailMemory_get?, if_pos inside]
  rfl

/-- The finite source has no memory keys beyond the represented Sail domain. -/
theorem ExecutionSnapshot.memory_absent (snapshot : ExecutionSnapshot) (address : ℕ)
    (outside : NativeLayout.sailMemory.upper ≤ address) :
    snapshot.realize.sail.mem.get? address = none := by
  change (snapshot.sail.memory.toSailMemory _).get? address = none
  change 2 ^ 48 ≤ address at outside
  rw [ByteMemory.toSailMemory_get?, if_neg (by omega)]

/-- Outside-domain equality is preserved independently of final AIR memory grounding. -/
theorem ExecutionPath.memory_outside {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy (image.toGuestProgram valid) source events target)
    (permitted : ExecutionPath.WritesPermitted policy (image.toGuestProgram valid) source events)
    (encoded : ExecutionPath.Encoded policy (image.toGuestProgram valid) source events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (hostBound : policy.memory.upper ≤ NativeLayout.sailMemory.upper)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail)
    (address : ℕ) (outside : NativeLayout.sailMemory.upper ≤ address) :
    target.sail.mem.get? address = source.sail.mem.get? address := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
    have permission := (ExecutionPath.writesPermitted_cons_iff step).mp permitted
    have encoding := (ExecutionPath.encoded_cons_iff step).mp encoded
    have next := step.frame configured loaded permission.1
    have rom := image.romLoaded_of_readOnly valid
      (fun address selected => next.2 address (protectsRom address selected)) loaded
    exact (ih permission.2 encoding.2 next.1 rom).trans
      (step.memory_outside configured loaded encoding.1 hostBound address outside)

/-- Every actual prefix inherits the incoming domain; no full outgoing snapshot is assumed. -/
theorem ExecutionPath.memory_present_prefix {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
    {source : ExecutionSnapshot} {target current : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy (image.toGuestProgram valid) source.realize events target)
    (permitted : ExecutionPath.WritesPermitted policy (image.toGuestProgram valid) source.realize events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.realize.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.realize.sail)
    {cut : ℕ} (replay : executionTrajectory policy (image.toGuestProgram valid) source.realize events cut = some current)
    (address : ℕ) (inside : address < NativeLayout.sailMemory.upper) :
    (current.sail.mem.get? address).isSome := by
  obtain ⟨middle, left, _, allowed, _⟩ := permitted.split path cut
  have same : middle = current := Option.some.inj (left.replay.symm.trans replay)
  subst current
  exact left.memory_present valid allowed protectsRom configured loaded address (source.memory_present address inside)

/-- Every encoded prefix has exactly the finite source's byte-key domain, including held endpoints. -/
theorem ExecutionPath.memory_domain_prefix {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
    {source : ExecutionSnapshot} {target current : ExecutionState} {events : List ExecutionEvent}
    (path : ExecutionPath policy (image.toGuestProgram valid) source.realize events target)
    (permitted : ExecutionPath.WritesPermitted policy (image.toGuestProgram valid) source.realize events)
    (encoded : ExecutionPath.Encoded policy (image.toGuestProgram valid) source.realize events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (hostBound : policy.memory.upper ≤ NativeLayout.sailMemory.upper)
    (configured : SailConfigured source.realize.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.realize.sail)
    {cut : ℕ} (replay : executionTrajectory policy (image.toGuestProgram valid) source.realize events cut = some current)
    (address : ℕ) :
    (current.sail.mem.get? address).isSome ↔ address < NativeLayout.sailMemory.upper := by
  constructor
  · intro present
    by_contra outside
    have outside : NativeLayout.sailMemory.upper ≤ address := by omega
    obtain ⟨middle, left, _, allowed, _⟩ := permitted.split path cut
    have same : middle = current := Option.some.inj (left.replay.symm.trans replay)
    subst current
    have encoding := ((ExecutionPath.encoded_append_iff (second := events.drop cut) left).mp
      (by simpa only [List.take_append_drop] using encoded)).1
    have unchanged := left.memory_outside valid allowed encoding protectsRom hostBound configured loaded address outside
    rw [unchanged, source.memory_absent address outside] at present
    contradiction
  · exact path.memory_present_prefix valid permitted protectsRom configured loaded replay address

end SP1Clean.Model.Core
