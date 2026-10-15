import SP1Clean.Model.Core.ExecutionMemory
import SP1Clean.Model.Core.ExecutionEncoding
import SP1Clean.Model.Semantics.TransitionView

/-! # Total access projection from complete native semantics

The existing decoder, route and access-plan extractor are reused literally. Complete incoming
memory and independent preservation supply RAM-cell availability; the semantic encoding predicate
supplies the address domain. No successful compiler call is assumed.
-/

namespace SP1Clean.Model.Core
open Machine Soundness.Target Semantics LeanRV64D.Defs

/-- Reading eight present bytes always materializes the existing Memory-bus word projection. -/
theorem ramWord64?_isSome_of_present (state : SailState) (address : BitVec 64)
    (present : ∀ index < 8, (state.mem.get? (address.toNat + index)).isSome) :
    (ramWord64? state address).isSome := by
  obtain ⟨b0, h0⟩ := Option.isSome_iff_exists.mp (present 0 (by decide))
  obtain ⟨b1, h1⟩ := Option.isSome_iff_exists.mp (present 1 (by decide))
  obtain ⟨b2, h2⟩ := Option.isSome_iff_exists.mp (present 2 (by decide))
  obtain ⟨b3, h3⟩ := Option.isSome_iff_exists.mp (present 3 (by decide))
  obtain ⟨b4, h4⟩ := Option.isSome_iff_exists.mp (present 4 (by decide))
  obtain ⟨b5, h5⟩ := Option.isSome_iff_exists.mp (present 5 (by decide))
  obtain ⟨b6, h6⟩ := Option.isSome_iff_exists.mp (present 6 (by decide))
  obtain ⟨b7, h7⟩ := Option.isSome_iff_exists.mp (present 7 (by decide))
  simp only [Nat.add_zero] at h0
  simp only [ramWord64?, h0, h1, h2, h3, h4, h5, h6, h7, bind, Option.bind_some,
    pure, Option.isSome_some]

/-- The canonical RAM cell address is ordinary floor alignment, without bitvector wraparound. -/
theorem memoryRamCell_baseAddr (base : BitVec 64) (offset : BitVec 12) :
    (memoryRamCell base offset).baseAddr.toNat = (memoryEffectiveAddress base offset).toNat / 8 * 8 := by
  have addressBound := (memoryEffectiveAddress base offset).isLt
  have cellBound : (memoryEffectiveAddress base offset).toNat / 8 < 2 ^ 61 := by omega
  have byteBound : (memoryEffectiveAddress base offset).toNat / 8 * 8 < 2 ^ 64 := by omega
  simp only [memoryRamCell, ramCellOfByteAddress, RamCell.baseAddr, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt cellBound, Nat.mod_eq_of_lt byteBound]

/-- A positive in-range memory instruction has its entire enclosing cell in the Sail domain. -/
theorem memoryRamCell_byte_lt {base : BitVec 64} {offset : BitVec 12} {width : ℕ}
    (positive : 0 < width)
    (inside : NativeLayout.guestMemory.ContainsSpan (memoryEffectiveAddress base offset).toNat width)
    (index : ℕ) (small : index < 8) :
    (memoryRamCell base offset).baseAddr.toNat + index < NativeLayout.sailMemory.upper := by
  rw [memoryRamCell_baseAddr]
  change _ < 2 ^ 48
  have upper : (memoryEffectiveAddress base offset).toNat + width ≤ 2 ^ 48 := inside.2
  omega

/-- Native memory encodings and complete byte domains discharge the extractor's actual RAM reads. -/
theorem instructionMemoryEncoded.cells_present {decoded : instruction} {source target : SailState}
    (encoded : instructionMemoryEncoded source.get_reg? decoded)
    (image : instructionImageOK decoded = true)
    (incoming : ∀ address < NativeLayout.sailMemory.upper, (source.mem.get? address).isSome)
    (outgoing : ∀ address < NativeLayout.sailMemory.upper, (target.mem.get? address).isSome) :
    InstructionCellsPresent decoded source target := by
  cases decoded <;> try trivial
  · rename_i args
    rcases args with ⟨offset, rs1, rd, unsigned, width⟩
    obtain ⟨base, observed, inside, _⟩ := encoded
    intro actual observedActual
    have same := Option.some.inj (observed.symm.trans observedActual)
    subst actual
    have positive : 0 < width.toNat := by
      simp only [instructionImageOK, loadWidthOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at image
      rcases image with ((rfl | rfl) | rfl) | ⟨rfl, _⟩ <;> decide
    exact ⟨ramWord64?_isSome_of_present source _ (fun i hi => incoming _ (memoryRamCell_byte_lt positive inside i hi)),
      ramWord64?_isSome_of_present target _ (fun i hi => outgoing _ (memoryRamCell_byte_lt positive inside i hi))⟩
  · rename_i args
    rcases args with ⟨offset, rs2, rs1, width⟩
    obtain ⟨base, observed, inside, _⟩ := encoded
    intro actual observedActual
    have same := Option.some.inj (observed.symm.trans observedActual)
    subst actual
    have positive : 0 < width.toNat := by
      simp only [instructionImageOK, storeWidthOK, Bool.or_eq_true, beq_iff_eq] at image
      rcases image with ((rfl | rfl) | rfl) | rfl <;> decide
    exact ⟨ramWord64?_isSome_of_present source _ (fun i hi => incoming _ (memoryRamCell_byte_lt positive inside i hi)),
      ramWord64?_isSome_of_present target _ (fun i hi => outgoing _ (memoryRamCell_byte_lt positive inside i hi))⟩

/-- Successful supported execution supplies a canonical, well-formed access plan. -/
theorem ordinary_accessPlan {decoded : instruction} {source target : SailState}
    (configured : SailConfigured source) (nextConfigured : SailConfigured target)
    (image : instructionImageOK decoded = true) (routed : (instructionRouteId decoded).isSome)
    (encoded : instructionMemoryEncoded source.get_reg? decoded)
    (incoming : ∀ address < NativeLayout.sailMemory.upper, (source.mem.get? address).isSome)
    (outgoing : ∀ address < NativeLayout.sailMemory.upper, (target.mem.get? address).isSome) :
    ∃ plan, instructionAccessPlan? decoded source target = some plan ∧ plan.WellFormed ∧ plan.length ≤ 3 := by
  obtain ⟨plan, generated⟩ := Option.isSome_iff_exists.mp (instructionAccessPlan?_isSome routed
    (fun index => Option.isSome_iff_exists.mpr (Advance.initialized_gpr source configured.init index))
    (fun index => Option.isSome_iff_exists.mpr (Advance.initialized_gpr target nextConfigured.init index))
    (encoded.cells_present image incoming outgoing))
  exact ⟨plan, generated, instructionAccessPlan_wellFormed generated, instructionAccessPlan_length_le_three generated⟩

/-- The canonical transition view and its access plan both succeed on complete native states. -/
theorem ordinaryEncodedAt.project {program : GuestProgram} {located : LocatedTransition}
    (encoded : ordinaryEncodedAt program located.source)
    (configured : SailConfigured located.source) (nextConfigured : SailConfigured located.transition.target)
    (incoming : ∀ address < NativeLayout.sailMemory.upper, (located.source.mem.get? address).isSome)
    (outgoing : ∀ address < NativeLayout.sailMemory.upper, (located.transition.target.mem.get? address).isSome) :
    ∃ view plan, projectSP1Transition? program located = some view ∧
      view.accessPlan? = some plan ∧ plan.WellFormed ∧ plan.length ≤ 3 := by
  obtain ⟨pc, word, decoded, atPc, fetched, decode, image, routed, memory⟩ := encoded
  obtain ⟨plan, generated, wellFormed, length⟩ :=
    ordinary_accessPlan configured nextConfigured image routed memory incoming outgoing
  have observed := decodeLocated?_eq_some_of atPc fetched (decode located.source configured)
  obtain ⟨id, route⟩ := Option.isSome_iff_exists.mp routed
  obtain ⟨key, keyEq⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind routed)
  refine ⟨⟨pc, word, decoded, key, id, some plan⟩, plan, ?_, rfl, wellFormed, length⟩
  simp [projectSP1Transition?, atPc, fetched, observed, image, keyEq, route, generated]

/-- Actual ordinary execution supplies both states needed by the canonical projection. -/
theorem ExecutionStep.project_ordinary {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} (step : ExecutionStep policy program source .ordinary target)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (permitted : InstructionWrite.PermittedAt policy.memory.readOnly program source.sail)
    (encoded : ordinaryEncodedAt program source.sail)
    (incoming : ∀ address < NativeLayout.sailMemory.upper, (source.sail.mem.get? address).isSome) :
    ∃ view plan, projectSP1Transition? program ⟨source.sail, ⟨.ordinary, target.sail⟩⟩ = some view ∧
      view.accessPlan? = some plan ∧ plan.WellFormed ∧ plan.length ≤ 3 := by
  have next := step.frame configured loaded (fun _ => permitted)
  exact encoded.project configured next.1 incoming (fun address inside =>
    step.memory_present configured loaded (fun _ => permitted) address (incoming address inside))

end SP1Clean.Model.Core
