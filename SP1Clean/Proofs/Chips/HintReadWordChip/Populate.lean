import SP1Clean.Proofs.Chips.HintReadWordChip.Formal
import SP1Clean.Proofs.Operations.HintReadStepPopulate
import SP1Clean.Proofs.Chips.HostRamAccessChip.Populate
import SP1Clean.Proofs.Operations.HintReadSpanPopulate

/-! # Constructing physical hint word consumers

The constructor retains the physical RAM transfer, node, and index, and computes the next
cursor. Its completeness domain consists of the existing RAM constructor domain and exact
index/address bounds, which a complete permitted span supplies.
-/

namespace SP1Clean.HintReadWordChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (last : Bool) (ram : HostRamAccessChip.Inputs (ZMod p))
    (pointer index : fields 3 (ZMod p)) : Inputs (ZMod p) :=
  let step := HintReadStep.populate last ⟨pointer, index, ram.new_value, if last then 1 else 0⟩
    #v[ram.addr0, ram.addr1, ram.addr2]
  ⟨ram, pointer, index, step.nextIndex, step.nextAddress⟩

theorem populate_assumptions (last : Bool) (ram : HostRamAccessChip.Inputs (ZMod p))
    (pointer index : fields 3 (ZMod p)) (valid : HostRamAccessChip.ProverAssumptions ram)
    (pointerBound : Address.Bounded pointer) (positive : 0 < Address.toNat pointer)
    (indexBound : Address.Bounded index) (indexFits : Address.toNat index + 1 < 2 ^ 48)
    (addressFits : last = false → Address.toNat #v[ram.addr0, ram.addr1, ram.addr2] + 8 < 2 ^ 48) :
    ProverAssumptions last (populate last ram pointer index) := by
  refine ⟨valid, ?_⟩
  apply HintReadStep.populate_spec last
    ⟨pointer, index, ram.new_value, if last then 1 else 0⟩ #v[ram.addr0, ram.addr1, ram.addr2]
  · refine ⟨pointerBound, positive, indexBound, valid.2.1, ?_⟩
    cases last <;> simp
  · rfl
  · exact Address.bounded_of_isU64_asWord valid.1.1
  · exact indexFits
  · exact addressFits

/-- A checked padded span supplies every extra successor bound for each physical word. -/
theorem populate_assumptions_of_span (span : HintReadSpan.Inputs (ZMod p))
    (checked : HintReadSpan.Spec span) (ram : HostRamAccessChip.Inputs (ZMod p))
    (valid : HostRamAccessChip.ProverAssumptions ram) (pointer : fields 3 (ZMod p))
    (pointerBound : Address.Bounded pointer) (positive : 0 < Address.toNat pointer)
    (index : ℕ) (position : index < Address.toNat span.count)
    (address : Address.toNat #v[ram.addr0, ram.addr1, ram.addr2] = Address.toNat span.start + index * 8) :
    ProverAssumptions (decide (index + 1 = Address.toNat span.count))
      (populate (decide (index + 1 = Address.toNat span.count)) ram pointer (Address.ofNat index)) := by
  have countFits := Address.toNat_lt checked.2.2.2.2.2.1
  have indexFits : index < 2 ^ 48 := by omega
  apply populate_assumptions _ _ _ _ valid pointerBound positive (Address.bounded_ofNat _)
  · rw [Address.toNat_ofNat _ indexFits]
    omega
  · intro notLast
    have different : index + 1 ≠ Address.toNat span.count := by simpa using notLast
    have next := checked.word_window (index + 1) (by omega)
    rw [address]
    omega

end SP1Clean.HintReadWordChip
