import SP1Clean.Model.Core.SyscallCode
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Math.WordEquality
import ToClean.Circuit.StaticTable

/-! # A fixed table of complete canonical syscall words

Membership constrains all four field limbs. The table is computed from the semantic eight-call
inventory and cannot be replaced by prover-supplied rows.
-/

namespace SP1Clean.Model.Core.SyscallKind

open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def encode (kind : SyscallKind) : Word (ZMod p) := bitVecToWord kind.code

@[irreducible] def fixedTable : StaticTable (ZMod p) Word :=
  StaticTable.ofRows "sp1.native.syscall_code" (all.map encode)

/-- The fixed lookup is exactly canonical encoding of a supported semantic word. -/
theorem fixedTable_spec (word : Word (ZMod p)) :
    (fixedTable (p := p)).Spec word ↔ word.isU64 ∧ Supported word.toBitVec64 := by
  rw [fixedTable]
  change word ∈ all.map encode ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨kind, _, rfl⟩
    exact ⟨isU64_bitVecToWord _, kind, (toBitVec64_bitVecToWord _).symm⟩
  · rintro ⟨bound, kind, equal⟩
    refine ⟨kind, mem_all kind, Word.eq_of_toBitVec64_eq (isU64_bitVecToWord _) bound ?_⟩
    exact (toBitVec64_bitVecToWord _).trans equal

omit [Fact (2 ^ 17 < p)] in
theorem encode_spec (kind : SyscallKind) : (fixedTable (p := p)).Spec (encode kind) := by
  rw [fixedTable]
  change encode kind ∈ all.map encode
  exact List.mem_map_of_mem (mem_all kind)

end SP1Clean.Model.Core.SyscallKind
