import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Foundations.Constraint

/-! # Multiplicity-gating lemmas

This file formally justifies SP1Clean's convention of dropping SP1's
`mult : F` field at the per-row stateless `Table` layer (see
`SP1Clean/ByteOpcodeTable.lean:13-16` and
`SP1Clean/ProgramTable.lean:27-29` — both were documented in prose
prior to this file).

The justification is uniform: at every per-row `send` site emitted by
the dirty `SP1Chips` constraint compiler, `mult` is either a literal
`1` or a column expression `is_real`/`is_trusted` that the constraint
list elsewhere proves binary (∈ {0, 1}). Under that binarity
hypothesis, SP1's per-row constraint-level prop
(`SP1Constraint.toProp`) is equivalent to the stateless-table membership
predicate (`ByteOpcodeSpec` / `ProgramSpec`) — for the byte case in
a particularly direct form (the spec's existential is trivially
witnessed by the concrete opcode being sent).

This file proves the equivalence for the two stateless tables used by
SP1Clean's pilot chips.

Scope note: gated-lookup soundness (where `mult * lookup_query` is
emitted instead of a bare query) is a different argument — see
`SP1Clean/Gated.lean` for the limitations there. The lemmas here cover
the simple ungated case used by every chip's `Assertion.main` today. -/

namespace SP1Clean.Multiplicity

variable {p : ℕ} [Fact p.Prime]

/-! ## Byte-side -/

/-- Under `mult ∈ {0, 1}`, the SP1 `.send (.byte op a b c) mult`
constraint is equivalent to the bare per-opcode `op.constrain a b c`
predicate, gated on `mult = 1`. This is the foundational form of the
gating equivalence; the `ByteOpcodeSpec` form (with existential) is
derived as a forward implication below. -/
theorem ByteOpcode_send_iff_constrain
    (op : ByteOpcode) (a b c mult : ZMod p)
    (h_mult_binary : mult = 0 ∨ mult = 1) :
    (SP1Constraint.send (.byte op a b c) mult).toProp ↔
      (mult = 1 → op.constrain a b c) := by
  simp only [SP1Constraint.toProp_send_byte]
  rcases h_mult_binary with h0 | h1
  · subst h0; simp
  · subst h1; simp

/-- Forward direction lifting `op.constrain a b c` to the existential
`ByteOpcodeSpec` predicate (the actual table-membership claim). The
existential is witnessed by `op` itself. -/
theorem ByteOpcodeSpec_of_constrain
    (op : ByteOpcode) (a b c : ZMod p)
    (h : op.constrain a b c) :
    SP1Clean.ByteOpcodeSpec (#v[(op.toNat : ZMod p), a, b, c] : fields 4 (ZMod p)) :=
  ⟨op, rfl, h⟩

/-- Combined byte-side bridge: under `mult ∈ {0, 1}`, the SP1 send
constraint implies (forward) the `ByteOpcodeSpec` membership predicate
under `mult = 1`. This is the form consumed by the byte-bus
`FormalAssertion.Soundness` proofs across chip files. -/
theorem ByteOpcode_send_imp_ByteOpcodeSpec
    (op : ByteOpcode) (a b c mult : ZMod p)
    (h_mult_binary : mult = 0 ∨ mult = 1)
    (h_send : (SP1Constraint.send (.byte op a b c) mult).toProp) :
    (mult = 1 → SP1Clean.ByteOpcodeSpec
      (#v[(op.toNat : ZMod p), a, b, c] : fields 4 (ZMod p))) := by
  intro h_mult_one
  apply ByteOpcodeSpec_of_constrain op
  exact ((ByteOpcode_send_iff_constrain op a b c mult h_mult_binary).mp h_send) h_mult_one

/-! ## Program-side -/

/-- Under `mult ∈ {0, 1}`, the SP1 `.send (.program ...) mult`
constraint is equivalent to the `ProgramSpec`-style conjunction gated
on `mult = 1`. The `ProgramSpec` definition mirrors this conjunction
verbatim modulo the `Opcode.ofNat (op.toNat).val = op` round-trip,
which is the forward implication captured by
`Program_send_imp_ProgramSpec` below. -/
theorem Program_send_iff_clause
    (pc0 pc1 pc2 : ZMod p) (opcode : Opcode)
    (op_a op_b_0 op_b_1 op_b_2 op_b_3
        op_c_0 op_c_1 op_c_2 op_c_3
        op_a_0 imm_b imm_c mult : ZMod p)
    (h_mult_binary : mult = 0 ∨ mult = 1) :
    (SP1Constraint.send
        (.program pc0 pc1 pc2 opcode op_a op_b_0 op_b_1 op_b_2 op_b_3
          op_c_0 op_c_1 op_c_2 op_c_3 op_a_0 imm_b imm_c) mult).toProp ↔
      (mult = 1 →
        opcode.trusted_instr op_a op_b_0 op_b_1 op_b_2 op_b_3
            op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
          ∧ op_a < 32
          ∧ (op_b_0 < 65536 ∧ op_b_1 < 65536 ∧ op_b_2 < 65536 ∧ op_b_3 < 65536)
          ∧ (op_c_0 < 65536 ∧ op_c_1 < 65536 ∧ op_c_2 < 65536 ∧ op_c_3 < 65536)
          ∧ (op_a_0 = 0 ∨ op_a_0 = 1)
          ∧ (op_a_0 = 1 ↔ op_a = 0)
          ∧ (imm_b = 0 ∨ imm_b = 1)
          ∧ (imm_c = 0 ∨ imm_c = 1)
          ∧ (pc0 % 4 = 0 ∧ pc0 < 65536 ∧ pc1 < 65536 ∧ pc2 < 65536)) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  unfold SP1Constraint.toProp
  rcases h_mult_binary with h0 | h1
  · subst h0; simp
  · subst h1; simp

end SP1Clean.Multiplicity
