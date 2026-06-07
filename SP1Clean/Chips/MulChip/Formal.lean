import SP1Clean.Chips.MulChip.Defs

/-! # `SP1Clean.MulChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.MulChip

open Circuit
open Extracted (MulCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Operands are 64-bit values (true on real and zero-padded rows). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: the operand `isU64`s plus the `is_real` binary selector. (The
threaded reader-block `Spec`s would be added here when the soundness/completeness proofs are filled in.) -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧ (input.is_real = 0 ∨ input.is_real = 1)

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hbU, hcU⟩ := h_assumptions
  obtain ⟨_hcpu, h_mulop, ha0, ha1, ha2, ha3, gb_mul, gb_mulh, gb_mulhu, gb_mulhsu, gb_mulw,
    gb_sum, hopa0, _hadapter, h_gate⟩ := h_holds
  have bmul := bool_of_mul_pred gb_mul
  have bmulh := bool_of_mul_pred gb_mulh
  have bmulhu := bool_of_mul_pred gb_mulhu
  have bmulhsu := bool_of_mul_pred gb_mulhsu
  have bmulw := bool_of_mul_pred gb_mulw
  have bsum := bool_of_mul_pred gb_sum
  have h_bin := bool_of_mul_pred h_gate
  -- `is_mulw = 1 → is_real = 1`, where the gate `is_real` is the flag-sum (SP1 `alu/mul/mod.rs:234`):
  -- one-hot via `sum_eq_one`. This is the (faithful) precondition the demoted `MulOperation` now needs.
  have h_mw := fun (hmw : (env.get (i₀ + 4) : ZMod p) = 1) =>
    MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  -- the gated `MulOperation.Assumptions` (operands `isU64` only when active; flag binaries; `is_mulw →
  -- is_real`; sum-bound). The input (incl `cols`/`is_real`) is inferred at each use site (from `h_mulop`'s
  -- domain / the requirement goal / `result_semantic`'s unification), so it never needs writing out.
  have h_spec := h_mulop ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩
  refine ⟨fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr h_bin,
    Or.inr ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩, Or.inr h_bin⟩
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inl h1)
    obtain ⟨_hisU64, hmul, _hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mul_eq, ← hmul h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inl h1))
    obtain ⟨_hisU64, _hmul, _hmulhu, hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulh_eq, ← hmulh h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inl h1)))
    obtain ⟨_hisU64, _hmul, hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhu_eq, ← hmulhu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhsu_eq, ← hmulhsu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, _hmulhsu, hmulw⟩ :=
      MulOperation.result_semantic ⟨fun _ => ⟨hbU, hcU⟩, bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulw_eq, ← hmulw h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  sorry

/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract, composing the demoted `MulOperation` `FormalAssertion` over `populate`-witnessed
`cols` (gated by the flag-sum, as SP1); output is the extracted `MulCols` column struct. **Soundness is
proven and axiom-clean** (consumes `MulOperation.result_semantic`); completeness is deferred (`sorry`) — it
needs a `MulOperation.spec_populate` (the schoolbook `populate` satisfies the structural `Spec`), the same
heavy-arithmetic deferral as the Shift chips. The native `populate` is already conformance-checked against
SP1's real `populate` (`WitnessTests/MulOperationWitness.lean`, `native_decide`). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs MulCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.MulChip
