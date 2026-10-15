module

public import SP1Clean.Semantics.Specs.LtSigned
public import SP1Clean.Circuits.Gadgets.LtUnsigned
public import SP1Clean.Circuits.Gadgets.U16MSB
public import SP1Clean.Model.Channels
public import Clean.Gadgets.Equality
import ToClean.Circuit.IteDecide
import Clean.Utils.Tactics.CircuitProofStart
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! # Native signed and unsigned word comparison

The bundled assertion composes two high-bit checks and unsigned comparison. Sign-bias
arithmetic connects their certificate to whole-word signed order. The public contract describes
the chosen mode and result; private algebraic evidence proves equivalence with the AIR.
Witness generation and its IR remain colocated with soundness and completeness.
-/

@[expose] public section

namespace SP1Clean.LtOperationSigned

open Circuit
open SP1Clean.Channels (byteChannel)
open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Sign-bias arithmetic

The signed compare flips bit 15 of the top limb (bit 63 of the word): the adjusted limb
`e13 = x + 32768 - 65536·msb` biases the value by `2^63 mod 2^64`, so an unsigned compare
of the adjusted words is the signed compare of the originals. -/

/-- The biased top limb `x + 32768 - 65536·msb` (with `msb = [x ≥ 2^15]`) is itself a 16-bit value,
and its `ℕ`-value lifts to the integer bias `x.val + 2^15 - 2^16·msb`. -/
private lemma adj_limb {x : ZMod p} (hx : x.val < 2 ^ 16) :
    ((x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val : ℤ)
        = (x.val : ℤ) + 32768 - 65536 * (if 32768 ≤ x.val then 1 else 0)
      ∧ (x + 32768 - 65536 * (if 32768 ≤ x.val then (1 : ZMod p) else 0)).val < 2 ^ 16 := by
  have hp : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  by_cases hsign : 32768 ≤ x.val
  · simp only [if_pos hsign, mul_one]
    have hval : (x + 32768 - 65536 : ZMod p).val = x.val - 32768 := by
      have e : ((x.val - 32768 : ℕ) : ZMod p) = x + 32768 - 65536 := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; push_cast; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val - 32768 < p by omega)
    rw [hval]; refine ⟨by omega, by omega⟩
  · simp only [if_neg hsign, mul_zero, sub_zero]
    have hval : (x + 32768 : ZMod p).val = x.val + 32768 := by
      have e : ((x.val + 32768 : ℕ) : ZMod p) = x + 32768 := by
        push_cast [ZMod.natCast_zmod_val]; ring
      rw [← e]; exact ZMod.val_natCast_of_lt (show x.val + 32768 < p by omega)
    rw [hval]; refine ⟨by push_cast; omega, by omega⟩

/-- **Sign-bias keystone.** For a 64-bit word `b`, the `toNat` of the word with its top limb biased
(bit 15 flipped: `e13 = b[3] + 2^15 - 2^16·[b[3] ≥ 2^15]`) equals `(toBitVec64 b).toInt + 2^63`. Hence
an unsigned `<` of two biased words is a signed `<` of the originals. -/
private lemma adj_bias {b : Word (ZMod p)} (hb : b.isU64) :
    ((Word.toNat (#v[b[0], b[1], b[2],
        b[3] + 32768 - 65536 * (if 32768 ≤ b[3].val then (1 : ZMod p) else 0)] : Word (ZMod p))) : ℤ)
      = (Word.toBitVec64 b).toInt + 2 ^ 63 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hval, _⟩ := adj_limb h3
  rw [Word.toNat_def, BitVec.toInt_eq_toNat_cond, Word.toBitVec64_toNat hb, Word.toNat_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hval ⊢
  by_cases hsign : 32768 ≤ b[3].val
  · rw [if_neg (by omega : ¬ 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_pos hsign] at hval ⊢; push_cast at hval ⊢; omega
  · rw [if_pos (by omega : 2 * (b[0].val + b[1].val * 2 ^ 16 + b[2].val * 2 ^ 32
        + b[3].val * 2 ^ 48) < 2 ^ 64)]
    simp only [if_neg hsign] at hval ⊢; push_cast at hval ⊢; omega

/-- Transfer: with the two top limbs biased by their sign bits, the **unsigned** `<` of the biased
words is the **signed** `<` (`toInt`) of the originals. -/
private lemma toInt_compare_of_bias {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64)
    {bm cm : ZMod p}
    (hbm : bm = if 32768 ≤ b[3].val then 1 else 0)
    (hcm : cm = if 32768 ≤ cc[3].val then 1 else 0) :
    (Word.toNat (#v[b[0], b[1], b[2], b[3] + 32768 - 65536 * bm] : Word (ZMod p))
        < Word.toNat (#v[cc[0], cc[1], cc[2], cc[3] + 32768 - 65536 * cm] : Word (ZMod p)))
      ↔ (Word.toBitVec64 b).toInt < (Word.toBitVec64 cc).toInt := by
  subst hbm hcm
  have hb' := adj_bias hb
  have hcc' := adj_bias hcc
  omega

omit [Fact (2 ^ 17 < p)] in
/-- For 64-bit words, `toBitVec64` equality is `toNat` equality (it round-trips through `toNat`). Used
to carry the unsigned core's `toNat`-equality up to the signed semantics' `toBitVec64` equality. -/
private lemma toBitVec64_eq_iff {b cc : Word (ZMod p)} (hb : b.isU64) (hcc : cc.isU64) :
    (Word.toBitVec64 b = Word.toBitVec64 cc) ↔ (Word.toNat b = Word.toNat cc) := by
  constructor
  · intro h; rw [← Word.toBitVec64_toNat hb, ← Word.toBitVec64_toNat hcc, h]
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [Word.toBitVec64_toNat hb, Word.toBitVec64_toNat hcc, h]

/-- Check the comparison certificate using two high-bit assertions and an unsigned comparison. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let cc := input.cc
  let cols := input.cols
  let is_signed := input.is_signed
  let is_real := input.is_real
  let bAdjusted := #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * cols.b_msb.msb]
  let cAdjusted := #v[cc[0], cc[1], cc[2], cc[3] + is_signed * 32768 - 65536 * cols.c_msb.msb]
  assertion U16MSBOperation.circuit ⟨b[3], { msb := cols.b_msb.msb }, is_signed⟩
  assertion U16MSBOperation.circuit ⟨cc[3], { msb := cols.c_msb.msb }, is_signed⟩
  assertion LtOperationUnsigned.circuit
    ⟨bAdjusted, cAdjusted,
      { u16_compare_operation := { bit := cols.result.u16_compare_operation.bit }
        u16_flags := #v[cols.result.u16_flags[0], cols.result.u16_flags[1],
          cols.result.u16_flags[2], cols.result.u16_flags[3]]
        not_eq_inv := cols.result.not_eq_inv
        comparison_limbs := #v[cols.result.comparison_limbs[0], cols.result.comparison_limbs[1]] },
      is_real⟩
  is_signed * (is_signed - 1) === 0
  is_real * (is_real - 1) === 0
  (is_real - 1) * is_signed === 0
  (is_signed - 1) * cols.b_msb.msb === 0
  (is_signed - 1) * cols.c_msb.msb === 0

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit_with {
    channelsWithGuarantees := [byteChannel.toRaw]
  }

@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- Keep the signed-compare interaction boundary folded for enclosing whole-chip proofs.  The gadget
emits only the byte interactions of its two MSB checks and unsigned comparison; its five local
equalities emit none. -/
theorem interactionsWith_byte_eq
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      ((U16MSBOperation.main
        ⟨input.b[3], { msb := input.cols.b_msb.msb },
          input.is_signed⟩).operations offset).interactionsWith
            byteChannel.toRaw ++
      ((U16MSBOperation.main
        ⟨input.cc[3], { msb := input.cols.c_msb.msb },
          input.is_signed⟩).operations offset).interactionsWith
            byteChannel.toRaw ++
      ((LtOperationUnsigned.main
        ⟨#v[input.b[0], input.b[1], input.b[2],
              input.b[3] + input.is_signed * 32768 -
                65536 * input.cols.b_msb.msb],
          #v[input.cc[0], input.cc[1], input.cc[2],
              input.cc[3] + input.is_signed * 32768 -
                65536 * input.cols.c_msb.msb],
          { u16_compare_operation :=
              { bit := input.cols.result.u16_compare_operation.bit }
            u16_flags :=
              #v[input.cols.result.u16_flags[0],
                input.cols.result.u16_flags[1],
                input.cols.result.u16_flags[2],
                input.cols.result.u16_flags[3]]
            not_eq_inv := input.cols.result.not_eq_inv
            comparison_limbs :=
              #v[input.cols.result.comparison_limbs[0],
                input.cols.result.comparison_limbs[1]] },
          input.is_real⟩).operations offset).interactionsWith
            byteChannel.toRaw := by
  simp only [main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions,
    U16MSBOperation.circuit, LtOperationUnsigned.circuit,
    Gadgets.Equality.main, List.filter_nil, List.append_nil]
  rfl

/-- Fully witnessed `LtOperationSigned` column struct (SP1's `populate`): the two `is_signed`-gated
sign bits and the `LtOperationUnsigned` compare columns on the sign-adjusted words — the latter zeroed
on a padding row (`is_real = 0`), where the threaded unsigned compare contributes nothing. -/
def populate (b cc : Word (ZMod p)) (is_signed is_real : ZMod p) :
    Circuits.Types.LtOperationSigned (ZMod p) :=
  let bm := is_signed * U16MSBOperation.populate_msb b[3]
  let cm := is_signed * U16MSBOperation.populate_msb cc[3]
  let bAdj : Word (ZMod p) := #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * bm]
  let cAdj : Word (ZMod p) := #v[cc[0], cc[1], cc[2], cc[3] + is_signed * 32768 - 65536 * cm]
  let result : Circuits.Types.LtOperationUnsigned (ZMod p) :=
    if is_real = 1 then LtOperationUnsigned.populate bAdj cAdj
    else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩
  ⟨result, ⟨bm⟩, ⟨cm⟩⟩

/-! ### Witness IR

The struct-shaped `FExpr` twin of `populate` (the `BitwiseU16Operation.populateFE` pattern): the
two `is_signed`-gated sign bits (`populate_msbF`'s first consumers), the sign-adjusted limb
expressions, and the `LtOperationUnsigned` scan twins instantiated at them — each unsigned cell
wrapped in the `is_real` gate that mirrors the value side's `if is_real = 1 … else zeroCols`.
Deliberately **not** `@[circuit_norm]`; only the lemmas below cross the boundary. -/

/-- The sign-adjusted limb expressions (`b[3] + is_signed·2^15 − 2^16·msb`), as witness IR. -/
def adjLimbsF (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  #v[.expr w[0], .expr w[1], .expr w[2],
     .expr w[3] + .expr is_signed * (32768 : Witgen.FExpr (ZMod p))
       - (65536 : Witgen.FExpr (ZMod p))
           * (.expr is_signed * U16MSBOperation.populate_msbF (.expr w[3]))]

/-- The witness-IR twin of `populate`, over the chip's input expressions (`is_signed` is the chip's
witnessed flag cell; `is_real` the input selector). -/
def populateFE (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p)) :
    Circuits.Types.LtOperationSigned (Witgen.FExpr (ZMod p)) :=
  let bAdj := adjLimbsF b is_signed
  let cAdj := adjLimbsF cc is_signed
  let gate : Witgen.FExpr (ZMod p) → Witgen.FExpr (ZMod p) :=
    fun e => .ite (is_real =? (1 : ZMod p)) e 0
  ⟨⟨⟨gate (LtOperationUnsigned.compareBitF bAdj cAdj)⟩,
    #v[gate (LtOperationUnsigned.flagsF bAdj cAdj 0), gate (LtOperationUnsigned.flagsF bAdj cAdj 1),
       gate (LtOperationUnsigned.flagsF bAdj cAdj 2), gate (LtOperationUnsigned.flagsF bAdj cAdj 3)],
    gate (LtOperationUnsigned.notEqInvF bAdj cAdj),
    #v[gate (LtOperationUnsigned.comparisonLimbsF bAdj cAdj 0),
       gate (LtOperationUnsigned.comparisonLimbsF bAdj cAdj 1)]⟩,
   ⟨.expr is_signed * U16MSBOperation.populate_msbF (.expr b[3])⟩,
   ⟨.expr is_signed * U16MSBOperation.populate_msbF (.expr cc[3])⟩⟩

section Navigators


/-- Cell `0` of a flattened `LtOperationSigned` struct is the compare bit. -/
private lemma toElements_cell_bit {F : Type} (s : Circuits.Types.LtOperationSigned F) :
    (toElements s)[0]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.result.u16_compare_operation.bit := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
  refine (Vector.getElem_append_left ?_).trans
    ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_left ?_).trans
      ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

/-- Cell `1 + k` (`k < 4`) is the `k`-th one-hot flag. -/
private lemma toElements_cell_flag {F : Type} (s : Circuits.Types.LtOperationSigned F)
    (k : ℕ) (hk : k < 4) :
    (toElements s)[1 + k]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.result.u16_flags[k] := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
         (Vector.getElem_append_left ?_))) <;> decide)

/-- Cell `5` is the non-equality inverse. -/
private lemma toElements_cell_notEqInv {F : Type} (s : Circuits.Types.LtOperationSigned F) :
    (toElements s)[5]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.result.not_eq_inv := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
  refine (Vector.getElem_append_left ?_).trans
    ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

/-- Cell `6 + k` (`k < 2`) is the `k`-th comparison limb. -/
private lemma toElements_cell_compLimb {F : Type} (s : Circuits.Types.LtOperationSigned F)
    (k : ℕ) (hk : k < 2) :
    (toElements s)[6 + k]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.result.comparison_limbs[k] := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_right ?_ ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
           (Vector.getElem_append_left ?_))))) <;> decide)

/-- Cell `8` is the gated `b` sign bit. -/
private lemma toElements_cell_bMsb {F : Type} (s : Circuits.Types.LtOperationSigned F) :
    (toElements s)[8]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.b_msb.msb := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_left ?_).trans
      ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_))) <;> decide

/-- Cell `9` is the gated `c` sign bit. -/
private lemma toElements_cell_cMsb {F : Type} (s : Circuits.Types.LtOperationSigned F) :
    (toElements s)[9]'(by have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl; omega)
      = s.c_msb.msb := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_left ?_).trans
        ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

end Navigators

/-- The evaluated sign-adjusted word (the value `populate`'s internal `bAdj`/`cAdj`). -/
private def adjVal (v : Word (ZMod p)) (vs : ZMod p) : Word (ZMod p) :=
  #v[v[0], v[1], v[2],
     v[3] + vs * 32768 - 65536 * (vs * U16MSBOperation.populate_msb v[3])]

omit [Fact (2 ^ 17 < p)] in
private lemma adjLimbsF_eval (env : ProverEnvironment (ZMod p))
    (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) (v : Word (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment w[i] = v[i])
    (hv3 : v[3].val < 2 ^ 16) :
    ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF w is_signed)[i]).eval { env := env }
      = (adjVal v (Expression.eval env.toEnvironment is_signed))[i] := by
  have hW0 := hW 0 (by omega); have hW1 := hW 1 (by omega)
  have hW2 := hW 2 (by omega); have hW3 := hW 3 (by omega)
  have hmsb := U16MSBOperation.populate_msbF_eval { env := env } (.expr w[3])
    (by simpa [circuit_norm, hW3] using hv3)
  intro i h
  interval_cases i <;>
    simp only [adjLimbsF, adjVal, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hmsb,
      hW0, hW1, hW2, hW3]

omit [Fact (2 ^ 17 < p)] in
private lemma msbF_eval (env : ProverEnvironment (ZMod p))
    (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) (v : Word (ZMod p))
    (hW3 : Expression.eval env.toEnvironment w[3] = v[3]) (hv3 : v[3].val < 2 ^ 16) :
    (Witgen.FExpr.expr is_signed * U16MSBOperation.populate_msbF (.expr w[3])).eval { env := env }
      = Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb v[3] := by
  have hmsb := U16MSBOperation.populate_msbF_eval { env := env } (.expr w[3])
    (by simpa [circuit_norm, hW3] using hv3)
  simp only [circuit_norm, hmsb, hW3]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the witness IR is exactly `populate` on the evaluated operands (the
`BitwiseU16Operation.populateFE_eval` statement shape; the `isU64` bounds feed the sign-bit
divisions, and one `is_real` case split resolves every gate on both sides at once). -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (vb vcc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvcc : #v[Expression.eval env.toEnvironment cc[0], Expression.eval env.toEnvironment cc[1],
               Expression.eval env.toEnvironment cc[2],
               Expression.eval env.toEnvironment cc[3]] = vcc)
    (hb : vb.isU64) (hcc : vcc.isU64) :
    Witgen.eval { env := env } (populateFE b cc is_signed is_real)
      = populate vb vcc (Expression.eval env.toEnvironment is_signed)
          (Expression.eval env.toEnvironment is_real) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  have hC : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment cc[i] = vcc[i] := by
    intro i h; rw [← hvcc]; interval_cases i <;> simp
  have hAdjB := adjLimbsF_eval env b is_signed vb hB hb3
  have hAdjC := adjLimbsF_eval env cc is_signed vcc hC hc3
  obtain ⟨hCL, hFL, hNI, hBit⟩ := LtOperationUnsigned.scanF_eval { env := env }
    (adjLimbsF b is_signed) (adjLimbsF cc is_signed)
    (adjVal vb (Expression.eval env.toEnvironment is_signed))
    (adjVal vcc (Expression.eval env.toEnvironment is_signed)) hAdjB hAdjC
  have hbmF := msbF_eval env b is_signed vb (hB 3 (by omega)) hb3
  have hcmF := msbF_eval env cc is_signed vcc (hC 3 (by omega)) hc3
  have hpop : populate vb vcc (Expression.eval env.toEnvironment is_signed)
        (Expression.eval env.toEnvironment is_real)
      = ⟨if Expression.eval env.toEnvironment is_real = 1 then
           LtOperationUnsigned.populate
             (adjVal vb (Expression.eval env.toEnvironment is_signed))
             (adjVal vcc (Expression.eval env.toEnvironment is_signed))
         else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩,
         ⟨Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb vb[3]⟩,
         ⟨Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb vcc[3]⟩⟩ := rfl
  rw [hpop]
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi10 : i < 10 := by
    have hsz : size Circuits.Types.LtOperationSigned = 10 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Circuits.Types.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  by_cases hreal : Expression.eval env.toEnvironment is_real = 1 <;>
  · interval_cases i
    · refine ((congrArg _ (toElements_cell_bit _)).trans ?_).trans (toElements_cell_bit _).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hBit]
    · refine ((congrArg _ (toElements_cell_flag _ 0 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 0 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 0]
    · refine ((congrArg _ (toElements_cell_flag _ 1 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 1 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 1]
    · refine ((congrArg _ (toElements_cell_flag _ 2 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 2 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 2]
    · refine ((congrArg _ (toElements_cell_flag _ 3 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 3 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 3]
    · refine ((congrArg _ (toElements_cell_notEqInv _)).trans ?_).trans
        (toElements_cell_notEqInv _).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hNI]
    · refine ((congrArg _ (toElements_cell_compLimb _ 0 (by omega))).trans ?_).trans
        (toElements_cell_compLimb _ 0 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hCL 0]
    · refine ((congrArg _ (toElements_cell_compLimb _ 1 (by omega))).trans ?_).trans
        (toElements_cell_compLimb _ 1 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hCL 1]
    · refine ((congrArg _ (toElements_cell_bMsb _)).trans ?_).trans (toElements_cell_bMsb _).symm
      simpa [populateFE, circuit_norm] using hbmF
    · refine ((congrArg _ (toElements_cell_cMsb _)).trans ?_).trans (toElements_cell_cMsb _).symm
      simpa [populateFE, circuit_norm] using hcmF


omit [Fact (2 ^ 17 < p)] in
/-- Elementwise corollary of `populateFE_eval`, in the exact per-cell shape the chip completeness
seam's witness obligations arrive in. -/
theorem populateFE_eval_cell (env : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (vb vcc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvcc : #v[Expression.eval env.toEnvironment cc[0], Expression.eval env.toEnvironment cc[1],
               Expression.eval env.toEnvironment cc[2],
               Expression.eval env.toEnvironment cc[3]] = vcc)
    (hb : vb.isU64) (hcc : vcc.isU64) (j : ℕ) (hj : j < 10) :
    Witgen.FExpr.eval { env := env }
        ((toElements (populateFE b cc is_signed is_real))[j]'(by
          have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl
          omega))
      = (toElements (populate vb vcc (Expression.eval env.toEnvironment is_signed)
          (Expression.eval env.toEnvironment is_real)))[j]'(by
          have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl
          omega) := by
  have h := congrArg
    (fun s : Circuits.Types.LtOperationSigned (ZMod p) => (toElements s)[j]'(by
      have h10 : size Circuits.Types.LtOperationSigned = 10 := rfl
      omega))
    (populateFE_eval env b cc is_signed is_real vb vcc hvb hvcc hb hcc)
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Circuits.Types.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements] at h
  simpa [Vector.getElem_map] using h

omit [Fact (2 ^ 17 < p)] in
/-- `ofFExprs`-of-`toElements` evaluation is the flattened struct evaluation. -/
private lemma ofFExprs_eval_eq (env : ProverEnvironment (ZMod p))
    (xs : Circuits.Types.LtOperationSigned (Witgen.FExpr (ZMod p))) :
    (Witgen.WitgenIR.ofFExprs (toElements xs)).eval env
      = toElements (Witgen.eval { env := env } xs) := by
  rw [show (Witgen.eval { env := env } xs : Circuits.Types.LtOperationSigned (ZMod p))
        = fromElements ((toElements xs).map (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements]
  apply Vector.ext
  intro i hi
  simp [circuit_norm, Vector.getElem_map]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the witness IR, in the raw `ofFExprs` payload form the
`ComputableWitnesses` obligations quantify over (a congruence, so it needs no bounds). -/
theorem populateFE_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment cc[i] = Expression.eval env'.toEnvironment cc[i])
    (hS : Expression.eval env.toEnvironment is_signed
      = Expression.eval env'.toEnvironment is_signed)
    (hR : Expression.eval env.toEnvironment is_real
      = Expression.eval env'.toEnvironment is_real) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFE b cc is_signed is_real))).eval env
      = (Witgen.WitgenIR.ofFExprs (toElements (populateFE b cc is_signed is_real))).eval env' := by
  have hmsbB := U16MSBOperation.populate_msbF_congr { env := env } { env := env' } (.expr b[3])
    (by simpa [circuit_norm] using hB 3 (by omega))
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' } (.expr cc[3])
    (by simpa [circuit_norm] using hC 3 (by omega))
  have hAdjB : ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF b is_signed)[i]).eval { env := env }
      = ((adjLimbsF b is_signed)[i]).eval { env := env' } := by
    intro i h
    interval_cases i <;>
      simp only [adjLimbsF, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, circuit_norm, -Witgen.u64Wrap, hmsbB, hS,
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
  have hAdjC : ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF cc is_signed)[i]).eval { env := env }
      = ((adjLimbsF cc is_signed)[i]).eval { env := env' } := by
    intro i h
    interval_cases i <;>
      simp only [adjLimbsF, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, circuit_norm, -Witgen.u64Wrap, hmsbC, hS,
        hC 0 (by omega), hC 1 (by omega), hC 2 (by omega), hC 3 (by omega)]
  obtain ⟨hCL, hFL, hNI, hBit⟩ := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (adjLimbsF b is_signed) (adjLimbsF cc is_signed) hAdjB hAdjC
  rw [ofFExprs_eval_eq, ofFExprs_eval_eq]
  refine congrArg toElements ?_
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi10 : i < 10 := by
    have hsz : size Circuits.Types.LtOperationSigned = 10 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Circuits.Types.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFE b cc is_signed is_real) :
          Circuits.Types.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bit _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hBit])).trans
      (congrArg _ (toElements_cell_bit _)).symm
  · exact ((congrArg _ (toElements_cell_flag _ 0 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 0])).trans
      (congrArg _ (toElements_cell_flag _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 1 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 1])).trans
      (congrArg _ (toElements_cell_flag _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 2 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 2])).trans
      (congrArg _ (toElements_cell_flag _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 3 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 3])).trans
      (congrArg _ (toElements_cell_flag _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_notEqInv _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hNI])).trans
      (congrArg _ (toElements_cell_notEqInv _)).symm
  · exact ((congrArg _ (toElements_cell_compLimb _ 0 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hCL 0])).trans
      (congrArg _ (toElements_cell_compLimb _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_compLimb _ 1 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hCL 1])).trans
      (congrArg _ (toElements_cell_compLimb _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bMsb _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hmsbB, hS])).trans
      (congrArg _ (toElements_cell_bMsb _)).symm
  · exact ((congrArg _ (toElements_cell_cMsb _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hmsbC, hS])).trans
      (congrArg _ (toElements_cell_cMsb _)).symm

private def ConstraintEvidence (input : Inputs (ZMod p)) : Prop :=
  let bm := input.cols.b_msb.msb
  let cm := input.cols.c_msb.msb
  let e13 := input.b[3] + input.is_signed * 32768 - 65536 * bm
  let e17 := input.cc[3] + input.is_signed * 32768 - 65536 * cm
  (input.is_signed = 0 ∨ input.is_signed = 1) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (bm = 0 ∨ bm = 1) ∧ (cm = 0 ∨ cm = 1) ∧
  ((input.is_real - 1) * input.is_signed = 0) ∧
  ((input.is_signed - 1) * bm = 0) ∧ ((input.is_signed - 1) * cm = 0) ∧
  (input.is_signed = 1 → bm = if input.b[3].val ≥ 32768 then 1 else 0) ∧
  (input.is_signed = 1 → cm = if input.cc[3].val ≥ 32768 then 1 else 0) ∧
  LtOperationUnsigned.Spec
    ⟨#v[input.b[0], input.b[1], input.b[2], e13],
     #v[input.cc[0], input.cc[1], input.cc[2], e17], input.cols.result, input.is_real⟩

/-- The composed `LtOperationUnsigned` sub-assertion's `main` reconstructs the result column vectors
element-wise (`#v[r.u16_flags[0], …]`); these eta lemmas fold them back to the whole vector so the
sub `Spec` matches the clean `input.cols.result`. -/
private lemma vec4_eta {α : Type} (v : Vector α 4) : #v[v[0], v[1], v[2], v[3]] = v := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl
private lemma vec2_eta {α : Type} (v : Vector α 2) : #v[v[0], v[1]] = v := by
  apply Vector.ext; intro i hi; interval_cases i <;> rfl

/-- The sign-adjusted top limb `x + s·2^15 - 2^16·m` is 16-bit on both branches of the binary `s`:
at `s = 0` the `(s-1)·m` gate forces `m = 0` and it is `x` itself; at `s = 1` it is `adj_limb`. -/
private lemma adj_top {x m s : ZMod p} (hx : x.val < 2 ^ 16) (hs : s = 0 ∨ s = 1)
    (hg : (s - 1) * m = 0) (hm : s = 1 → m = if x.val ≥ 32768 then 1 else 0) :
    (x + s * 32768 - 65536 * m).val < 2 ^ 16 := by
  rcases hs with h | h
  · rw [h] at hg
    have hm0 : m = 0 := by simpa using hg
    rw [h, hm0]; simpa using hx
  · rw [h, one_mul, hm h]; simpa using (adj_limb hx).2

omit [Fact (2 ^ 17 < p)] in
/-- Replacing a 64-bit word's top limb by any 16-bit value (here the sign-adjusted limb of
`adj_top`) leaves it 64-bit — the three low limbs are untouched. -/
private lemma isU64_top {b : Word (ZMod p)} {t : ZMod p} (hb : Word.isU64 b)
    (ht : t.val < 2 ^ 16) : Word.isU64 #v[b[0], b[1], b[2], t] := by
  obtain ⟨h0, h1, h2, -⟩ := Word.lt_cases_of_isU64 hb
  exact Word.isU64_of_cases (by simpa using h0) (by simpa using h1) (by simpa using h2)
    (by simpa using ht)

/-- Derive whole-word order from the composed certificates: on a real row the compare `bit`
is the signed (`is_signed = 1`, via `toInt`) / unsigned (`is_signed = 0`, via `toNat`) less-than
indicator, and in either mode the flags sum to `0` exactly when the words are equal. -/
private theorem result_of_evidence {input : Inputs (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc) (hir : input.is_real = 1)
    (hs : ConstraintEvidence input) : Result input := by
  obtain ⟨his, _hirb, _hbmb, _hcmb, _hg5, hg7, hg9, hbm_eq, hcm_eq, h_uns⟩ := hs
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  rcases his with hs0 | hs1
  · -- `is_signed = 0`: `bm = cm = 0`, the unsigned compare on the unbiased words.
    have hbm0 : input.cols.b_msb.msb = 0 := by rw [hs0] at hg7; linear_combination -hg7
    have hcm0 : input.cols.c_msb.msb = 0 := by rw [hs0] at hg9; linear_combination -hg9
    rw [hs0, hbm0, hcm0] at h_uns
    simp only [zero_mul, mul_zero, sub_zero, add_zero] at h_uns
    have hbit := LtOperationUnsigned.result_semantic h_uns hir
    refine ⟨?_, ?_⟩
    · rw [hbit.1]
      simp only [hs0, if_neg h01, Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      rfl
    · rw [toBitVec64_eq_iff hb hcc]
      have key := hbit.2
      simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at key ⊢
      exact key
  · -- `is_signed = 1`: `bm`/`cm` are the sign bits; the unsigned compare of the bias-flipped words.
    have hbm : input.cols.b_msb.msb = if input.b[3].val ≥ 32768 then 1 else 0 := hbm_eq hs1
    have hcm : input.cols.c_msb.msb = if input.cc[3].val ≥ 32768 then 1 else 0 := hcm_eq hs1
    rw [hs1] at h_uns
    simp only [one_mul] at h_uns
    have hbit := LtOperationUnsigned.result_semantic h_uns hir
    dsimp only at hbit
    refine ⟨?_, ?_⟩
    · rw [hbit.1]
      simp only [hs1, ↓reduceIte, toInt_compare_of_bias hb hcc hbm hcm]
    · rw [hbit.2, hbm, hcm, ← BitVec.toInt_inj]
      have hb' := adj_bias hb
      have hc' := adj_bias hcc
      rw [← Int.natCast_inj, hb', hc', add_right_cancel_iff]

/-- The semantic contract accepts exactly the existing assertion domain. In particular, padding
retains the unsigned comparator's noncanonical certificates. -/
private theorem spec_iff_evidence {input : Inputs (ZMod p)} (ha : Assumptions input) :
    Spec input ↔ ConstraintEvidence input := by
  constructor
  · rintro ⟨hr, hm, hu, _⟩
    rcases hm with ⟨hs0, hb0, hc0⟩ | ⟨hs1, hr1, hb, hc⟩
    · refine ⟨Or.inl hs0, hr, Or.inl hb0, Or.inl hc0, ?_, ?_, ?_, ?_, ?_, hu⟩
      · simp [hs0]
      · simp [hb0]
      · simp [hc0]
      · simp [hs0]
      · simp [hs0]
    · refine ⟨Or.inr hs1, hr, ?_, ?_, ?_, ?_, ?_, fun _ => hb, fun _ => hc, hu⟩
      · rw [hb]; split <;> simp
      · rw [hc]; split <;> simp
      · simp [hr1]
      · simp [hs1]
      · simp [hs1]
  · intro he
    have ⟨hs, hr, _, _, hg5, hg7, hg9, hb, hc, hu⟩ := he
    refine ⟨hr, ?_, hu, fun hr1 => result_of_evidence ha.1 ha.2.1 hr1 he⟩
    rcases hs with hs0 | hs1
    · left
      refine ⟨hs0, ?_, ?_⟩
      · rw [hs0] at hg7; simpa using hg7
      · rw [hs0] at hg9; simpa using hg9
    · right
      refine ⟨hs1, ?_, hb hs1, hc hs1⟩
      rw [hs1, mul_one, sub_eq_zero] at hg5
      exact hg5

/-- The canonical witness satisfies the private algebraic evidence. -/
private theorem evidence_populate {b cc : Word (ZMod p)} {is_signed is_real : ZMod p}
    (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (hs_bin : is_signed = 0 ∨ is_signed = 1) (hr_bin : is_real = 0 ∨ is_real = 1)
    (h_gate : (is_real - 1) * is_signed = 0) :
    ConstraintEvidence (⟨b, cc, populate b cc is_signed is_real, is_signed, is_real⟩ : Inputs (ZMod p)) := by
  obtain ⟨-, -, -, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨-, -, -, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have hpmb : U16MSBOperation.populate_msb b[3] = if b[3].val ≥ 32768 then 1 else 0 :=
    (U16MSBOperation.spec_populate (by simpa using hb3) 1).2 rfl
  have hpmc : U16MSBOperation.populate_msb cc[3] = if cc[3].val ≥ 32768 then 1 else 0 :=
    (U16MSBOperation.spec_populate (by simpa using hc3) 1).2 rfl
  have hbmb : U16MSBOperation.populate_msb b[3] = 0 ∨ U16MSBOperation.populate_msb b[3] = 1 :=
    U16MSBOperation.populate_msb_bool (by simpa using hb3)
  have hcmb : U16MSBOperation.populate_msb cc[3] = 0 ∨ U16MSBOperation.populate_msb cc[3] = 1 :=
    U16MSBOperation.populate_msb_bool (by simpa using hc3)
  have hbtop : (b[3] + is_signed * 32768 -
      65536 * (is_signed * U16MSBOperation.populate_msb b[3])).val < 2 ^ 16 := by
    rcases hs_bin with hs0 | hs1
    · simpa [hs0] using hb3
    · simpa [hs1, hpmb] using (adj_limb hb3).2
  have hctop : (cc[3] + is_signed * 32768 -
      65536 * (is_signed * U16MSBOperation.populate_msb cc[3])).val < 2 ^ 16 := by
    rcases hs_bin with hs0 | hs1
    · simpa [hs0] using hc3
    · simpa [hs1, hpmc] using (adj_limb hc3).2
  simp only [ConstraintEvidence, populate]
  refine ⟨hs_bin, hr_bin, ?_, ?_, h_gate, ?_, ?_, ?_, ?_, ?_⟩
  · -- `b_msb = is_signed * populate_msb` is boolean
    rcases hs_bin with h | h <;> rw [h]
    · left; ring
    · rw [one_mul]; exact hbmb
  · rcases hs_bin with h | h <;> rw [h]
    · left; ring
    · rw [one_mul]; exact hcmb
  · -- `(is_signed - 1) * (is_signed * populate_msb) = 0`
    rcases hs_bin with h | h <;> rw [h] <;> ring
  · rcases hs_bin with h | h <;> rw [h] <;> ring
  · -- `is_signed = 1 → b_msb = high bit`
    intro h1; rw [h1, one_mul, hpmb]
  · intro h1; rw [h1, one_mul, hpmc]
  · -- the composed `LtOperationUnsigned.Spec` on the sign-adjusted words
    by_cases hr1 : is_real = 1
    · subst hr1
      rw [if_pos rfl]
      exact LtOperationUnsigned.spec_populate (isU64_top hb hbtop) (isU64_top hcc hctop)
    · rw [if_neg hr1]
      have hr0 : is_real = 0 := Or.resolve_right hr_bin hr1
      subst hr0
      -- all-zero unsigned columns satisfy `LtOperationUnsigned.Spec` at `is_real = 0`
      exact LtOperationUnsigned.spec_zero _ _ rfl

/-- The witnessed columns `populate b cc is_signed is_real` satisfy the gadget `Spec`. The composing
chip uses this to discharge the `assertion LtOperationSigned.circuit` obligation. -/
theorem spec_populate {b cc : Word (ZMod p)} {is_signed is_real : ZMod p}
    (hb : Word.isU64 b) (hcc : Word.isU64 cc)
    (hs_bin : is_signed = 0 ∨ is_signed = 1) (hr_bin : is_real = 0 ∨ is_real = 1)
    (h_gate : (is_real - 1) * is_signed = 0) :
    Spec (⟨b, cc, populate b cc is_signed is_real, is_signed, is_real⟩ : Inputs (ZMod p)) := by
  exact (spec_iff_evidence ⟨hb, hcc, hr_bin, hs_bin⟩).2
    (evidence_populate hb hcc hs_bin hr_bin h_gate)

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  let row : Inputs (ZMod p) :=
    ⟨input_b, input_cc,
      ⟨⟨⟨input_cols_result_u16_compare_operation_bit⟩, input_cols_result_u16_flags,
          input_cols_result_not_eq_inv, input_cols_result_comparison_limbs⟩,
        ⟨input_cols_b_msb_msb⟩, ⟨input_cols_c_msb_msb⟩⟩,
      input_is_signed, input_is_real⟩
  apply (spec_iff_evidence (input := row) h_assumptions).2
  obtain ⟨hb_u64, hcc_u64, hir_bin, his_bin⟩ := h_assumptions
  obtain ⟨hib, hicc, ⟨⟨_, hflags, _, hcl⟩, _, _⟩, _, _⟩ := h_input
  have eb : ∀ i (hi : i < 4), Expression.eval env input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4),
      Expression.eval env input_var_cols_result_u16_flags[i] = input_cols_result_u16_flags[i] := by
    intro i hi; rw [← hflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2), Expression.eval env input_var_cols_result_comparison_limbs[i]
      = input_cols_result_comparison_limbs[i] := by
    intro i hi; rw [← hcl]; simp only [Vector.getElem_map]
  obtain ⟨-, -, -, hb3⟩ := Word.lt_cases_of_isU64 hb_u64
  obtain ⟨-, -, -, hc3⟩ := Word.lt_cases_of_isU64 hcc_u64
  obtain ⟨h_msb_b, h_msb_c, h_lt, _, _, hE5, hE7, hE9⟩ := h_holds
  simp only [eb, ec, ef, ecl, vec4_eta, vec2_eta]
    at h_msb_b h_msb_c h_lt hE5 hE7 hE9 ⊢
  -- the two `U16MSBOperation` sub-assertion `Assumptions` (16-bit operands, `is_signed` binary).
  have hAb : U16MSBOperation.circuit.Assumptions
      ⟨input_b[3], ⟨input_cols_b_msb_msb⟩, input_is_signed⟩ := ⟨fun _ => hb3, his_bin⟩
  have hAc : U16MSBOperation.circuit.Assumptions
      ⟨input_cc[3], ⟨input_cols_c_msb_msb⟩, input_is_signed⟩ := ⟨fun _ => hc3, his_bin⟩
  obtain ⟨hbm_bool, hbm_eq⟩ := h_msb_b hAb
  obtain ⟨hcm_bool, hcm_eq⟩ := h_msb_c hAc
  -- defeq-reduced forms (the sub `Spec`'s `{…}.cols.msb` / `{…}.a.val` projections reduce).
  have hbm_bool' : input_cols_b_msb_msb = 0 ∨ input_cols_b_msb_msb = 1 := hbm_bool
  have hcm_bool' : input_cols_c_msb_msb = 0 ∨ input_cols_c_msb_msb = 1 := hcm_bool
  have hbm_eq' : input_is_signed = 1 →
      input_cols_b_msb_msb = if input_b[3].val ≥ 32768 then 1 else 0 := hbm_eq
  have hcm_eq' : input_is_signed = 1 →
      input_cols_c_msb_msb = if input_cc[3].val ≥ 32768 then 1 else 0 := hcm_eq
  -- the `LtOperationUnsigned` sub-assertion `Assumptions` (the sign-adjusted words are 16-bit).
  have hbtop := adj_top hb3 his_bin hE7 hbm_eq'
  have hctop := adj_top hc3 his_bin hE9 hcm_eq'
  have hAlt : LtOperationUnsigned.circuit.Assumptions
      ⟨#v[input_b[0], input_b[1], input_b[2],
         input_b[3] + input_is_signed * 32768 - 65536 * input_cols_b_msb_msb],
       #v[input_cc[0], input_cc[1], input_cc[2],
         input_cc[3] + input_is_signed * 32768 - 65536 * input_cols_c_msb_msb],
       ⟨⟨input_cols_result_u16_compare_operation_bit⟩, input_cols_result_u16_flags,
         input_cols_result_not_eq_inv, input_cols_result_comparison_limbs⟩, input_is_real⟩ :=
    ⟨fun _ => ⟨isU64_top hb_u64 hbtop, isU64_top hcc_u64 hctop⟩, hir_bin⟩
  -- All three children expose their empty requirement lists canonically; their assumptions remain
  -- useful local inputs to the semantic lemmas but do not leak into the parent soundness contract.
  exact ⟨his_bin, hir_bin, hbm_bool', hcm_bool', hE5, hE7, hE9, hbm_eq', hcm_eq', h_lt hAlt⟩

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  let row : Inputs (ZMod p) :=
    ⟨input_b, input_cc,
      ⟨⟨⟨input_cols_result_u16_compare_operation_bit⟩, input_cols_result_u16_flags,
          input_cols_result_not_eq_inv, input_cols_result_comparison_limbs⟩,
        ⟨input_cols_b_msb_msb⟩, ⟨input_cols_c_msb_msb⟩⟩,
      input_is_signed, input_is_real⟩
  have h_evidence := (spec_iff_evidence (input := row) h_assumptions).1 h_spec
  obtain ⟨hb_u64, hcc_u64, hir_bin, his_bin⟩ := h_assumptions
  obtain ⟨_, _, hbm_bool, hcm_bool, hg5, hg7, hg9, hbm_eq, hcm_eq, h_uns_spec⟩ := h_evidence
  obtain ⟨hib, hicc, ⟨⟨_, hflags, _, hcl⟩, _, _⟩, _, _⟩ := h_input
  have eb : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_b[i] = input_b[i] := by
    intro i hi; rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cc[i] = input_cc[i] := by
    intro i hi; rw [← hicc]; simp only [Vector.getElem_map]
  have ef : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_cols_result_u16_flags[i]
      = input_cols_result_u16_flags[i] := by
    intro i hi; rw [← hflags]; simp only [Vector.getElem_map]
  have ecl : ∀ i (hi : i < 2),
      Expression.eval env.toEnvironment input_var_cols_result_comparison_limbs[i]
        = input_cols_result_comparison_limbs[i] := by
    intro i hi; rw [← hcl]; simp only [Vector.getElem_map]
  obtain ⟨-, -, -, hb3⟩ := Word.lt_cases_of_isU64 hb_u64
  obtain ⟨-, -, -, hc3⟩ := Word.lt_cases_of_isU64 hcc_u64
  have hbtop := adj_top hb3 his_bin hg7 hbm_eq
  have hctop := adj_top hc3 his_bin hg9 hcm_eq
  simp only [eb, ec, ef, ecl, vec4_eta, vec2_eta]
  refine ⟨⟨⟨fun _ => hb3, his_bin⟩, hbm_bool, hbm_eq⟩,
    ⟨⟨fun _ => hc3, his_bin⟩, hcm_bool, hcm_eq⟩,
    ⟨⟨fun _ => ⟨isU64_top hb_u64 hbtop, isU64_top hcc_u64 hctop⟩, hir_bin⟩, h_uns_spec⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rcases his_bin with h | h <;> rw [h] <;> simp
  · rcases hir_bin with h | h <;> rw [h] <;> simp
  · exact hg5
  · exact hg7
  · exact hg9

/-- SP1's `LtOperationSigned::eval` as a Clean-native `FormalAssertion`: composes two
`U16MSBOperation` and one `LtOperationUnsigned` as sub-assertions, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

/-- Expose the bundled semantic contract to `circuit_norm`. -/
@[circuit_norm] lemma circuit_Spec_eq : (circuit (p := p)).Spec = Spec := rfl
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl
@[circuit_norm] lemma channelsWithRequirements_eq :
    circuit.channelsWithRequirements = ([] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.LtOperationSigned
