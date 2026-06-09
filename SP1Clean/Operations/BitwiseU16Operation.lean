import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Bitwise
import SP1Clean.Operations.BitwiseOperation.Formal
import SP1Clean.Operations.BitwiseOperation.Populate
import SP1Clean.Operations.U16toU8OperationSafe
import SP1Clean.Extracted.BitwiseU16Operation
import SP1Clean.Extracted.U16toU8OperationUnsafe
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic

/-! # `BitwiseU16Operation` as a Clean-native composed `FormalAssertion`

SP1's `BitwiseU16Operation::eval` (`operations/bitwise_u16.rs`): split the two operand words `b`/`c`
into eight bytes each via `U16toU8OperationUnsafe` (pure projection — `byte[2i] = low[i]`,
`byte[2i+1] = (w[i] − low[i])·256⁻¹`), then call `BitwiseOperation::eval` (eight byte-bus AND/OR/XOR
pulls). Here that is a `FormalAssertion` that **composes `BitwiseOperation.circuit`** on the two byte
decompositions plus the `is_real` binary gate — witnessing nothing (the `b_low_bytes`/`c_low_bytes`/
`bitwise_operation.result` columns are chip-owned inputs). The structural `Spec` *is* the composed
`BitwiseOperation.Spec`; the whole-word readout (`toBitVec64 (resultWord …) = b op c`) is derived by
`result_semantic`, which the `BitwiseChip` soundness consumes. -/

namespace SP1Clean.BitwiseU16Operation

open Circuit
open SP1Clean.Channels (byteChannel binary_gate_req_vacuous)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The two operand words, the (chip-owned) decomposition + result column struct, the opcode selector
(AND=0, OR=1, XOR=2), and the `is_real` gate — SP1's `eval` params verbatim. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  cols : Extracted.BitwiseU16Operation F
  opcode : F
  is_real : F
deriving ProvableStruct

/-- The eight little-endian bytes of a word given its low-byte columns: `byte[2i] = low[i]`,
`byte[2i+1] = (w[i] − low[i])·256⁻¹` (SP1's `eval_u16_to_u8_unsafe`). Reducible so it unifies with the
byte expressions `main` feeds the composed `BitwiseOperation`. -/
@[reducible] def decompBytes (w : Word (ZMod p)) (low : Extracted.U16toU8Operation (ZMod p)) :
    Vector (ZMod p) 8 :=
  #v[low.low_bytes[0], (w[0] - low.low_bytes[0]) * (256 : ZMod p)⁻¹,
     low.low_bytes[1], (w[1] - low.low_bytes[1]) * (256 : ZMod p)⁻¹,
     low.low_bytes[2], (w[2] - low.low_bytes[2]) * (256 : ZMod p)⁻¹,
     low.low_bytes[3], (w[3] - low.low_bytes[3]) * (256 : ZMod p)⁻¹]

/-- Reassemble the eight result bytes into a four-limb word. -/
def resultWord (r : Vector (ZMod p) 8) : Word (ZMod p) :=
  #v[r[0] + r[1] * 256, r[2] + r[3] * 256, r[4] + r[5] * 256, r[6] + r[7] * 256]

/-- The two operand words are 64-bit; opcode is one of AND/OR/XOR; `is_real` is binary. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.c ∧ input.opcode.val < 3 ∧
    (input.is_real = 0 ∨ input.is_real = 1)

/-- Structural contract: the composed `BitwiseOperation.Spec` on the two byte decompositions — on a
real row the eight decomposed bytes are genuine bytes and each result byte is their per-opcode bitwise
combination. Equivalent to the constraint list (so completeness holds). The whole-word semantic readout
is `result_semantic`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.BitwiseOperation.Spec
    (⟨decompBytes input.b input.cols.b_low_bytes, decompBytes input.c input.cols.c_low_bytes,
      input.cols.bitwise_operation, input.opcode, input.is_real⟩ :
      SP1Clean.BitwiseOperation.Inputs (ZMod p))

/-- The reassembly identity `low + (w − low)·256⁻¹·256 = w`. -/
lemma reassemble (w low : ZMod p) :
    w = low + (w - low) * (256 : ZMod p)⁻¹ * 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  rw [mul_assoc, h256, mul_one]; ring

/-- A limb's value splits as its low byte plus 256× its high byte, given both are bytes. -/
lemma limb_split {w low : ZMod p} (hlo : low.val < 256)
    (hhi : ((w - low) * (256 : ZMod p)⁻¹).val < 256) :
    w.val = low.val + ((w - low) * (256 : ZMod p)⁻¹).val * 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  conv_lhs => rw [reassemble w low]
  exact val_lo_add_hi hlo hhi

/-- A limb of `w` splits as its two decomposed bytes (low + 256·high), given both are bytes. Keeps the
split in `decompBytes`-indexed form so it unifies syntactically with `toBitVec64_asm8`. -/
lemma decomp_limb_split {w : Word (ZMod p)} {low : Extracted.U16toU8Operation (ZMod p)} (i : Fin 4)
    (hlo : (decompBytes w low)[2 * (i : ℕ)].val < 256)
    (hhi : (decompBytes w low)[2 * (i : ℕ) + 1].val < 256) :
    w[(i : ℕ)].val
      = (decompBytes w low)[2 * (i : ℕ)].val + (decompBytes w low)[2 * (i : ℕ) + 1].val * 256 := by
  fin_cases i <;>
    · simp only [decompBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ] at hlo hhi ⊢
      exact limb_split hlo hhi

set_option maxHeartbeats 4000000 in
/-- **Whole-word readout.** From the structural `Spec` on a real row, the reassembled result word is
the AND/OR/XOR (as 64-bit values) of the two operands. The `BitwiseChip` soundness consumes this. -/
theorem result_semantic (input : Inputs (ZMod p))
    (hir : input.is_real = 1) (hs : Spec input) :
    (input.opcode = 0 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b &&& Word.toBitVec64 input.c) ∧
    (input.opcode = 1 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b ||| Word.toBitVec64 input.c) ∧
    (input.opcode = 2 →
      Word.toBitVec64 (resultWord input.cols.bitwise_operation.result)
        = Word.toBitVec64 input.b ^^^ Word.toBitVec64 input.c) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  set b := input.b with hb_def
  set c := input.c with hc_def
  set lb := input.cols.b_low_bytes with hlb_def
  set lc := input.cols.c_low_bytes with hlc_def
  set r := input.cols.bitwise_operation.result with hr_def
  obtain ⟨hbnd, harms⟩ := hs hir
  have bbB : ∀ i : Fin 8, (decompBytes b lb)[(i : ℕ)].val < 256 := fun i => (hbnd i).1
  have bbC : ∀ i : Fin 8, (decompBytes c lc)[(i : ℕ)].val < 256 := fun i => (hbnd i).2
  -- the two operand words, packaged as `BitVec.ofNat` of the base-256 assembly of their bytes
  have hsplitB : Word.toBitVec64 b = BitVec.ofNat 64 (asm8
      (decompBytes b lb)[0].val (decompBytes b lb)[1].val (decompBytes b lb)[2].val
      (decompBytes b lb)[3].val (decompBytes b lb)[4].val (decompBytes b lb)[5].val
      (decompBytes b lb)[6].val (decompBytes b lb)[7].val) :=
    toBitVec64_asm8 b _ _ _ _ _ _ _ _
      (decomp_limb_split 0 (bbB 0) (bbB 1)) (decomp_limb_split 1 (bbB 2) (bbB 3))
      (decomp_limb_split 2 (bbB 4) (bbB 5)) (decomp_limb_split 3 (bbB 6) (bbB 7))
  have hsplitC : Word.toBitVec64 c = BitVec.ofNat 64 (asm8
      (decompBytes c lc)[0].val (decompBytes c lc)[1].val (decompBytes c lc)[2].val
      (decompBytes c lc)[3].val (decompBytes c lc)[4].val (decompBytes c lc)[5].val
      (decompBytes c lc)[6].val (decompBytes c lc)[7].val) :=
    toBitVec64_asm8 c _ _ _ _ _ _ _ _
      (decomp_limb_split 0 (bbC 0) (bbC 1)) (decomp_limb_split 1 (bbC 2) (bbC 3))
      (decomp_limb_split 2 (bbC 4) (bbC 5)) (decomp_limb_split 3 (bbC 6) (bbC 7))
  -- per-opcode resolver: from the arm's byte equalities, run the keystone reassembly
  have core : ∀ (op : ℕ), op < 3 →
      (∀ i : Fin 8, r[(i : ℕ)].val
        = byteOp op (decompBytes b lb)[(i : ℕ)].val (decompBytes c lc)[(i : ℕ)].val) →
      Word.toBitVec64 (resultWord r) = bitOp64 op (Word.toBitVec64 b) (Word.toBitVec64 c) := by
    intro op hop hbyteop
    have hr_lt : ∀ i : Fin 8, r[(i : ℕ)].val < 256 := fun i => by
      rw [hbyteop i]; exact byteOp_lt256 _ _ _ (bbB i) (bbC i)
    have hres : Word.toBitVec64 (resultWord r) = BitVec.ofNat 64 (asm8
        r[0].val r[1].val r[2].val r[3].val r[4].val r[5].val r[6].val r[7].val) := by
      refine toBitVec64_asm8 (resultWord r) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;>
        simp only [resultWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
      · exact val_lo_add_hi (hr_lt 0) (hr_lt 1)
      · exact val_lo_add_hi (hr_lt 2) (hr_lt 3)
      · exact val_lo_add_hi (hr_lt 4) (hr_lt 5)
      · exact val_lo_add_hi (hr_lt 6) (hr_lt 7)
    rw [hres, hsplitB, hsplitC]
    exact reassemble_byteOp op hop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (bbB 0) (bbB 1) (bbB 2) (bbB 3) (bbB 4) (bbB 5) (bbB 6)
      (bbC 0) (bbC 1) (bbC 2) (bbC 3) (bbC 4) (bbC 5) (bbC 6)
      (hbyteop 0) (hbyteop 1) (hbyteop 2) (hbyteop 3) (hbyteop 4) (hbyteop 5) (hbyteop 6) (hbyteop 7)
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · have := core 0 (by omega) (fun i => by rw [byteOp_zero]; exact (harms.1 h0) i)
    rwa [bitOp64_zero] at this
  · have := core 1 (by omega) (fun i => by rw [byteOp_one]; exact (harms.2.1 h1) i)
    rwa [bitOp64_one] at this
  · have := core 2 (by omega) (fun i => by rw [byteOp_two]; exact (harms.2.2 h2) i)
    rwa [bitOp64_two] at this

/-- The decomposition + result columns for `populate`: the low bytes are `w[i] % 256`, the result bytes
are the per-byte `byteOp opcode` of the decomposed operand bytes (mirroring SP1's `populate`). -/
def populate (b c : Word (ZMod p)) (opcode : ZMod p) : Extracted.BitwiseU16Operation (ZMod p) :=
  let lb : Extracted.U16toU8Operation (ZMod p) :=
    ⟨#v[((b[0].val % 256 : ℕ) : ZMod p), ((b[1].val % 256 : ℕ) : ZMod p),
        ((b[2].val % 256 : ℕ) : ZMod p), ((b[3].val % 256 : ℕ) : ZMod p)]⟩
  let lc : Extracted.U16toU8Operation (ZMod p) :=
    ⟨#v[((c[0].val % 256 : ℕ) : ZMod p), ((c[1].val % 256 : ℕ) : ZMod p),
        ((c[2].val % 256 : ℕ) : ZMod p), ((c[3].val % 256 : ℕ) : ZMod p)]⟩
  ⟨lb, lc, BitwiseOperation.populate (decompBytes b lb) (decompBytes c lc) opcode⟩

set_option maxHeartbeats 4000000 in
/-- The witnessed columns `populate b c opcode` satisfy the gadget `Spec` for any `is_real`, given the
operands are 64-bit and the opcode is AND/OR/XOR: the populated low bytes (`w[i] % 256`) and the derived
high bytes are genuine bytes, so the composed `BitwiseOperation.spec_populate` applies. The composing
`BitwiseChip` uses this to discharge its `assertion BitwiseU16Operation.circuit` prover obligation. -/
theorem spec_populate {b c : Word (ZMod p)} (hb : Word.isU64 b) (hc : Word.isU64 c)
    {opcode : ZMod p} (hop : opcode.val < 3) (is_real : ZMod p) :
    Spec (⟨b, c, populate b c opcode, opcode, is_real⟩ : Inputs (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp256 : (256 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have low_lt : ∀ u : ZMod p, (((u.val % 256 : ℕ) : ZMod p)).val < 256 := fun u => by
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  have high_lt : ∀ u : ZMod p, u.val < 65536 →
      ((u - ((u.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val < 256 := fun u hu => by
    rw [← e8]; exact U16toU8OperationSafe.high_byte_lt u (by rw [e16]; exact hu)
  have hbytes : ∀ i : Fin 8,
      (decompBytes b (populate b c opcode).b_low_bytes)[(i : ℕ)].val < 256 ∧
        (decompBytes c (populate b c opcode).c_low_bytes)[(i : ℕ)].val < 256 := by
    intro i
    fin_cases i <;>
      refine ⟨?_, ?_⟩ <;>
      · simp only [populate, decompBytes, Vector.getElem_mk, List.getElem_toArray,
          List.getElem_cons_zero, List.getElem_cons_succ]
        first
          | exact low_lt _
          | (apply high_lt; assumption)
  exact BitwiseOperation.spec_populate hbytes hop is_real

/-- SP1's `BitwiseU16Operation::eval` as a `FormalAssertion`: the `is_real` binary gate plus the
composed `BitwiseOperation.circuit` on the two byte decompositions. Witnesses nothing. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let b := input.b
  let c := input.c
  let lb := input.cols.b_low_bytes.low_bytes
  let lc := input.cols.c_low_bytes.low_bytes
  input.is_real * (input.is_real - 1) === 0
  assertion BitwiseOperation.circuit
    (⟨#v[lb[0], (b[0] - lb[0]) * (256 : ZMod p)⁻¹, lb[1], (b[1] - lb[1]) * (256 : ZMod p)⁻¹,
         lb[2], (b[2] - lb[2]) * (256 : ZMod p)⁻¹, lb[3], (b[3] - lb[3]) * (256 : ZMod p)⁻¹],
      #v[lc[0], (c[0] - lc[0]) * (256 : ZMod p)⁻¹, lc[1], (c[1] - lc[1]) * (256 : ZMod p)⁻¹,
         lc[2], (c[2] - lc[2]) * (256 : ZMod p)⁻¹, lc[3], (c[3] - lc[3]) * (256 : ZMod p)⁻¹],
      input.cols.bitwise_operation, input.opcode, input.is_real⟩ :
      Var SP1Clean.BitwiseOperation.Inputs (ZMod p))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements := [byteChannel.toRawGated]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRawGated] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

set_option maxHeartbeats 4000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_hb, _hc, hop, hbin⟩ := h_assumptions
  obtain ⟨hib, hic, ⟨hilb, hilc, _hires⟩, _hiop, _hireal⟩ := h_input
  have eb : ∀ (k : ℕ) (_ : k < 4), Expression.eval env input_var_b[k] = input_b[k] :=
    fun k _ => by rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ (k : ℕ) (_ : k < 4), Expression.eval env input_var_c[k] = input_c[k] :=
    fun k _ => by rw [← hic]; simp only [Vector.getElem_map]
  have elb : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env input_var_cols_b_low_bytes_low_bytes[k]
        = input_cols_b_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilb]; simp only [Vector.getElem_map]
  have elc : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env input_var_cols_c_low_bytes_low_bytes[k]
        = input_cols_c_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilc]; simp only [Vector.getElem_map]
  obtain ⟨_h_gate, h_bw⟩ := h_holds
  have h_spec := h_bw ⟨hop, hbin⟩
  refine ⟨?_, Or.inr ⟨hop, hbin⟩⟩
  simp only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] at h_spec ⊢
  exact h_spec

set_option maxHeartbeats 4000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_hb, _hc, hop, hbin⟩ := h_assumptions
  obtain ⟨hib, hic, ⟨hilb, hilc, _hires⟩, _hiop, _hireal⟩ := h_input
  have eb : ∀ (k : ℕ) (_ : k < 4), Expression.eval env.toEnvironment input_var_b[k] = input_b[k] :=
    fun k _ => by rw [← hib]; simp only [Vector.getElem_map]
  have ec : ∀ (k : ℕ) (_ : k < 4), Expression.eval env.toEnvironment input_var_c[k] = input_c[k] :=
    fun k _ => by rw [← hic]; simp only [Vector.getElem_map]
  have elb : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env.toEnvironment input_var_cols_b_low_bytes_low_bytes[k]
        = input_cols_b_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilb]; simp only [Vector.getElem_map]
  have elc : ∀ (k : ℕ) (_ : k < 4),
      Expression.eval env.toEnvironment input_var_cols_c_low_bytes_low_bytes[k]
        = input_cols_c_low_bytes_low_bytes[k] :=
    fun k _ => by rw [← hilc]; simp only [Vector.getElem_map]
  refine ⟨?_, ⟨hop, hbin⟩, ?_⟩
  · rcases hbin with h | h <;> rw [h] <;> simp
  · simp only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] at h_spec ⊢
    exact h_spec

/-- SP1's `BitwiseU16Operation::eval` as a Clean-native `FormalAssertion`: the `is_real` binary gate
plus the composed `BitwiseOperation` on the two `U16toU8` byte decompositions, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.BitwiseU16Operation
