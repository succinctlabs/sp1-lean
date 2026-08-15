import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Bitwise
import SP1Clean.Proofs.Operations.BitwiseOperation.Formal
import SP1Clean.Native.Operations.BitwiseOperation.Populate
import SP1Clean.Native.Operations.U16toU8OperationSafe
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
`result_semantic`, which the `BitwiseChip` soundness consumes.

Measured elaboration floors (ladder against a 1-heartbeat control, the four sites laddered at
different rungs to separate ownership — at the control rung all four report at the shared
`variable` line): `result_semantic` (15k, 20k], `spec_populate` (10k, 15k], `soundness` (5k, 10k],
`completeness` <=5k. All four formerly carried a 4000000-heartbeat ceiling — 200-800x over — and
now run at the plain default with >=10x headroom. -/

namespace SP1Clean.BitwiseU16Operation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Proof-oriented local columns for the composed u16 bitwise gadget: the two low-byte decomposition
blocks (the shared `Extracted.U16toU8Operation` struct, kept because the decomposition is the shared
generated substrate) plus the native `BitwiseOperation.Columns` result block. The assembled chip
faithfulness map is the only place that relates this shape to SP1 Rust's helper-operation columns. -/
structure Columns (F : Type) where
  b_low_bytes : Extracted.U16toU8Operation F
  c_low_bytes : Extracted.U16toU8Operation F
  bitwise_operation : BitwiseOperation.Columns F
deriving ProvableStruct

/-- The two operand words, the (chip-owned) decomposition + result column struct, the opcode selector
(AND=0, OR=1, XOR=2), and the `is_real` gate — SP1's `eval` params verbatim. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  cols : Columns F
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
  rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one]; ring

/-- A limb's value splits as its low byte plus 256× its high byte, given both are bytes. -/
lemma limb_split {w low : ZMod p} (hlo : low.val < 256)
    (hhi : ((w - low) * (256 : ZMod p)⁻¹).val < 256) :
    w.val = low.val + ((w - low) * (256 : ZMod p)⁻¹).val * 256 := by
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
def populate (b c : Word (ZMod p)) (opcode : ZMod p) : Columns (ZMod p) :=
  let lb : Extracted.U16toU8Operation (ZMod p) :=
    ⟨#v[((b[0].val % 256 : ℕ) : ZMod p), ((b[1].val % 256 : ℕ) : ZMod p),
        ((b[2].val % 256 : ℕ) : ZMod p), ((b[3].val % 256 : ℕ) : ZMod p)]⟩
  let lc : Extracted.U16toU8Operation (ZMod p) :=
    ⟨#v[((c[0].val % 256 : ℕ) : ZMod p), ((c[1].val % 256 : ℕ) : ZMod p),
        ((c[2].val % 256 : ℕ) : ZMod p), ((c[3].val % 256 : ℕ) : ZMod p)]⟩
  ⟨lb, lc, BitwiseOperation.populate (decompBytes b lb) (decompBytes c lc) opcode⟩

/-! ### Witness IR

The exportable twin of `populate` (the `AddOperation/Populate.lean` pattern, struct-shaped): the
same sixteen columns as a `Columns` struct of `FExpr`s, the composing chip's `witness` payload. The
result-byte operands are computed **in the u64 sort** — even bytes `b[i].val % 256`, odd bytes
`b[i].val / 256` — which agrees with `populate`'s field-side `(w − low)·256⁻¹` high bytes on
16-bit limbs (`decomp_high_eq`); `byteOpF` branches on the *field* opcode exactly as `byteOp`
branches on its `val` (equivalent by `val` injectivity, no opcode bound needed). Deliberately
**not** `@[circuit_norm]` (the opacity doctrine); only `populateFE_eval`/`populateFE_congr` cross
the boundary. The three `toElements_cell_*` navigators are the per-cell `toElements` projections
over an *opaque* struct (the `toElements_result_byte` technique from the chip's `Formal.lean`), so
neither proof ever runs `whnf` through the `combinedSize'` tower on a compound literal. -/

/-- The `FExpr` twin of `Math.byteOp`, branching on the field opcode (AND = 0, OR = 1, XOR = 2). -/
def byteOpF (opcode : Expression (ZMod p)) (a b : Witgen.U64Expr (ZMod p)) :
    Witgen.FExpr (ZMod p) :=
  .ite (opcode =? (0 : ZMod p)) (a &&& b).toField
    (.ite (opcode =? (1 : ZMod p)) (a ||| b).toField (a ^^^ b).toField)

/-- The witness-IR twin of `populate`, over the chip's input expressions. -/
def populateFE (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) :
    Columns (Witgen.FExpr (ZMod p)) :=
  ⟨⟨#v[(b[0].val % 256).toField, (b[1].val % 256).toField,
       (b[2].val % 256).toField, (b[3].val % 256).toField]⟩,
   ⟨#v[(c[0].val % 256).toField, (c[1].val % 256).toField,
       (c[2].val % 256).toField, (c[3].val % 256).toField]⟩,
   ⟨#v[byteOpF opcode (b[0].val % 256) (c[0].val % 256),
       byteOpF opcode (b[0].val / 256) (c[0].val / 256),
       byteOpF opcode (b[1].val % 256) (c[1].val % 256),
       byteOpF opcode (b[1].val / 256) (c[1].val / 256),
       byteOpF opcode (b[2].val % 256) (c[2].val % 256),
       byteOpF opcode (b[2].val / 256) (c[2].val / 256),
       byteOpF opcode (b[3].val % 256) (c[3].val % 256),
       byteOpF opcode (b[3].val / 256) (c[3].val / 256)]⟩⟩

/-- `populate`'s field-side high byte is the ℕ high byte: `(x − (v % 256))·256⁻¹ = v / 256` when
`x` casts `v` (the subtraction is exact, and `256` is invertible under `2^17 < p`). -/
private lemma decomp_high_eq {x : ZMod p} {v : ℕ} (hx : x = (v : ZMod p)) :
    (x - ((v % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹ = ((v / 256 : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have h256 : (256 : ZMod p) ≠ 0 := by
    intro h
    have hval : ((256 : ℕ) : ZMod p).val = 256 := ZMod.val_natCast_of_lt (by omega)
    rw [Nat.cast_ofNat, h, ZMod.val_zero] at hval
    omega
  subst hx
  rw [show (v : ZMod p) - ((v % 256 : ℕ) : ZMod p) = ((256 * (v / 256) : ℕ) : ZMod p) by
        rw [← Nat.cast_sub (Nat.mod_le v 256)]; congr 1; omega,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm ((256 : ZMod p)) _, mul_assoc,
      mul_inv_cancel₀ h256, mul_one]

set_option linter.unusedSectionVars false in
/-- Cell `k` (`k < 4`) of a flattened `Columns` struct is the `k`-th `b` low byte. Stated over an
opaque `s`, so instantiating at a compound literal only pattern-matches. -/
private lemma toElements_cell_bLow {F : Type} (s : Columns F) (k : ℕ) (hk : k < 4) :
    (toElements s)[k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.b_low_bytes.low_bytes[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `4 + k` (`k < 4`) of a flattened `Columns` struct is the `k`-th `c` low byte. -/
private lemma toElements_cell_cLow {F : Type} (s : Columns F) (k : ℕ) (hk : k < 4) :
    (toElements s)[4 + k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.c_low_bytes.low_bytes[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_left ?_).trans
         ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_))) <;> decide)

set_option linter.unusedSectionVars false in
/-- Cell `8 + k` (`k < 8`) of a flattened `Columns` struct is the `k`-th result byte (the generic-`F`
form of the chip-side `toElements_result_byte`). -/
private lemma toElements_cell_result {F : Type} (s : Columns F) (k : ℕ) (hk : k < 8) :
    (toElements s)[8 + k]'(by have h16 : size Columns = 16 := rfl; omega)
      = s.bitwise_operation.result[k] := by
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_right ?_ ?_).trans
       ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_left ?_).trans
           ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide)

/-! The per-shape eval/congr helpers, each proved once over *abstract* operand values with a
minimal context (the fold rule: `u64Wrap`'s `omega` takes the whole local context as facts, so
sixteen fat-context simp cases blow the declaration budget where six small-context helpers plus
term-mode assembly stay cheap). -/

omit [Fact (2 ^ 17 < p)] in
private lemma lowByteFE_eval (env : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p)) (v : ZMod p)
    (he : Expression.eval env.toEnvironment e = v) (hv : v.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField) = ((v.val % 256 : ℕ) : ZMod p) := by
  simp only [circuit_norm, he]

private lemma byteOpFE_eval_lo (env : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p)) (v w : ZMod p)
    (he : Expression.eval env.toEnvironment e = v)
    (hf : Expression.eval env.toEnvironment f = w)
    (hv : v.val < 2 ^ 16) (hw : w.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val % 256) (f.val % 256))
      = ((byteOp (Expression.eval env.toEnvironment opcode).val
          (((v.val % 256 : ℕ) : ZMod p)).val (((w.val % 256 : ℕ) : ZMod p)).val : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hval0 : ∀ x : ZMod p, x.val = 0 ↔ x = 0 := fun x => by
    rw [show (0 : ℕ) = ZMod.val (0 : ZMod p) from ZMod.val_zero.symm, FiniteField.val_inj_F]
  have hval1 : ∀ x : ZMod p, x.val = 1 ↔ x = 1 := fun x => by
    rw [show (1 : ℕ) = ZMod.val (1 : ZMod p) by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)],
      FiniteField.val_inj_F]
  simp only [byteOpF, byteOp, circuit_norm, he, hf,
    ZMod.val_natCast_of_lt (show v.val % 256 < p by omega),
    ZMod.val_natCast_of_lt (show w.val % 256 < p by omega),
    hval0, hval1, apply_ite (Nat.cast (R := ZMod p))]

private lemma byteOpFE_eval_hi (env : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p)) (v w : ZMod p)
    (he : Expression.eval env.toEnvironment e = v)
    (hf : Expression.eval env.toEnvironment f = w)
    (hv : v.val < 2 ^ 16) (hw : w.val < 2 ^ 16) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val / 256) (f.val / 256))
      = ((byteOp (Expression.eval env.toEnvironment opcode).val
          ((v - ((v.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val
          ((w - ((w.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val : ℕ) : ZMod p) := by
  have hp : 2 ^ 17 < p := Fact.out
  have hval0 : ∀ x : ZMod p, x.val = 0 ↔ x = 0 := fun x => by
    rw [show (0 : ℕ) = ZMod.val (0 : ZMod p) from ZMod.val_zero.symm, FiniteField.val_inj_F]
  have hval1 : ∀ x : ZMod p, x.val = 1 ↔ x = 1 := fun x => by
    rw [show (1 : ℕ) = ZMod.val (1 : ZMod p) by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)],
      FiniteField.val_inj_F]
  have hxv : v = ((v.val : ℕ) : ZMod p) := by rw [ZMod.natCast_val, ZMod.cast_id]
  have hxw : w = ((w.val : ℕ) : ZMod p) := by rw [ZMod.natCast_val, ZMod.cast_id]
  rw [decomp_high_eq hxv, decomp_high_eq hxw]
  simp only [byteOpF, byteOp, circuit_norm, he, hf,
    ZMod.val_natCast_of_lt (show v.val / 256 < p by omega),
    ZMod.val_natCast_of_lt (show w.val / 256 < p by omega),
    hval0, hval1, apply_ite (Nat.cast (R := ZMod p))]

omit [Fact (2 ^ 17 < p)] in
private lemma lowByteFE_congr (env env' : ProverEnvironment (ZMod p))
    (e : Expression (ZMod p))
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e) :
    Witgen.FExpr.eval { env := env } ((e.val % 256).toField)
      = Witgen.FExpr.eval { env := env' } ((e.val % 256).toField) := by
  simp only [circuit_norm, -Witgen.u64Wrap, he]

omit [Fact (2 ^ 17 < p)] in
private lemma byteOpFE_congr_lo (env env' : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p))
    (hop : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode)
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e)
    (hf : Expression.eval env.toEnvironment f = Expression.eval env'.toEnvironment f) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val % 256) (f.val % 256))
      = Witgen.FExpr.eval { env := env' } (byteOpF opcode (e.val % 256) (f.val % 256)) := by
  simp only [byteOpF, circuit_norm, -Witgen.u64Wrap, hop, he, hf]

omit [Fact (2 ^ 17 < p)] in
private lemma byteOpFE_congr_hi (env env' : ProverEnvironment (ZMod p))
    (opcode e f : Expression (ZMod p))
    (hop : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode)
    (he : Expression.eval env.toEnvironment e = Expression.eval env'.toEnvironment e)
    (hf : Expression.eval env.toEnvironment f = Expression.eval env'.toEnvironment f) :
    Witgen.FExpr.eval { env := env } (byteOpF opcode (e.val / 256) (f.val / 256))
      = Witgen.FExpr.eval { env := env' } (byteOpF opcode (e.val / 256) (f.val / 256)) := by
  simp only [byteOpF, circuit_norm, -Witgen.u64Wrap, hop, he, hf]

/-- Evaluating the witness IR is exactly `populate` on the evaluated operands (stated with the
evaluated words abstracted, in the `#v[…]`-of-`Expression.eval` form the chip completeness context
carries). The `isU64` bounds keep the u64-sorted `val`s from wrapping; the opcode needs no bound —
`byteOpF`'s field branches and `byteOp`'s `val` branches agree by `val` injectivity. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) (vb vc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hb : vb.isU64) (hc : vc.isU64) :
    Witgen.eval { env := env } (populateFE b c opcode)
      = populate vb vc (Expression.eval env.toEnvironment opcode) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hc
  have hB0 : Expression.eval env.toEnvironment b[0] = vb[0] := by rw [← hvb]; simp
  have hB1 : Expression.eval env.toEnvironment b[1] = vb[1] := by rw [← hvb]; simp
  have hB2 : Expression.eval env.toEnvironment b[2] = vb[2] := by rw [← hvb]; simp
  have hB3 : Expression.eval env.toEnvironment b[3] = vb[3] := by rw [← hvb]; simp
  have hC0 : Expression.eval env.toEnvironment c[0] = vc[0] := by rw [← hvc]; simp
  have hC1 : Expression.eval env.toEnvironment c[1] = vc[1] := by rw [← hvc]; simp
  have hC2 : Expression.eval env.toEnvironment c[2] = vc[2] := by rw [← hvc]; simp
  have hC3 : Expression.eval env.toEnvironment c[3] = vc[3] := by rw [← hvc]; simp
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi16 : i < 16 := by
    have hsz : size Columns = 16 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bLow _ 0 (by omega))).trans
      (lowByteFE_eval env b[0] vb[0] hB0 hb0)).trans (toElements_cell_bLow _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 1 (by omega))).trans
      (lowByteFE_eval env b[1] vb[1] hB1 hb1)).trans (toElements_cell_bLow _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 2 (by omega))).trans
      (lowByteFE_eval env b[2] vb[2] hB2 hb2)).trans (toElements_cell_bLow _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 3 (by omega))).trans
      (lowByteFE_eval env b[3] vb[3] hB3 hb3)).trans (toElements_cell_bLow _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 0 (by omega))).trans
      (lowByteFE_eval env c[0] vc[0] hC0 hc0)).trans (toElements_cell_cLow _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 1 (by omega))).trans
      (lowByteFE_eval env c[1] vc[1] hC1 hc1)).trans (toElements_cell_cLow _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 2 (by omega))).trans
      (lowByteFE_eval env c[2] vc[2] hC2 hc2)).trans (toElements_cell_cLow _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 3 (by omega))).trans
      (lowByteFE_eval env c[3] vc[3] hC3 hc3)).trans (toElements_cell_cLow _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 0 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[0] c[0] vb[0] vc[0] hB0 hC0 hb0 hc0)).trans
      (toElements_cell_result _ 0 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 1 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[0] c[0] vb[0] vc[0] hB0 hC0 hb0 hc0)).trans
      (toElements_cell_result _ 1 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 2 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[1] c[1] vb[1] vc[1] hB1 hC1 hb1 hc1)).trans
      (toElements_cell_result _ 2 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 3 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[1] c[1] vb[1] vc[1] hB1 hC1 hb1 hc1)).trans
      (toElements_cell_result _ 3 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 4 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[2] c[2] vb[2] vc[2] hB2 hC2 hb2 hc2)).trans
      (toElements_cell_result _ 4 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 5 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[2] c[2] vb[2] vc[2] hB2 hC2 hb2 hc2)).trans
      (toElements_cell_result _ 5 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 6 (by omega))).trans
      (byteOpFE_eval_lo env opcode b[3] c[3] vb[3] vc[3] hB3 hC3 hb3 hc3)).trans
      (toElements_cell_result _ 6 (by omega)).symm
  · exact ((congrArg _ (toElements_cell_result _ 7 (by omega))).trans
      (byteOpFE_eval_hi env opcode b[3] c[3] vb[3] vc[3] hB3 hC3 hb3 hc3)).trans
      (toElements_cell_result _ 7 (by omega)).symm

/-- Elementwise corollary of `populateFE_eval`, in the exact shape the chip completeness seam's
per-cell witness obligations arrive in (`FExpr.eval` of one `toElements` cell of the folded
`populateFE`). -/
theorem populateFE_eval_cell (env : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p)) (vb vc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvc : #v[Expression.eval env.toEnvironment c[0], Expression.eval env.toEnvironment c[1],
              Expression.eval env.toEnvironment c[2], Expression.eval env.toEnvironment c[3]] = vc)
    (hb : vb.isU64) (hc : vc.isU64) (j : ℕ) (hj : j < 16) :
    Witgen.FExpr.eval { env := env }
        ((toElements (populateFE b c opcode))[j]'(by
          have h16 : size Columns = 16 := rfl
          omega))
      = (toElements (populate vb vc (Expression.eval env.toEnvironment opcode)))[j]'(by
          have h16 : size Columns = 16 := rfl
          omega) := by
  have h := congrArg
    (fun s : Columns (ZMod p) => (toElements s)[j]'(by
      have h16 : size Columns = 16 := rfl
      omega))
    (populateFE_eval env b c opcode vb vc hvb hvc hb hc)
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements] at h
  simpa [Vector.getElem_map] using h

omit [Fact (2 ^ 17 < p)] in
/-- `ofFExprs`-of-`toElements` evaluation is the flattened struct evaluation (the raw payload
form the `ComputableWitnesses` obligations quantify over). -/
private lemma ofFExprs_eval_eq (env : ProverEnvironment (ZMod p))
    (xs : Columns (Witgen.FExpr (ZMod p))) :
    (Witgen.WitgenIR.ofFExprs (toElements xs)).eval env
      = toElements (Witgen.eval { env := env } xs) := by
  rw [show (Witgen.eval { env := env } xs : Columns (ZMod p))
        = fromElements ((toElements xs).map (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements]
  apply Vector.ext
  intro i hi
  simp [circuit_norm, Vector.getElem_map]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the witness IR (the `ComputableWitnesses` counterpart of
`populateFE_eval` — a congruence, so it needs no bounds). -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment c[i] = Expression.eval env'.toEnvironment c[i])
    (hOp : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode) :
    Witgen.eval { env := env } (populateFE b c opcode)
      = Witgen.eval { env := env' } (populateFE b c opcode) := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi16 : i < 16 := by
    have hsz : size Columns = 16 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFE b c opcode) : Columns (ZMod p))
        = fromElements ((toElements (populateFE b c opcode)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bLow _ 0 (by omega))).trans
      (lowByteFE_congr env env' b[0] hB0)).trans
      (congrArg _ (toElements_cell_bLow _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 1 (by omega))).trans
      (lowByteFE_congr env env' b[1] hB1)).trans
      (congrArg _ (toElements_cell_bLow _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 2 (by omega))).trans
      (lowByteFE_congr env env' b[2] hB2)).trans
      (congrArg _ (toElements_cell_bLow _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bLow _ 3 (by omega))).trans
      (lowByteFE_congr env env' b[3] hB3)).trans
      (congrArg _ (toElements_cell_bLow _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 0 (by omega))).trans
      (lowByteFE_congr env env' c[0] hC0)).trans
      (congrArg _ (toElements_cell_cLow _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 1 (by omega))).trans
      (lowByteFE_congr env env' c[1] hC1)).trans
      (congrArg _ (toElements_cell_cLow _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 2 (by omega))).trans
      (lowByteFE_congr env env' c[2] hC2)).trans
      (congrArg _ (toElements_cell_cLow _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_cLow _ 3 (by omega))).trans
      (lowByteFE_congr env env' c[3] hC3)).trans
      (congrArg _ (toElements_cell_cLow _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 0 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[0] c[0] hOp hB0 hC0)).trans
      (congrArg _ (toElements_cell_result _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 1 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[0] c[0] hOp hB0 hC0)).trans
      (congrArg _ (toElements_cell_result _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 2 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[1] c[1] hOp hB1 hC1)).trans
      (congrArg _ (toElements_cell_result _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 3 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[1] c[1] hOp hB1 hC1)).trans
      (congrArg _ (toElements_cell_result _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 4 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[2] c[2] hOp hB2 hC2)).trans
      (congrArg _ (toElements_cell_result _ 4 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 5 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[2] c[2] hOp hB2 hC2)).trans
      (congrArg _ (toElements_cell_result _ 5 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 6 (by omega))).trans
      (byteOpFE_congr_lo env env' opcode b[3] c[3] hOp hB3 hC3)).trans
      (congrArg _ (toElements_cell_result _ 6 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_result _ 7 (by omega))).trans
      (byteOpFE_congr_hi env env' opcode b[3] c[3] hOp hB3 hC3)).trans
      (congrArg _ (toElements_cell_result _ 7 (by omega))).symm

omit [Fact (2 ^ 17 < p)] in
/-- `populateFE_congr` in the raw `ofFExprs` payload form the `ComputableWitnesses` obligations
quantify over. -/
theorem populateFE_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b c : Word (Expression (ZMod p))) (opcode : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment c[i] = Expression.eval env'.toEnvironment c[i])
    (hOp : Expression.eval env.toEnvironment opcode = Expression.eval env'.toEnvironment opcode) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFE b c opcode))).eval env
      = (Witgen.WitgenIR.ofFExprs (toElements (populateFE b c opcode))).eval env' :=
  (ofFExprs_eval_eq env _).trans
    ((congrArg toElements (populateFE_congr env env' b c opcode hB hC hOp)).trans
      (ofFExprs_eval_eq env' _).symm)

/-- The witnessed columns `populate b c opcode` satisfy the gadget `Spec` for any `is_real`, given the
operands are 64-bit and the opcode is AND/OR/XOR: the populated low bytes (`w[i] % 256`) and the derived
high bytes are genuine bytes, so the composed `BitwiseOperation.spec_populate` applies. The composing
`BitwiseChip` uses this to discharge its `assertion BitwiseU16Operation.circuit` prover obligation. -/
theorem spec_populate {b c : Word (ZMod p)} (hb : Word.isU64 b) (hc : Word.isU64 c)
    {opcode : ZMod p} (hop : opcode.val < 3) (is_real : ZMod p) :
    Spec (⟨b, c, populate b c opcode, opcode, is_real⟩ : Inputs (ZMod p)) := by
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
  channelsWithGuarantees := [byteChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

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
  change BitwiseOperation.Spec _ at h_spec
  refine ⟨?_, Or.inr ⟨hop, hbin⟩⟩
  simpa only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] using h_spec

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
  · change BitwiseOperation.Spec _
    simpa only [decompBytes, eb, ec, elb, elc, ← sub_eq_add_neg] using h_spec

/-- SP1's `BitwiseU16Operation::eval` as a Clean-native `FormalAssertion`: the `is_real` binary gate
plus the composed `BitwiseOperation` on the two `U16toU8` byte decompositions, witnessing nothing. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [] }

set_option linter.unusedSectionVars false in
/-- Since Lean 4.32, class projections through `ProvableType`-derived instances no longer whnf-reduce
at `.reducible` transparency (Clean `088a9287`), so `circuit_norm` can no longer cross
`circuit.Spec` ↔ `Spec` on its own. Supply the bridge as a rewrite. -/
@[circuit_norm] lemma circuit_Spec_eq : (circuit (p := p)).Spec = Spec := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.BitwiseU16Operation

