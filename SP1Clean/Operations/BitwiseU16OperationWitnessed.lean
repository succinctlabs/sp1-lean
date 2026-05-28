import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.BitwiseOperation

/-! # Witness-generation pilot: `BitwiseU16Operation` as a `FormalCircuit`

**Status: pilot skeleton (validated structure, 2 documented `sorry`s).** This
file is the worked example for "solving completeness via witness generation"
discussed in `docs/CLEAN_VERIFICATION_STATUS.md` §4. It is **not** imported by
the `SP1Clean` lib root, so it does not affect `lake build SP1Clean`; validate
it standalone with `lake env lean SP1Clean/Operations/BitwiseU16OperationWitnessed.lean`.

## Why this exists

The production `SP1Clean.BitwiseU16Op` (`BitwiseU16Operation.lean`) is a
`FormalAssertion` whose byte-decomposition columns (`b_low_bytes`,
`c_low_bytes`, `result`) are *free inputs*, so its `Spec` is forced to be
*structural* and its completeness is only "structural completeness" (it cannot
prove a purely semantic `result = b OP c` spec — a wrong `b_low_bytes` satisfies
the semantic spec yet violates the constraints).

This pilot models those aux cells the way the SP1 prover actually treats them:
**internally-generated committed witnesses**. With the bytes produced by
closed-form `witnessVector` compute functions, the circuit becomes a
`FormalCircuit` (it has an *output* — the result word) whose `Spec` is genuinely
*semantic* (`output = execute_RTYPE_pure_w b cc {AND,OR,XOR}`), and whose
completeness (`Assumptions → constraints`, quantified over
`env.UsesLocalWitnessesCompleteness` — i.e. "the prover uses these witness
generators") is *actually* provable. That is the boundary-A "intra-Lean witness
construction" closure.

## Templates for closing the two `sorry`s

- `Clean/Gadgets/Xor/Xor64.lean` — the from-scratch `FormalCircuit` skeleton
  (witness compute + byte lookups + `output := varFromOffset`; its `soundness` /
  `completeness` proofs are the structural template).
- `SP1Clean/Operations/IsZeroOperation.lean:38` — in-repo proof that
  `FormalCircuit` with a semantic spec + internal witness works in SP1Clean.
- `SP1Operations/.../BitwiseU16Operation.lean` `spec.{and,or,xor}` — the forward
  (constraints ⇒ `execute_RTYPE_pure_w`) content reusable for `soundness`.
- `SP1Operations/.../AddOperation.lean:131` `spec_inv` — the per-limb
  `% / ÷ 256` → ZMod (`ZMod.natCast_zmod_val`, `linear_combination`) technique
  for evaluating the high-byte decomposition `(b[j] - b_low[j]) * 256⁻¹ = b[j]/256`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.BitwiseU16OpWitnessed

open Circuit
open SP1Clean (ByteOpcodeTable)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Byte-level bitwise op (opcode convention: AND=0, OR=1, XOR=2, matching
`ByteOpcode.ofNat` and SP1's `BitwiseU16Operation.constraints`). -/
def byteOp (op a b : ℕ) : ℕ :=
  if op = 0 then a &&& b else if op = 1 then a ||| b else a ^^^ b

/-- Inputs: two 4-limb operands and the byte opcode. The byte-decomposition
witnesses and the 8-byte result are generated *internally* (not inputs). -/
structure Inputs (F : Type) where
  b : fields 4 F
  cc : fields 4 F
  opcode : F
deriving ProvableStruct

/-- Generated circuit. Witnesses `b_low`/`c_low` (the 4 low bytes of each
operand) and the 8 `result` bytes (each = `byteOp` of the corresponding
decomposed bytes), then emits the 8 `ByteOpcodeTable` lookups over the
decomposition `#v[low, (limb - low)·256⁻¹]` per limb. Returns the result. -/
def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var (fields 8) (ZMod p)) := do
  let b_low ← witnessVector 4 (fun env =>
    #v[(((env input.b[0]).val % 256 : ℕ) : ZMod p),
       (((env input.b[1]).val % 256 : ℕ) : ZMod p),
       (((env input.b[2]).val % 256 : ℕ) : ZMod p),
       (((env input.b[3]).val % 256 : ℕ) : ZMod p)])
  let c_low ← witnessVector 4 (fun env =>
    #v[(((env input.cc[0]).val % 256 : ℕ) : ZMod p),
       (((env input.cc[1]).val % 256 : ℕ) : ZMod p),
       (((env input.cc[2]).val % 256 : ℕ) : ZMod p),
       (((env input.cc[3]).val % 256 : ℕ) : ZMod p)])
  let result ← witnessVector 8 (fun env =>
    let op := (env input.opcode).val
    let b0 := (env input.b[0]).val; let b1 := (env input.b[1]).val
    let b2 := (env input.b[2]).val; let b3 := (env input.b[3]).val
    let c0 := (env input.cc[0]).val; let c1 := (env input.cc[1]).val
    let c2 := (env input.cc[2]).val; let c3 := (env input.cc[3]).val
    #v[((byteOp op (b0 % 256) (c0 % 256) : ℕ) : ZMod p),
       ((byteOp op (b0 / 256) (c0 / 256) : ℕ) : ZMod p),
       ((byteOp op (b1 % 256) (c1 % 256) : ℕ) : ZMod p),
       ((byteOp op (b1 / 256) (c1 / 256) : ℕ) : ZMod p),
       ((byteOp op (b2 % 256) (c2 % 256) : ℕ) : ZMod p),
       ((byteOp op (b2 / 256) (c2 / 256) : ℕ) : ZMod p),
       ((byteOp op (b3 % 256) (c3 % 256) : ℕ) : ZMod p),
       ((byteOp op (b3 / 256) (c3 / 256) : ℕ) : ZMod p)])
  lookup ByteOpcodeTable (#v[input.opcode, result[0], b_low[0], c_low[0]])
  lookup ByteOpcodeTable (#v[input.opcode, result[1], (input.b[0] - b_low[0]) * (256 : ZMod p)⁻¹, (input.cc[0] - c_low[0]) * (256 : ZMod p)⁻¹])
  lookup ByteOpcodeTable (#v[input.opcode, result[2], b_low[1], c_low[1]])
  lookup ByteOpcodeTable (#v[input.opcode, result[3], (input.b[1] - b_low[1]) * (256 : ZMod p)⁻¹, (input.cc[1] - c_low[1]) * (256 : ZMod p)⁻¹])
  lookup ByteOpcodeTable (#v[input.opcode, result[4], b_low[2], c_low[2]])
  lookup ByteOpcodeTable (#v[input.opcode, result[5], (input.b[2] - b_low[2]) * (256 : ZMod p)⁻¹, (input.cc[2] - c_low[2]) * (256 : ZMod p)⁻¹])
  lookup ByteOpcodeTable (#v[input.opcode, result[6], b_low[3], c_low[3]])
  lookup ByteOpcodeTable (#v[input.opcode, result[7], (input.b[3] - b_low[3]) * (256 : ZMod p)⁻¹, (input.cc[3] - c_low[3]) * (256 : ZMod p)⁻¹])
  return result

/-- Witnesses, in allocation order: `b_low` (4) at `i0`, `c_low` (4) at `i0+4`,
`result` (8) at `i0+8`. Output = the result vector. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs (fields 8) where
  main := main
  localLength _ := 16
  output _ i0 := varFromOffset (fields 8) (i0 + 8)

/-- Operand words fit in 64 bits and the opcode is one of AND/OR/XOR. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧ input.opcode.val < 3

/-- Semantic spec: the synthesized result word equals the RISC-V bitwise op of
the operands, selected by the opcode. -/
def resultWord (result : Vector (ZMod p) 8) : Word (ZMod p) :=
  #v[result[0] + result[1] * 256, result[2] + result[3] * 256,
     result[4] + result[5] * 256, result[6] + result[7] * 256]

def Spec (input : Inputs (ZMod p)) (result : Vector (ZMod p) 8) : Prop :=
  (input.opcode = 0 → Word.toBitVec64 (resultWord result) = execute_RTYPE_pure_w input.b input.cc .AND) ∧
  (input.opcode = 1 → Word.toBitVec64 (resultWord result) = execute_RTYPE_pure_w input.b input.cc .OR) ∧
  (input.opcode = 2 → Word.toBitVec64 (resultWord result) = execute_RTYPE_pure_w input.b input.cc .XOR)

/-- The byte-level op stays within a byte. -/
lemma byteOp_lt256 (op x y : ℕ) (hx : x < 256) (hy : y < 256) : byteOp op x y < 256 := by
  have hx8 : x < 2 ^ 8 := by omega
  have hy8 : y < 2 ^ 8 := by omega
  unfold byteOp
  split
  · have := Nat.and_lt_two_pow (n := 8) x hy8; omega
  · split
    · have := Nat.or_lt_two_pow (n := 8) hx8 hy8; omega
    · have := Nat.xor_lt_two_pow (n := 8) hx8 hy8; omega

/-- A single byte-table lookup row is satisfied (witness `ByteOpcode.ofNat
opcode.val`) when the opcode selects AND/OR/XOR and the operand bytes fit in a
byte. The result cell is the closed-form `byteOp`, exactly as `main` witnesses. -/
lemma byteOpcodeSpec_cell (opcode : ZMod p) (x y : ℕ)
    (hop : opcode.val < 3) (hx : x < 256) (hy : y < 256) :
    ByteOpcodeSpec (#v[opcode, ((byteOp opcode.val x y : ℕ) : ZMod p),
        ((x : ℕ) : ZMod p), ((y : ℕ) : ZMod p)] : Vector (ZMod p) 4) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 256 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hround : ((opcode.val : ℕ) : ZMod p) = opcode := ZMod.natCast_zmod_val opcode
  have hbop := byteOp_lt256 opcode.val x y hx hy
  have hxv : ((x : ℕ) : ZMod p).val = x := ZMod.val_natCast_of_lt (by omega)
  have hyv : ((y : ℕ) : ZMod p).val = y := ZMod.val_natCast_of_lt (by omega)
  have hrv : ((byteOp opcode.val x y : ℕ) : ZMod p).val = byteOp opcode.val x y :=
    ZMod.val_natCast_of_lt (by omega)
  have hlt : ∀ m : ℕ, m < 256 → ((m : ℕ) : ZMod p) < 256 := by
    intro m hm
    change ((m : ℕ) : ZMod p).val < (256 : ZMod p).val
    rw [ZMod.val_natCast_of_lt (show m < p by omega),
      show (256 : ZMod p) = ((256 : ℕ) : ZMod p) by norm_cast,
      ZMod.val_natCast_of_lt hp]
    exact hm
  refine ⟨ByteOpcode.ofNat opcode.val, ?_, ?_⟩
  · have htoNat : (ByteOpcode.ofNat opcode.val).toNat = opcode.val := by
      interval_cases h : opcode.val <;> rfl
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, htoNat, hround]
  · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero]
    interval_cases h : opcode.val <;>
      simp only [ByteOpcode.ofNat_zero, ByteOpcode.ofNat_one, ByteOpcode.ofNat_two,
        ByteOpcode.constrain_AND, ByteOpcode.constrain_OR, ByteOpcode.constrain_XOR] <;>
      refine ⟨⟨hlt _ hbop, hlt x hx, hlt y hy⟩, ?_⟩ <;>
      rw [hrv, hxv, hyv] <;> simp [byteOp]

/-- The witnessed high byte `(b - low) · 256⁻¹` evaluates to `b.val / 256`
(the `AddOperation.spec_inv` ZMod technique: `b = ↑b.val`, `Nat.mod_add_div'`,
`256 · 256⁻¹ = 1`). Stated with `m` free to avoid `.val` self-rewrites. -/
lemma high_byte_eval (b : ZMod p) (m : ℕ) (hb : b = (m : ZMod p)) :
    (b + -((m % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹ = ((m / 256 : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 256 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h256ne : (256 : ZMod p) ≠ 0 := by
    intro hc
    have hv : (256 : ZMod p).val = 0 := by rw [hc, ZMod.val_zero]
    rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) by push_cast; rfl,
      ZMod.val_natCast_of_lt hp] at hv
    omega
  subst hb
  have hcast : ((m : ℕ) : ZMod p) =
      ((m % 256 : ℕ) : ZMod p) + ((m / 256 : ℕ) : ZMod p) * 256 := by
    calc ((m : ℕ) : ZMod p) = ((m % 256 + m / 256 * 256 : ℕ) : ZMod p) := by
          rw [Nat.mod_add_div' m 256]
      _ = _ := by push_cast; ring
  rw [hcast, ← sub_eq_add_neg, add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ h256ne, mul_one]

/-- Extract the per-byte `ByteOpcode.constrain` from a satisfied lookup row,
pinning the existential witness to `ByteOpcode.ofNat opcode.val` (reverse of
`byteOpcodeSpec_cell`; mirrors `BitwiseOp.Spec_of_ByteOpcodeSpec_when_lt7`). -/
lemma constrain_of_byteOpcodeSpec (opcode r dB dC : ZMod p) (_hop : opcode.val < 3)
    (h : ByteOpcodeSpec (#v[opcode, r, dB, dC] : Vector (ZMod p) 4)) :
    (ByteOpcode.ofNat opcode.val).constrain r dB dC := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 256 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  obtain ⟨bop, hbop, hcon⟩ := h
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at hbop hcon
  have hbop_lt : bop.toNat < 7 := by cases bop <;> simp [ByteOpcode.toNat]
  have hbop_val : bop.toNat = opcode.val := by
    apply_fun ZMod.val at hbop
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : bop.toNat < p)] at hbop
    exact hbop
  have hbop_eq : bop = ByteOpcode.ofNat opcode.val := by
    rw [← hbop_val]; cases bop <;> simp [ByteOpcode.toNat]
  rw [hbop_eq] at hcon; exact hcon

-- CLOSURE STEP 1 (soundness, ≈ `spec.{and,or,xor}` content, 3 opcodes):
-- After `intro …; simp [circuit_norm, main, ByteOpcodeTable]`, `h_holds` gives
-- 8 `ByteOpcodeSpec` facts. Via `BitwiseOp.Spec_of_ByteOpcodeSpec_when_lt7`
-- (opcode.val < 3 < 7) get per-byte `(ofNat opcode.val).constrain`, i.e.
-- `result[i].val = decompB[i].val OP decompC[i].val` with all bytes < 256.
-- The decomp bytes sum to the limbs algebraically (the `(b-low)·256⁻¹` form),
-- so reconstruct `resultWord = b OP c` per opcode by the `spec.and` recipe
-- (`Word.toBitVec64`, byte `.val` arithmetic, `bv_decide`).
theorem soundness : Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw, ByteOpcodeTable] at h_holds
  obtain ⟨hb_isU64, hcc_isU64, hop⟩ := h_assumptions
  obtain ⟨hib, hic, hio⟩ := h_input
  have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp [Vector.getElem_map]
  have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp [Vector.getElem_map]
  have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp [Vector.getElem_map]
  have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp [Vector.getElem_map]
  have ec0 : Expression.eval env input_var_cc[0] = input_cc[0] := by rw [← hic]; simp [Vector.getElem_map]
  have ec1 : Expression.eval env input_var_cc[1] = input_cc[1] := by rw [← hic]; simp [Vector.getElem_map]
  have ec2 : Expression.eval env input_var_cc[2] = input_cc[2] := by rw [← hic]; simp [Vector.getElem_map]
  have ec3 : Expression.eval env input_var_cc[3] = input_cc[3] := by rw [← hic]; simp [Vector.getElem_map]
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3, hio, ← sub_eq_add_neg] at h_holds
  simp only [show (i₀ + 4 + 4 : ℕ) = i₀ + 8 from by omega] at h_holds
  obtain ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩ := h_holds
  set cols : BitwiseU16Operation (ZMod p) :=
    { b_low_bytes := ⟨#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)]⟩,
      c_low_bytes := ⟨#v[env.get (i₀ + 4), env.get (i₀ + 4 + 1), env.get (i₀ + 4 + 2),
        env.get (i₀ + 4 + 3)]⟩,
      bitwise_operation := ⟨#v[env.get (i₀ + 8), env.get (i₀ + 8 + 1), env.get (i₀ + 8 + 2),
        env.get (i₀ + 8 + 3), env.get (i₀ + 8 + 4), env.get (i₀ + 8 + 5), env.get (i₀ + 8 + 6),
        env.get (i₀ + 8 + 7)]⟩ } with hcols
  have hres : ∀ op : ZMod p,
      (BitwiseU16Operation.constraints input_b input_cc cols op 1).1 =
        resultWord (Vector.map (Expression.eval env)
          (Vector.mapRange 8 fun i => var { index := i₀ + 8 + i })) := by
    intro op
    simp [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints, hcols, resultWord,
      Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have c0 := constrain_of_byteOpcodeSpec _ _ _ _ hop H0
  have c1 := constrain_of_byteOpcodeSpec _ _ _ _ hop H1
  have c2 := constrain_of_byteOpcodeSpec _ _ _ _ hop H2
  have c3 := constrain_of_byteOpcodeSpec _ _ _ _ hop H3
  have c4 := constrain_of_byteOpcodeSpec _ _ _ _ hop H4
  have c5 := constrain_of_byteOpcodeSpec _ _ _ _ hop H5
  have c6 := constrain_of_byteOpcodeSpec _ _ _ _ hop H6
  have c7 := constrain_of_byteOpcodeSpec _ _ _ _ hop H7
  have hallHold : List.Forall SP1Constraint.toProp
      (BitwiseU16Operation.constraints input_b input_cc cols input_opcode 1).2 := by
    simp only [BitwiseU16Operation.constraints, U16toU8OperationUnsafe.constraints,
      BitwiseOperation.constraints, hcols, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, coeHead_zmod_eq_val,
      List.nil_append, List.cons_append, List.append_assoc, List.singleton_append,
      List.Forall, SP1Constraint.toProp_send_byte, SP1Constraint.toProp_assertZero,
      ne_eq, one_ne_zero, not_false_eq_true, true_implies]
    exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, by ring⟩
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · subst h0; rw [← hres 0]; exact BitwiseU16Operation.spec.and hb_isU64 hcc_isU64 hallHold
  · subst h1; rw [← hres 1]; exact BitwiseU16Operation.spec.or hb_isU64 hcc_isU64 hallHold
  · subst h2; rw [← hres 2]; exact BitwiseU16Operation.spec.xor hb_isU64 hcc_isU64 hallHold

-- CLOSURE STEP 2 (completeness — the witness-generation heart):
-- `intro i0 env input_var h_env input h_input as`. `h_env` (UsesLocalWitnesses)
-- pins each witnessed cell to its compute value: `b_low[j] = b[j].val % 256`,
-- high byte `(b[j]-b_low[j])·256⁻¹ = b[j].val / 256` (AddOperation.spec_inv
-- technique: `b[j] = (b[j].val : ZMod)`, `Nat.div_add_mod`, `256·256⁻¹ = 1`),
-- and `result[k] = (byteOp op x y : ZMod)`. Each lookup's `Lookup.Completeness`
-- = `ByteOpcodeSpec #v[opcode, result[k], decompB[k], decompC[k]]`; witness
-- `bop := ByteOpcode.ofNat opcode.val` (opcode.val < 3 round-trips) and discharge
-- `.constrain` from: bytes < 256 (omega from isU64) and
-- `result[k].val = byteOp op x y = x OP y` (a per-byte helper lemma:
-- `byteOp op x y < 256` via `Nat.{and,or,xor}_lt_two_pow`, then `interval_cases op`).
theorem completeness : Completeness (ZMod p) elaborated Assumptions := by
  circuit_proof_start
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw, ByteOpcodeTable]
  obtain ⟨hib, hic, hio⟩ := h_input
  obtain ⟨hb_isU64, hcc_isU64, hop⟩ := h_assumptions
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by
    rw [← hib]; simp [Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by
    rw [← hib]; simp [Vector.getElem_map]
  have eb2 : Expression.eval env.toEnvironment input_var_b[2] = input_b[2] := by
    rw [← hib]; simp [Vector.getElem_map]
  have eb3 : Expression.eval env.toEnvironment input_var_b[3] = input_b[3] := by
    rw [← hib]; simp [Vector.getElem_map]
  have ec0 : Expression.eval env.toEnvironment input_var_cc[0] = input_cc[0] := by
    rw [← hic]; simp [Vector.getElem_map]
  have ec1 : Expression.eval env.toEnvironment input_var_cc[1] = input_cc[1] := by
    rw [← hic]; simp [Vector.getElem_map]
  have ec2 : Expression.eval env.toEnvironment input_var_cc[2] = input_cc[2] := by
    rw [← hic]; simp [Vector.getElem_map]
  have ec3 : Expression.eval env.toEnvironment input_var_cc[3] = input_cc[3] := by
    rw [← hic]; simp [Vector.getElem_map]
  simp only [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3, hio] at h_env ⊢
  obtain ⟨hbl, hcl, hrr⟩ := h_env
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb_isU64
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc_isU64
  have g_b0 : env.get i₀ = ((input_b[0].val % 256 : ℕ) : ZMod p) := by simpa using hbl 0
  have g_b1 : env.get (i₀ + 1) = ((input_b[1].val % 256 : ℕ) : ZMod p) := by simpa using hbl 1
  have g_b2 : env.get (i₀ + 2) = ((input_b[2].val % 256 : ℕ) : ZMod p) := by simpa using hbl 2
  have g_b3 : env.get (i₀ + 3) = ((input_b[3].val % 256 : ℕ) : ZMod p) := by simpa using hbl 3
  have g_c0 : env.get (i₀ + 4) = ((input_cc[0].val % 256 : ℕ) : ZMod p) := by simpa using hcl 0
  have g_c1 : env.get (i₀ + 4 + 1) = ((input_cc[1].val % 256 : ℕ) : ZMod p) := by simpa using hcl 1
  have g_c2 : env.get (i₀ + 4 + 2) = ((input_cc[2].val % 256 : ℕ) : ZMod p) := by simpa using hcl 2
  have g_c3 : env.get (i₀ + 4 + 3) = ((input_cc[3].val % 256 : ℕ) : ZMod p) := by simpa using hcl 3
  have g_r0 : env.get (i₀ + 4 + 4) =
      ((byteOp input_opcode.val (input_b[0].val % 256) (input_cc[0].val % 256) : ℕ) : ZMod p) := by
    simpa using hrr 0
  have g_r1 : env.get (i₀ + 4 + 4 + 1) =
      ((byteOp input_opcode.val (input_b[0].val / 256) (input_cc[0].val / 256) : ℕ) : ZMod p) := by
    simpa using hrr 1
  have g_r2 : env.get (i₀ + 4 + 4 + 2) =
      ((byteOp input_opcode.val (input_b[1].val % 256) (input_cc[1].val % 256) : ℕ) : ZMod p) := by
    simpa using hrr 2
  have g_r3 : env.get (i₀ + 4 + 4 + 3) =
      ((byteOp input_opcode.val (input_b[1].val / 256) (input_cc[1].val / 256) : ℕ) : ZMod p) := by
    simpa using hrr 3
  have g_r4 : env.get (i₀ + 4 + 4 + 4) =
      ((byteOp input_opcode.val (input_b[2].val % 256) (input_cc[2].val % 256) : ℕ) : ZMod p) := by
    simpa using hrr 4
  have g_r5 : env.get (i₀ + 4 + 4 + 5) =
      ((byteOp input_opcode.val (input_b[2].val / 256) (input_cc[2].val / 256) : ℕ) : ZMod p) := by
    simpa using hrr 5
  have g_r6 : env.get (i₀ + 4 + 4 + 6) =
      ((byteOp input_opcode.val (input_b[3].val % 256) (input_cc[3].val % 256) : ℕ) : ZMod p) := by
    simpa using hrr 6
  have g_r7 : env.get (i₀ + 4 + 4 + 7) =
      ((byteOp input_opcode.val (input_b[3].val / 256) (input_cc[3].val / 256) : ℕ) : ZMod p) := by
    simpa using hrr 7
  simp only [g_b0, g_b1, g_b2, g_b3, g_c0, g_c1, g_c2, g_c3,
    g_r0, g_r1, g_r2, g_r3, g_r4, g_r5, g_r6, g_r7]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · simp only [high_byte_eval input_b[0] input_b[0].val (ZMod.natCast_zmod_val _).symm,
      high_byte_eval input_cc[0] input_cc[0].val (ZMod.natCast_zmod_val _).symm]
    exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · simp only [high_byte_eval input_b[1] input_b[1].val (ZMod.natCast_zmod_val _).symm,
      high_byte_eval input_cc[1] input_cc[1].val (ZMod.natCast_zmod_val _).symm]
    exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · simp only [high_byte_eval input_b[2] input_b[2].val (ZMod.natCast_zmod_val _).symm,
      high_byte_eval input_cc[2] input_cc[2].val (ZMod.natCast_zmod_val _).symm]
    exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)
  · simp only [high_byte_eval input_b[3] input_b[3].val (ZMod.natCast_zmod_val _).symm,
      high_byte_eval input_cc[3] input_cc[3].val (ZMod.natCast_zmod_val _).symm]
    exact byteOpcodeSpec_cell input_opcode _ _ hop (by omega) (by omega)

/-- The pilot `FormalCircuit`: a genuinely semantic bitwise-u16 operation whose
byte witnesses are generated internally. Closing the two `sorry`s above makes it
axiom-clean. -/
def circuit : FormalCircuit (ZMod p) Inputs (fields 8) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SP1Clean.BitwiseU16OpWitnessed
