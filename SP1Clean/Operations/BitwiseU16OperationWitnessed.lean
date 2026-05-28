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

-- CLOSURE STEP 1 (soundness, ≈ `spec.{and,or,xor}` content, 3 opcodes):
-- After `intro …; simp [circuit_norm, main, ByteOpcodeTable]`, `h_holds` gives
-- 8 `ByteOpcodeSpec` facts. Via `BitwiseOp.Spec_of_ByteOpcodeSpec_when_lt7`
-- (opcode.val < 3 < 7) get per-byte `(ofNat opcode.val).constrain`, i.e.
-- `result[i].val = decompB[i].val OP decompC[i].val` with all bytes < 256.
-- The decomp bytes sum to the limbs algebraically (the `(b-low)·256⁻¹` form),
-- so reconstruct `resultWord = b OP c` per opcode by the `spec.and` recipe
-- (`Word.toBitVec64`, byte `.val` arithmetic, `bv_decide`).
theorem soundness : Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

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
  sorry

/-- The pilot `FormalCircuit`: a genuinely semantic bitwise-u16 operation whose
byte witnesses are generated internally. Closing the two `sorry`s above makes it
axiom-clean. -/
def circuit : FormalCircuit (ZMod p) Inputs (fields 8) where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SP1Clean.BitwiseU16OpWitnessed
