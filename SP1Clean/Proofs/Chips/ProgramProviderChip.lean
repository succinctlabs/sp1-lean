import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import ToClean.Circuit.InteractionRecovery

/-! # The in-circuit Program-ROM provider (push side of SP1's preprocessed program/decode chip)

SP1's program chip is a **preprocessed** ROM over the committed program: it `receive`s every committed
instruction fetch — on the Program bus those receives are *pushes* of validly-decoded rows, balanced
against the CPU readers' pulls (the W11 polarity flip). Clean has no "trusted preprocessed table"
primitive for channels, so a finished-`programChannel` **provider must re-prove each pushed row valid
in-circuit** — the `ProgramMsg.RowSpec` membership predicate (`Model/Channels.lean`): the write-register
index `op_a < 32` (5-bit), the pc limbs `< 2^16` (16-bit), and `op_a_0` boolean.

This module is the in-circuit provider's push side: a single Clean `GeneralFormalCircuit` whose `main`
range-checks `op_a`/`pc0`/`pc1`/`pc2` in-circuit with Clean's `Gadgets.ToBits.rangeCheck` (genuine
bit-decomposition `assertion`s — *not* lookups, so the provider owes nothing to a bus), asserts `op_a_0`
boolean, reads an explicit multiplicity `m`, and `programChannel.pushIf m`-pushes the row; and whose soundness
discharges the push's `Requirements` (`ProgramMsg.RowSpec` of the pushed message, since `programChannel`'s
`Guarantees` is `RowSpec` and a `push` owes its guarantees). The remaining fields (`opcode`, `op_b*`,
`op_c*`, `imm_b`, `imm_c`) are part of the fetched message but unconstrained by `RowSpec` (immediate-type
fetches put immediates in those slots), so they are pushed through unchecked.

The byte-bus sibling is `Proofs/Chips/ByteChip/ByteChip.lean` (`U8Range.circuit`). -/

namespace SP1Clean.ProgramProviderChip

open Circuit
open SP1Clean.Channels (programChannel ProgramMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `p > 2`, needed by `Gadgets.ToBits.rangeCheck`'s `Fact (p > 2)`. `local` so it does not leak to
importing files (cf. `ByteChip`). -/
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2^5 < p` — the width bound `rangeCheck 5` needs for the register index. -/
lemma two_pow_five_lt : (2 : ℕ) ^ 5 < p := by
  have := Fact.out (p := 2 ^ 17 < p); omega

omit [Fact p.Prime] in
/-- `2^16 < p` — the width bound `rangeCheck 16` needs for the pc limbs. -/
lemma two_pow_sixteen_lt : (2 : ℕ) ^ 16 < p := by
  have := Fact.out (p := 2 ^ 17 < p); omega

/-- One program-provider row: the committed decode message together with its LogUp count. A zero
count is a padding row; a larger count aggregates repeated fetches of the same instruction. -/
structure Inputs (F : Type) where
  pc0 : F
  pc1 : F
  pc2 : F
  opcode : F
  op_a : F
  op_b : Word F
  op_c : Word F
  op_a_0 : F
  imm_b : F
  imm_c : F
  multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Forget the provider-only multiplicity column and recover the Program-bus payload. -/
def Inputs.toMessage {R : Type} (input : Inputs R) : ProgramMsg R where
  pc0 := input.pc0
  pc1 := input.pc1
  pc2 := input.pc2
  opcode := input.opcode
  op_a := input.op_a
  op_b := input.op_b
  op_c := input.op_c
  op_a_0 := input.op_a_0
  imm_b := input.imm_b
  imm_c := input.imm_c

omit [Fact (2 ^ 17 < p)] in
theorem Inputs.eval_toMessage (env : Environment (ZMod p)) (input : Var Inputs (ZMod p)) :
    eval env input.toMessage = (eval env input).toMessage := by
  simp only [ProvableStruct.eval_eq_eval]
  rfl

/-- Range-checks the write-register index `op_a` (5-bit) and the three pc limbs (16-bit), asserts `op_a_0`
boolean, and pushes the committed instruction fetch `input.toMessage` onto
`programChannel` with multiplicity `m`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.ToBits.rangeCheck 5 two_pow_five_lt) input.op_a
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.pc0
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.pc1
  assertion (Gadgets.ToBits.rangeCheck 16 two_pow_sixteen_lt) input.pc2
  assertion assertBool input.op_a_0
  programChannel.pushIf input.multiplicity input.toMessage

/-- The complete Program contribution retains every field of the provider input. -/
theorem main_program_interactions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      [(programChannel.pushedIf input.multiplicity input.toMessage).toRaw] := by
  have rangeEmpty (width : ℕ) (bound : 2 ^ width < p) (value : Expression (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil
      (Gadgets.ToBits.rangeCheck width bound) programChannel.toRaw value
      (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
      (by change programChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  have boolEmpty (n : ℕ) := InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    assertBool programChannel.toRaw input.op_a_0
    (by change programChannel.toRaw ∉ []; exact List.not_mem_nil)
    (by change programChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  simp only [circuit_norm] at boolEmpty
  simp only [main, circuit_norm, rangeEmpty, List.nil_append]
  rw [boolEmpty, List.nil_append]

/-- The Program-ROM provider: pushes a committed instruction fetch whose decode fields it range-checks
in-circuit. `Spec` is `ProgramMsg.RowSpec` (the rich membership facts the consumers pull-and-derive);
soundness discharges the push's `RowSpec` requirement from the range checks. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := "sp1.native.program"
  main
  Spec input _ _ := ProgramMsg.RowSpec input.toMessage
  ProverAssumptions input _ _ := ProgramMsg.RowSpec input.toMessage
  channelsWithRequirements := [programChannel.toRaw]
  soundness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, ProgramMsg.RowSpec, Inputs.toMessage]
    obtain ⟨hoa, hp0, hp1, hp2, hbool⟩ := h_holds
    have hrow : input_op_a.val < 32 ∧ input_pc0.val < 2 ^ 16 ∧
        input_pc1.val < 2 ^ 16 ∧ input_pc2.val < 2 ^ 16 ∧
        (input_op_a_0 = 0 ∨ input_op_a_0 = 1) :=
      ⟨by simpa using hoa, hp0, hp1, hp2, hbool⟩
    exact ⟨hrow, fun _ _ => hrow⟩
  completeness := by
    circuit_proof_start [Gadgets.ToBits.rangeCheck, ProgramMsg.RowSpec, Inputs.toMessage]
    obtain ⟨hoa, hp0, hp1, hp2, hbool⟩ := h_assumptions
    exact ⟨by simpa using hoa, hp0, hp1, hp2, hbool⟩

end SP1Clean.ProgramProviderChip
