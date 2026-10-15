import SP1Clean.FormalModel.Contracts.FinalRegisterValue
import SP1Clean.Math.WordEquality
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.StaticProvider

/-! # Fixed target-register authentication

The source and target use separate membership channels. Every sparse row consumes one complete
final record, including its clock, and authenticates its value through the target's verifier-fixed
register provider. The separate provider retains all 32 rows, including unused registers.
-/

namespace SP1Clean.FinalRegisterValue

open Circuit Model.Core Channels Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The target keeps the snapshot predicate with its own private channel identity. -/
def membership (target : MemorySnapshot) : StaticTable (ZMod p) RegisterSnapshotRow :=
  { target.registerTable with name := "sp1.native.target_registers" }

def main (target : MemorySnapshot) (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) Unit := do
  (membership target).channel.pull ⟨⟨input.addr0, input.value⟩, 1⟩
  assertZero input.addr1
  assertZero input.addr2
  (FinalMemoryValue.channel false).pull input

instance elaborated (target : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) MemoryMsg unit (main target) := by elaborate_circuit

omit [Fact (2 ^ 17 < p)] in
theorem receipt_values (target : MemorySnapshot) (input : Var MemoryMsg (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith (FinalMemoryValue.channel false).toRaw env =
      [(FinalMemoryValue.channel false).pulledValue (eval env input)] := by
  have raw : ((main target input).operations offset).interactionsWith (FinalMemoryValue.channel false).toRaw =
      [((FinalMemoryValue.channel false).pulled input).toRaw] := by
    simp [main, circuit_norm, membership, StaticTable.channel, FinalMemoryValue.channel]
  rw [Operations.interactionValuesWith, raw]
  exact congrArg (fun value => [value]) Channel.eval_pulled

def circuit (target : MemorySnapshot) : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  name := "sp1.native.memory.check.registers"
  main := main target
  elaborated := elaborated target
  Spec input _ _ := Spec target input
  ProverAssumptions input _ _ :=
    target.registerTable.Spec ⟨input.addr0, input.value⟩ ∧ input.addr1 = 0 ∧ input.addr2 = 0
  channelsWithRequirements := [(FinalMemoryValue.channel false).toRaw]
  soundness := by
    circuit_proof_start [FinalMemoryValue.channel, StaticTable.channel, membership]
    obtain ⟨member, one, two⟩ := h_holds
    obtain ⟨bound, range, value⟩ := target.registerTable_sound ⟨input_addr0, input_value⟩ member
    refine ⟨bound, one, two, range, ?_⟩
    simpa only [MemoryMsg.locOf, bound, one, two, and_self, ↓reduceIte] using value
  completeness := by
    circuit_proof_start [FinalMemoryValue.channel, StaticTable.channel, membership]
    exact h_assumptions

instance (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Decidable (Spec target record) := by
  unfold Spec Word.isU64
  infer_instance

/-- A final record is already the complete input; construction only checks its target value. -/
def populate? (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) : Option (MemoryMsg (ZMod p)) :=
  if Spec target record then some record else none

omit [Fact (2 ^ 17 < p)] in
theorem populate?_isSome_iff (target : MemorySnapshot) (record : MemoryMsg (ZMod p)) :
    (populate? target record).isSome = true ↔ Spec target record := by
  unfold populate?
  split <;> simp_all

theorem populate?_sound (target : MemorySnapshot) (record input : MemoryMsg (ZMod p))
    (found : populate? target record = some input) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    (circuit target).ProverAssumptions input data hint ∧ input = record := by
  unfold populate? at found
  split at found
  next valid =>
    obtain rfl := Option.some.inj found
    refine ⟨⟨?_, valid.2.1, valid.2.2.1⟩, rfl⟩
    apply (target.registerTable_spec _).mpr
    refine ⟨BitVec.ofNat 5 record.addr0.val, ?_⟩
    have index : (BitVec.ofNat 5 record.addr0.val).toNat = record.addr0.val :=
      Nat.mod_eq_of_lt valid.1
    have value : Soundness.Target.bitVecToWord
        (target.read (.reg (BitVec.ofNat 5 record.addr0.val))) = record.value := by
      apply Word.eq_of_toBitVec64_eq (Soundness.Target.isU64_bitVecToWord _) valid.2.2.2.1
      rw [Soundness.Target.toBitVec64_bitVecToWord, valid.2.2.2.2]
      simp only [MemoryMsg.locOf, valid.1, valid.2.1, valid.2.2.1, and_self, ↓reduceIte]
    simp only [MemorySnapshot.registerRow, index, ZMod.natCast_zmod_val, value]
  next invalid => contradiction

end SP1Clean.FinalRegisterValue
