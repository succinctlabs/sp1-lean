import SP1Clean.FormalModel.Contracts.CoreSyscall
import SP1Clean.FormalModel.Contracts.RegisterRead

/-! # Instruction-authenticated native host calls

Each active instruction emits its full syscall word, arguments, return word, and event clock.
WRITE additionally reads x12 at event time plus one; other calls emit zero in the length field
and perform no extra register access. This interface binds the host tables to instruction rows;
the host tables must still establish the returned value and stateful effects.
-/

namespace SP1Clean.HostCallChip

open Circuit Channels

structure Inputs (F : Type) where
  instruction : SyscallInstrsChip.Inputs F
  length : Circuits.Types.RegisterAccessCols F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

structure Message (F : Type) where
  clk_high : F
  clk_low : F
  code : Word F
  arg1 : Word F
  arg2 : Word F
  result : Word F
  length : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Message

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_call"
  Guarantees _ _ := True

def writeWord {R : Type} [OfNat R 2] [Zero R] : Word R := #v[2, 0, 0, 0]

def writeFlag {p : ℕ} (word : Word (ZMod p)) : ZMod p :=
  if word = writeWord then 1 else 0

def Inputs.read {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R] [OfNat R 12]
    (input : Inputs R) (flag : R) : Readers.RegisterRead.Inputs R :=
  ⟨input.length, input.instruction.state.clk_high,
    input.instruction.state.clk_0_16 + input.instruction.state.clk_16_24 * 65536 + 1,
    12, input.instruction.is_real * flag⟩

def Inputs.message {R : Type} [Add R] [Mul R] [OfNat R 65536]
    (input : Inputs R) (flag : R) : Message R :=
  ⟨input.instruction.state.clk_high,
    input.instruction.state.clk_0_16 + input.instruction.state.clk_16_24 * 65536,
    input.instruction.op_a_memory.prev_value, input.instruction.op_b_memory.prev_value,
    input.instruction.op_c_memory.prev_value, input.instruction.op_a_value,
    input.length.prev_value.map (flag * ·)⟩

def Spec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] (input : Inputs (ZMod p)) : Prop :=
  CoreSyscallChip.Spec input.instruction ∧
    Readers.RegisterRead.Spec (input.read (writeFlag input.instruction.op_a_memory.prev_value))

end SP1Clean.HostCallChip
