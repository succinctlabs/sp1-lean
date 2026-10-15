import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Model.Semantics.MicroTime

/-! # One register read with unchanged read-back

The caller binds the register index and access clock. The reader authenticates a bounded word
and strict prior/access time order, emitting that same word at both timestamps.
-/

namespace SP1Clean.Readers.RegisterRead

open Circuit Channels

structure Inputs (F : Type) where
  cols : Circuits.Types.RegisterAccessCols F
  clk_high : F
  clk_target : F
  index : F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def Inputs.prior {R : Type} [Zero R] (input : Inputs R) : MemoryMsg R :=
  ⟨input.clk_high, input.cols.access_timestamp.prev_low, input.index, 0, 0, input.cols.prev_value⟩

def Inputs.pushed {R : Type} [Zero R] (input : Inputs R) : MemoryMsg R :=
  ⟨input.clk_high, input.clk_target, input.index, 0, 0, input.cols.prev_value⟩

def Assumptions {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ ClkDisciplineAt input.clk_target input.is_real

def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 → Word.isU64 input.cols.prev_value ∧ MemoryMsg.ClkBound input.prior ∧
    Semantics.MemoryMsg.timeNat input.prior < Semantics.MemoryMsg.timeNat input.pushed

end SP1Clean.Readers.RegisterRead
