import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.AddChip.Formal
import SP1Clean.Proofs.Chips.AddiChip.Formal
import SP1Clean.Proofs.Chips.AddwChip.Formal
import SP1Clean.Proofs.Chips.SubChip.Formal
import SP1Clean.Proofs.Chips.SubwChip.Formal
import SP1Clean.Proofs.Chips.BitwiseChip.Formal
import SP1Clean.Proofs.Chips.LtChip.Formal
import SP1Clean.Proofs.Chips.ShiftLeftChip.Formal
import SP1Clean.Proofs.Chips.ShiftRightChip.Formal
import SP1Clean.Proofs.Chips.JalChip.Formal
import SP1Clean.Proofs.Chips.JalrChip.Formal
import SP1Clean.Proofs.Chips.BranchChip.Formal
import SP1Clean.Proofs.Chips.UTypeChip.Formal
import SP1Clean.Proofs.Chips.LoadByteChip.Formal
import SP1Clean.Proofs.Chips.LoadHalfChip.Formal
import SP1Clean.Proofs.Chips.LoadWordChip.Formal
import SP1Clean.Proofs.Chips.LoadDoubleChip.Formal
import SP1Clean.Proofs.Chips.LoadX0Chip.Formal
import SP1Clean.Proofs.Chips.StoreByteChip.Formal
import SP1Clean.Proofs.Chips.StoreHalfChip.Formal
import SP1Clean.Proofs.Chips.StoreWordChip.Formal
import SP1Clean.Proofs.Chips.StoreDoubleChip.Formal
import SP1Clean.Proofs.Chips.MulChip.Formal
import SP1Clean.Proofs.Chips.DivRemChip.Complete
import SP1Clean.Proofs.Chips.AluX0Chip.Formal

/-! # Instruction-local Rust export

Export production instruction components through Clean's built-in lowering and Rust emitter.
Each surrounding singleton has no providers: its channels remain open, so it is a row-level
comparison fixture, not an executable SP1 ensemble or a proof of global balance.
-/

namespace SP1CleanTest.Core.InstructionExport

open Air.Flat SP1Clean

open ComponentExport

/-- All supported instruction families in release order. DivRem alone selects DIVU on padding;
the other components generate their padding witnesses from zero inputs. -/
def rustExports : List (String × Except String String) := [
  ("add_instruction.rs", exportRust "AddInstruction" AddChip.circuit),
  ("addi_instruction.rs", exportRust "AddiInstruction" AddiChip.circuit),
  ("addw_instruction.rs", exportRust "AddwInstruction" AddwChip.circuit),
  ("sub_instruction.rs", exportRust "SubInstruction" SubChip.circuit),
  ("subw_instruction.rs", exportRust "SubwInstruction" SubwChip.circuit),
  ("bitwise_instruction.rs", exportRust "BitwiseInstruction" BitwiseChip.circuit),
  ("lt_instruction.rs", exportRust "LtInstruction" LtChip.circuit),
  ("shift_left_instruction.rs", exportRust "ShiftLeftInstruction" ShiftLeftChip.circuit),
  ("shift_right_instruction.rs", exportRust "ShiftRightInstruction" ShiftRightChip.circuit),
  ("jal_instruction.rs", exportRust "JalInstruction" JalChip.circuit),
  ("jalr_instruction.rs", exportRust "JalrInstruction" JalrChip.circuit),
  ("branch_instruction.rs", exportRust "BranchInstruction" BranchChip.circuit),
  ("u_type_instruction.rs", exportRust "UTypeInstruction" UTypeChip.circuit),
  ("load_byte_instruction.rs", exportRust "LoadByteInstruction" LoadByteChip.circuit),
  ("load_half_instruction.rs", exportRust "LoadHalfInstruction" LoadHalfChip.circuit),
  ("load_word_instruction.rs", exportRust "LoadWordInstruction" LoadWordChip.circuit),
  ("load_double_instruction.rs", exportRust "LoadDoubleInstruction" LoadDoubleChip.circuit),
  ("load_x0_instruction.rs", exportRust "LoadX0Instruction" LoadX0Chip.circuit),
  ("store_byte_instruction.rs", exportRust "StoreByteInstruction" StoreByteChip.circuit),
  ("store_half_instruction.rs", exportRust "StoreHalfInstruction" StoreHalfChip.circuit),
  ("store_word_instruction.rs", exportRust "StoreWordInstruction" StoreWordChip.circuit),
  ("store_double_instruction.rs", exportRust "StoreDoubleInstruction" StoreDoubleChip.circuit),
  ("mul_instruction.rs", exportRust "MulInstruction" MulChip.circuit),
  ("div_rem_instruction.rs", Extraction.Rust.ensembleToRust "DivRemInstruction"
    (ensemble { circuit := DivRemChip.circuit })
    ({ config DivRemChip.Inputs with
      padding := [{ input := (toElements (TraceGen.divRemPaddingInputs (p := SP1Prime))).toArray }] } :
      WitnessGeneration.Config Fp DivRemChip.Inputs)),
  ("alu_x0_instruction.rs", exportRust "AluX0Instruction" AluX0Chip.circuit)]

end SP1CleanTest.Core.InstructionExport
