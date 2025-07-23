-- import SP1Foundations
-- import SP1Operations.MemoryConsistency
-- import LeanRV32IM.RiscvRegs

-- open Sail
-- open LeanRV32IM.Functions

-- --- A Reader that only accesses values of type `T`.
-- structure JTypeReader (T : Type) where
--   op_a : T
--   op_a_memory : MemoryAccessInSharedCols
--   op_a_0 : T
--   op_b_imm : Word T
--   op_c_imm : Word T
