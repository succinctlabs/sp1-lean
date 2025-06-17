import SP1Foundations
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

namespace BitwiseU16Operation



end BitwiseU16Operation

namespace BitwiseChip

-- def constraints
--   (Main : Vector BabyBear 128)
--   : Finset SP1Constraint
--   :=
--   let E0 := Main[30] + Main[31]
--   let E2 := E0 + Main[32]
--   let E4 := Main[30] - 1
--   let E6 := Main[30] * E4
--   let E8 := Main[31] - 1
--   let E10 := Main[31] * E8
--   let E12 := Main[32] - 1
--   let E14 := Main[32] * E12
--   let E16 := E2 - 1
--   let E18 := E2 * E16
--   let E20 := Main[30] * 2
--   let E22 := Main[31] * 1
--   let E24 := E20 + E22
--   let E26 := Main[32] * 0
--   let E28 := E24 + E26
--   let E30 := Main[30] * 3
--   let E32 := Main[31] * 4
--   let E34 := E30 + E32
--   let E36 := Main[32] * 5
--   let E38 := E34 + E36
--   let E42 := Main[3] + 4
--   let E44 := 16384 * Main[1]
--   let E46 := E44 + Main[2]
--   let E48 := E2 - 1
--   let E50 := E2 * E48
--   let E52 := E46 + 4
--   let E54 := 16384 * Main[1]
--   let E56 := E54 + Main[2]
--   let E58 := E2 - 1
--   let E60 := E2 * E58
--   let E62 := E2 - 1
--   let E64 := Main[21] - 0
--   let E66 := E62 * E64
--   let E68 := 0 + Main[10]
--   let E70 := E40 - 0
--   let E72 := Main[9] * E70
--   let E74 := E41 - 0
--   let E76 := Main[9] * E74
--   let E78 := E56 + 3
--   let E80 := E2 - 1
--   let E82 := E2 * E80
--   let E84 := E78 - Main[7]
--   let E86 := E84 - 1
--   let E88 := E86 - Main[8]
--   let E90 := E88 * 2013143041
--   let E92 := E56 + 2
--   let E94 := E2 - 1
--   let E96 := E2 * E94
--   let E98 := E92 - Main[13]
--   let E100 := E98 - 1
--   let E102 := E100 - Main[14]
--   let E104 := E102 * 2013143041
--   let E106 := E56 + 1
--   let E108 := E2 - Main[21]
--   let E110 := E108 - 1
--   let E112 := E108 * E110
--   let E114 := E106 - Main[19]
--   let E116 := E114 - 1
--   let E118 := E116 - Main[20]
--   let E120 := E118 * 2013143041
--   let E122 := Main[17] - Main[15]
--   let E124 := Main[21] * E122
--   let E126 := Main[18] - Main[16]
--   let E128 := Main[21] * E126
--   _


end BitwiseChip
