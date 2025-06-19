import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace BitwiseChip


def constraints
  (Main : Vector BabyBear 23)
  : SP1ConstraintList :=
  let E0 : BabyBear := Main[22] - 1
  let E2 : BabyBear := Main[22] * E0
  let E4 : BabyBear := Main[3] + 4
  let E6 : BabyBear := 16384 * Main[1]
  let E8 : BabyBear := E6 + Main[2]
  [ .assertZero E2
  ]
  ++ (AddOperation.constraints #v[Main[11], Main[12], Main[16], Main[17], Main[20], Main[21], Main[22]])
  ++ (CPUState.constraints
      { shard := Main[0]
      , clk_high_limb := Main[1]
      , clk_low_limb := Main[2]
      , pc := Main[3] }
      E4
      4
      Main[22])
  ++ (RTypeReader.constraints
    Main[0]
    E8
    -- Main[3]
    -- 0
    #v[Main[20], Main[21]]
    { op_a := Main[4]
    , op_a_memory :=
        { prev_value := #v[Main[5], Main[6]]
        , access_timestamp :=
            { prev_clk := Main[7]
            , diff_low_limb := Main[8]
            }
        }
    , op_a_0 := Main[9]
    , op_b := Main[10]
    , op_b_memory :=
        { prev_value := #v[Main[11], Main[12]]
        , access_timestamp :=
            { prev_clk := Main[13]
            , diff_low_limb := Main[14]
            }
        }
    , op_c := Main[15]
    , op_c_memory :=
        { prev_value := #v[Main[16], Main[17]]
        , access_timestamp :=
            { prev_clk := Main[18]
            , diff_low_limb := Main[19]
            }
        }
    }
    Main[22])

end BitwiseChip
