import SP1Operations

-- namespace SubChip

-- def constraints (Main : Vector (Fin BB) 23) : SP1ConstraintList :=
--   let E0 : Fin BB := Main[22] - 1
--   let E1 : Fin BB := Main[22] * E0
--   let CS0 : SP1ConstraintList := SubOperation.constraints #v[Main[11], Main[12]] #v[Main[16], Main[17]] { value := #v[Main[20], Main[21]] } Main[22]
--   let E2 : Fin BB := Main[3] + 4
--   let CS1 : SP1ConstraintList := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E2 8 Main[22]
--   let E3 : Fin BB := Main[1] * 65536
--   let E4 : Fin BB := Main[2] + E3
--   let CS2 : SP1ConstraintList := RTypeReader.constraints Main[0] E4 Main[3] 2 #v[Main[20], Main[21]] { op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := Main[15], op_c_memory := { access_timestamp := { diff_low_limb := Main[19], prev_low := Main[18] }, prev_value := #v[Main[16], Main[17]] } } Main[22]
--   [
--     .assertZero E1
--   ] ++ CS0 ++ CS1 ++ CS2

-- end SubChip
