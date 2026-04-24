import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader

namespace DivRem

set_option linter.style.setOption false
set_option maxHeartbeats 100000000
set_option linter.constructorNameAsVariable false
-- The chip's `correct_*` proofs drive an imbalanced goal tree via chained
-- `apply ... at` / `specialize ... at` that operates on one focused case at a
-- time. Rewriting each to `<;>` would flatten the tree but require goal-state
-- reasoning the linter can't see; keep the existing structure.
set_option linter.style.multiGoal false

variable (Main : Vector (Fin KB) 247)

section constraints

-- Generated Lean code for chip DivRemChip
@[irreducible] def constraints (Main : Vector (Fin KB) 246) : SP1ConstraintList :=
  let E0 : Fin KB := Main[205] + Main[206]
  let E1 : Fin KB := E0 + Main[207]
  let E2 : Fin KB := E1 + Main[208]
  let E3 : Fin KB := Main[202] + Main[204]
  let E4 : Fin KB := E3 + Main[201]
  let E5 : Fin KB := E4 + Main[203]
  let E6 : Fin KB := Main[205] + Main[206]
  let E7 : Fin KB := Main[207] + Main[208]
  let E8 : Fin KB := Main[201] + Main[203]
  let E9 : Fin KB := E8 + Main[205]
  let E10 : Fin KB := E9 + Main[206]
  let E11 : Fin KB := 1 - E2
  let E12 : Fin KB := Main[244] * E11
  let E13 : Fin KB := Main[239] - E12
  let E14 : Fin KB := Main[232] * E10
  let E15 : Fin KB := E14 - Main[236]
  let E16 : Fin KB := Main[233] * E10
  let E17 : Fin KB := E16 - Main[240]
  let E18 : Fin KB := Main[234] * E10
  let E19 : Fin KB := E18 - Main[241]
  let E20 : Fin KB := Main[15] - Main[32]
  let E21 : Fin KB := Main[22] - Main[36]
  let E22 : Fin KB := Main[16] - Main[33]
  let E23 : Fin KB := Main[23] - Main[37]
  let E24 : Fin KB := 1 - E2
  let E25 : Fin KB := Main[17] * E24
  let E26 : Fin KB := Main[236] * E2
  let E27 : Fin KB := E26 * 65535
  let E28 : Fin KB := E25 + E27
  let E29 : Fin KB := Main[34] - E28
  let E30 : Fin KB := 1 - E2
  let E31 : Fin KB := Main[24] * E30
  let E32 : Fin KB := Main[241] * E2
  let E33 : Fin KB := E32 * 65535
  let E34 : Fin KB := E31 + E33
  let E35 : Fin KB := Main[38] - E34
  let E36 : Fin KB := 1 - E2
  let E37 : Fin KB := Main[18] * E36
  let E38 : Fin KB := Main[236] * E2
  let E39 : Fin KB := E38 * 65535
  let E40 : Fin KB := E37 + E39
  let E41 : Fin KB := Main[35] - E40
  let E42 : Fin KB := 1 - E2
  let E43 : Fin KB := Main[25] * E42
  let E44 : Fin KB := Main[241] * E2
  let E45 : Fin KB := E44 * 65535
  let E46 : Fin KB := E43 + E45
  let E47 : Fin KB := Main[39] - E46
  let E48 : Fin KB := Main[44] - Main[40]
  let E49 : Fin KB := Main[45] - Main[41]
  let E50 : Fin KB := Main[46] - 0
  let E51 : Fin KB := E7 * E50
  let E52 : Fin KB := Main[235] * 65535
  let E53 : Fin KB := Main[46] - E52
  let E54 : Fin KB := E6 * E53
  let E55 : Fin KB := Main[235] * 65535
  let E56 : Fin KB := Main[42] - E55
  let E57 : Fin KB := E2 * E56
  let E58 : Fin KB := Main[46] - Main[42]
  let E59 : Fin KB := E5 * E58
  let E60 : Fin KB := Main[47] - 0
  let E61 : Fin KB := E7 * E60
  let E62 : Fin KB := Main[235] * 65535
  let E63 : Fin KB := Main[47] - E62
  let E64 : Fin KB := E6 * E63
  let E65 : Fin KB := Main[235] * 65535
  let E66 : Fin KB := Main[43] - E65
  let E67 : Fin KB := E2 * E66
  let E68 : Fin KB := Main[47] - Main[43]
  let E69 : Fin KB := E5 * E68
  let E70 : Fin KB := Main[48] - Main[52]
  let E71 : Fin KB := Main[49] - Main[53]
  let E72 : Fin KB := Main[50] - 0
  let E73 : Fin KB := E7 * E72
  let E74 : Fin KB := Main[233] * 65535
  let E75 : Fin KB := Main[50] - E74
  let E76 : Fin KB := E6 * E75
  let E77 : Fin KB := Main[233] * 65535
  let E78 : Fin KB := Main[54] - E77
  let E79 : Fin KB := E2 * E78
  let E80 : Fin KB := Main[50] - Main[54]
  let E81 : Fin KB := E5 * E80
  let E82 : Fin KB := Main[51] - 0
  let E83 : Fin KB := E7 * E82
  let E84 : Fin KB := Main[233] * 65535
  let E85 : Fin KB := Main[51] - E84
  let E86 : Fin KB := E6 * E85
  let E87 : Fin KB := Main[233] * 65535
  let E88 : Fin KB := Main[55] - E87
  let E89 : Fin KB := E2 * E88
  let E90 : Fin KB := Main[51] - Main[55]
  let E91 : Fin KB := E5 * E90
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[68], Main[69], Main[70], Main[71]] #v[Main[44], Main[45], Main[46], Main[47]] #v[Main[36], Main[37], Main[38], Main[39]] { carry := #v[Main[76], Main[77], Main[78], Main[79], Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91]], product := #v[Main[92], Main[93], Main[94], Main[95], Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107]], b_lower_byte := { low_bytes := #v[Main[108], Main[109], Main[110], Main[111]] }, c_lower_byte := { low_bytes := #v[Main[112], Main[113], Main[114], Main[115]] }, b_msb := Main[116], c_msb := Main[117], product_msb := { msb := Main[118] }, b_sign_extend := Main[119], c_sign_extend := Main[120] } Main[244] Main[244] 0 0 0 0
  let E92 : Fin KB := Main[201] + Main[203]
  let E93 : Fin KB := Main[202] + Main[204]
  let CS1 : SP1ConstraintList := MulOperation.constraints #v[Main[72], Main[73], Main[74], Main[75]] #v[Main[44], Main[45], Main[46], Main[47]] #v[Main[36], Main[37], Main[38], Main[39]] { carry := #v[Main[121], Main[122], Main[123], Main[124], Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136]], product := #v[Main[137], Main[138], Main[139], Main[140], Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152]], b_lower_byte := { low_bytes := #v[Main[153], Main[154], Main[155], Main[156]] }, c_lower_byte := { low_bytes := #v[Main[157], Main[158], Main[159], Main[160]] }, b_msb := Main[161], c_msb := Main[162], product_msb := { msb := Main[163] }, b_sign_extend := Main[164], c_sign_extend := Main[165] } Main[239] 0 E92 0 E93 0
  let CS2 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[0, 0, 0, 32768] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[210], result := Main[211] }, { inverse := Main[212], result := Main[213] }, { inverse := Main[214], result := Main[215] }, { inverse := Main[216], result := Main[217] }], is_zero_first_half := Main[218], is_zero_second_half := Main[219], result := Main[220] } } Main[239]
  let CS3 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[22], Main[23], Main[24], Main[25]] #v[65535, 65535, 65535, 65535] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[221], result := Main[222] }, { inverse := Main[223], result := Main[224] }, { inverse := Main[225], result := Main[226] }, { inverse := Main[227], result := Main[228] }], is_zero_first_half := Main[229], is_zero_second_half := Main[230], result := Main[231] } } Main[239]
  let CS4 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], 0, 0] #v[0, 32768, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[210], result := Main[211] }, { inverse := Main[212], result := Main[213] }, { inverse := Main[214], result := Main[215] }, { inverse := Main[216], result := Main[217] }], is_zero_first_half := Main[218], is_zero_second_half := Main[219], result := Main[220] } } E2
  let CS5 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[22], Main[23], 0, 0] #v[65535, 65535, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[221], result := Main[222] }, { inverse := Main[223], result := Main[224] }, { inverse := Main[225], result := Main[226] }, { inverse := Main[227], result := Main[228] }], is_zero_first_half := Main[229], is_zero_second_half := Main[230], result := Main[231] } } E2
  let E94 : Fin KB := Main[220] * Main[231]
  let E95 : Fin KB := E94 * E10
  let E96 : Fin KB := Main[209] - E95
  let E97 : Fin KB := 1 - Main[209]
  let E98 : Fin KB := Main[236] * E97
  let E99 : Fin KB := Main[237] - E98
  let E100 : Fin KB := 1 - Main[236]
  let E101 : Fin KB := 1 - Main[209]
  let E102 : Fin KB := E100 * E101
  let E103 : Fin KB := Main[238] - E102
  let E104 : Fin KB := Main[40] - Main[32]
  let E105 : Fin KB := Main[209] * E104
  let E106 : Fin KB := Main[52] - 0
  let E107 : Fin KB := Main[209] * E106
  let E108 : Fin KB := Main[41] - Main[33]
  let E109 : Fin KB := Main[209] * E108
  let E110 : Fin KB := Main[53] - 0
  let E111 : Fin KB := Main[209] * E110
  let E112 : Fin KB := Main[42] - Main[34]
  let E113 : Fin KB := Main[209] * E112
  let E114 : Fin KB := Main[54] - 0
  let E115 : Fin KB := Main[209] * E114
  let E116 : Fin KB := Main[43] - Main[35]
  let E117 : Fin KB := Main[209] * E116
  let E118 : Fin KB := Main[55] - 0
  let E119 : Fin KB := Main[209] * E118
  let E120 : Fin KB := Main[240] * 65535
  let E121 : Fin KB := Main[68] + Main[48]
  let E122 : Fin KB := Main[182] * 65536
  let E123 : Fin KB := E121 - E122
  let E124 : Fin KB := Main[69] + Main[49]
  let E125 : Fin KB := Main[183] * 65536
  let E126 : Fin KB := E124 - E125
  let E127 : Fin KB := E126 + Main[182]
  let E128 : Fin KB := Main[70] + Main[50]
  let E129 : Fin KB := Main[184] * 65536
  let E130 : Fin KB := E128 - E129
  let E131 : Fin KB := E130 + Main[183]
  let E132 : Fin KB := Main[71] + Main[51]
  let E133 : Fin KB := Main[185] * 65536
  let E134 : Fin KB := E132 - E133
  let E135 : Fin KB := E134 + Main[184]
  let E136 : Fin KB := Main[72] + E120
  let E137 : Fin KB := Main[186] * 65536
  let E138 : Fin KB := E136 - E137
  let E139 : Fin KB := E138 + Main[185]
  let E140 : Fin KB := Main[73] + E120
  let E141 : Fin KB := Main[187] * 65536
  let E142 : Fin KB := E140 - E141
  let E143 : Fin KB := E142 + Main[186]
  let E144 : Fin KB := Main[74] + E120
  let E145 : Fin KB := Main[188] * 65536
  let E146 : Fin KB := E144 - E145
  let E147 : Fin KB := E146 + Main[187]
  let E148 : Fin KB := Main[75] + E120
  let E149 : Fin KB := Main[189] * 65536
  let E150 : Fin KB := E148 - E149
  let E151 : Fin KB := E150 + Main[188]
  let E152 : Fin KB := Main[209] - 1
  let E153 : Fin KB := Main[32] - E123
  let E154 : Fin KB := E152 * E153
  let E155 : Fin KB := Main[209] - 1
  let E156 : Fin KB := Main[33] - E127
  let E157 : Fin KB := E155 * E156
  let E158 : Fin KB := Main[209] - 1
  let E159 : Fin KB := Main[34] - E131
  let E160 : Fin KB := E158 * E159
  let E161 : Fin KB := Main[209] - 1
  let E162 : Fin KB := Main[35] - E135
  let E163 : Fin KB := E161 * E162
  let E164 : Fin KB := Main[209] - 1
  let E165 : Fin KB := Main[236] * 65535
  let E166 : Fin KB := E165 - E139
  let E167 : Fin KB := E164 * E166
  let E168 : Fin KB := Main[209] - 1
  let E169 : Fin KB := Main[236] * 65535
  let E170 : Fin KB := E169 - E143
  let E171 : Fin KB := E168 * E170
  let E172 : Fin KB := Main[209] - 1
  let E173 : Fin KB := Main[236] * 65535
  let E174 : Fin KB := E173 - E147
  let E175 : Fin KB := E172 * E174
  let E176 : Fin KB := Main[209] - 1
  let E177 : Fin KB := Main[236] * 65535
  let E178 : Fin KB := E177 - E151
  let E179 : Fin KB := E176 * E178
  let E180 : Fin KB := Main[202] + Main[201]
  let E181 : Fin KB := E180 + Main[205]
  let E182 : Fin KB := E181 + Main[207]
  let E183 : Fin KB := Main[40] - Main[28]
  let E184 : Fin KB := E182 * E183
  let E185 : Fin KB := Main[204] + Main[203]
  let E186 : Fin KB := E185 + Main[206]
  let E187 : Fin KB := E186 + Main[208]
  let E188 : Fin KB := Main[52] - Main[28]
  let E189 : Fin KB := E187 * E188
  let E190 : Fin KB := Main[202] + Main[201]
  let E191 : Fin KB := E190 + Main[205]
  let E192 : Fin KB := E191 + Main[207]
  let E193 : Fin KB := Main[41] - Main[29]
  let E194 : Fin KB := E192 * E193
  let E195 : Fin KB := Main[204] + Main[203]
  let E196 : Fin KB := E195 + Main[206]
  let E197 : Fin KB := E196 + Main[208]
  let E198 : Fin KB := Main[53] - Main[29]
  let E199 : Fin KB := E197 * E198
  let E200 : Fin KB := Main[202] + Main[201]
  let E201 : Fin KB := E200 + Main[205]
  let E202 : Fin KB := E201 + Main[207]
  let E203 : Fin KB := Main[42] - Main[30]
  let E204 : Fin KB := E202 * E203
  let E205 : Fin KB := Main[204] + Main[203]
  let E206 : Fin KB := E205 + Main[206]
  let E207 : Fin KB := E206 + Main[208]
  let E208 : Fin KB := Main[54] - Main[30]
  let E209 : Fin KB := E207 * E208
  let E210 : Fin KB := Main[202] + Main[201]
  let E211 : Fin KB := E210 + Main[205]
  let E212 : Fin KB := E211 + Main[207]
  let E213 : Fin KB := Main[43] - Main[31]
  let E214 : Fin KB := E212 * E213
  let E215 : Fin KB := Main[204] + Main[203]
  let E216 : Fin KB := E215 + Main[206]
  let E217 : Fin KB := E216 + Main[208]
  let E218 : Fin KB := Main[55] - Main[31]
  let E219 : Fin KB := E217 * E218
  let E220 : Fin KB := 0 + Main[52]
  let E221 : Fin KB := E220 + Main[53]
  let E222 : Fin KB := E221 + Main[54]
  let E223 : Fin KB := E222 + Main[55]
  let E224 : Fin KB := Main[236] - 1
  let E225 : Fin KB := Main[240] * E224
  let E226 : Fin KB := 1 - Main[240]
  let E227 : Fin KB := E226 * Main[236]
  let E228 : Fin KB := E223 * E227
  let CS6 : SP1ConstraintList := IsZeroWordOperation.constraints #v[Main[36], Main[37], Main[38], Main[39]] { is_zero_limb := #v[{ inverse := Main[190], result := Main[191] }, { inverse := Main[192], result := Main[193] }, { inverse := Main[194], result := Main[195] }, { inverse := Main[196], result := Main[197] }], is_zero_first_half := Main[198], is_zero_second_half := Main[199], result := Main[200] } Main[244]
  let E229 : Fin KB := Main[40] - 65535
  let E230 : Fin KB := Main[200] * E229
  let E231 : Fin KB := Main[41] - 65535
  let E232 : Fin KB := Main[200] * E231
  let E233 : Fin KB := Main[42] - 65535
  let E234 : Fin KB := Main[200] * E233
  let E235 : Fin KB := Main[43] - 65535
  let E236 : Fin KB := Main[200] * E235
  let E237 : Fin KB := Main[48] - Main[32]
  let E238 : Fin KB := Main[200] * E237
  let E239 : Fin KB := Main[49] - Main[33]
  let E240 : Fin KB := Main[200] * E239
  let E241 : Fin KB := Main[50] - Main[34]
  let E242 : Fin KB := Main[200] * E241
  let E243 : Fin KB := Main[51] - Main[35]
  let E244 : Fin KB := Main[200] * E243
  let E245 : Fin KB := Main[241] - 1
  let E246 : Fin KB := Main[36] - Main[60]
  let E247 : Fin KB := E245 * E246
  let E248 : Fin KB := Main[240] - 1
  let E249 : Fin KB := Main[48] - Main[56]
  let E250 : Fin KB := E248 * E249
  let E251 : Fin KB := Main[241] - 1
  let E252 : Fin KB := Main[37] - Main[61]
  let E253 : Fin KB := E251 * E252
  let E254 : Fin KB := Main[240] - 1
  let E255 : Fin KB := Main[49] - Main[57]
  let E256 : Fin KB := E254 * E255
  let E257 : Fin KB := Main[241] - 1
  let E258 : Fin KB := Main[38] - Main[62]
  let E259 : Fin KB := E257 * E258
  let E260 : Fin KB := Main[240] - 1
  let E261 : Fin KB := Main[50] - Main[58]
  let E262 : Fin KB := E260 * E261
  let E263 : Fin KB := Main[241] - 1
  let E264 : Fin KB := Main[39] - Main[63]
  let E265 : Fin KB := E263 * E264
  let E266 : Fin KB := Main[240] - 1
  let E267 : Fin KB := Main[51] - Main[59]
  let E268 : Fin KB := E266 * E267
  let CS7 : SP1ConstraintList := AddOperation.constraints #v[Main[36], Main[37], Main[38], Main[39]] #v[Main[60], Main[61], Main[62], Main[63]] { value := #v[Main[166], Main[167], Main[168], Main[169]] } Main[242]
  let E269 : Fin KB := 0 - Main[166]
  let E270 : Fin KB := Main[242] * E269
  let E271 : Fin KB := 0 - Main[167]
  let E272 : Fin KB := Main[242] * E271
  let E273 : Fin KB := 0 - Main[168]
  let E274 : Fin KB := Main[242] * E273
  let E275 : Fin KB := 0 - Main[169]
  let E276 : Fin KB := Main[242] * E275
  let CS8 : SP1ConstraintList := AddOperation.constraints #v[Main[48], Main[49], Main[50], Main[51]] #v[Main[56], Main[57], Main[58], Main[59]] { value := #v[Main[170], Main[171], Main[172], Main[173]] } Main[243]
  let E277 : Fin KB := 0 - Main[170]
  let E278 : Fin KB := Main[243] * E277
  let E279 : Fin KB := 0 - Main[171]
  let E280 : Fin KB := Main[243] * E279
  let E281 : Fin KB := 0 - Main[172]
  let E282 : Fin KB := Main[243] * E281
  let E283 : Fin KB := 0 - Main[173]
  let E284 : Fin KB := Main[243] * E283
  let E285 : Fin KB := Main[241] * Main[244]
  let E286 : Fin KB := Main[242] - E285
  let E287 : Fin KB := Main[240] * Main[244]
  let E288 : Fin KB := Main[243] - E287
  let E289 : Fin KB := Main[200] * 1
  let E290 : Fin KB := 1 - Main[200]
  let E291 : Fin KB := E290 * Main[60]
  let E292 : Fin KB := E289 + E291
  let E293 : Fin KB := 1 - Main[200]
  let E294 : Fin KB := E293 * Main[61]
  let E295 : Fin KB := 1 - Main[200]
  let E296 : Fin KB := E295 * Main[62]
  let E297 : Fin KB := 1 - Main[200]
  let E298 : Fin KB := E297 * Main[63]
  let E299 : Fin KB := Main[64] - E292
  let E300 : Fin KB := Main[65] - E294
  let E301 : Fin KB := Main[66] - E296
  let E302 : Fin KB := Main[67] - E298
  let E303 : Fin KB := 1 - Main[200]
  let E304 : Fin KB := E303 * Main[244]
  let E305 : Fin KB := E304 - Main[245]
  let CS9 : SP1ConstraintList := LtOperationUnsigned.constraints #v[Main[56], Main[57], Main[58], Main[59]] #v[Main[64], Main[65], Main[66], Main[67]] { u16_compare_operation := { bit := Main[174] }, u16_flags := #v[Main[175], Main[176], Main[177], Main[178]], not_eq_inv := Main[179], comparison_limbs := #v[Main[180], Main[181]] } Main[245]
  let E306 : Fin KB := 1 - Main[174]
  let E307 : Fin KB := Main[245] * E306
  let CS10 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[232] } Main[239]
  let CS11 : SP1ConstraintList := U16MSBOperation.constraints Main[25] { msb := Main[234] } Main[239]
  let CS12 : SP1ConstraintList := U16MSBOperation.constraints Main[55] { msb := Main[233] } Main[239]
  let CS13 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[232] } E2
  let CS14 : SP1ConstraintList := U16MSBOperation.constraints Main[23] { msb := Main[234] } E2
  let CS15 : SP1ConstraintList := U16MSBOperation.constraints Main[53] { msb := Main[233] } E2
  let CS16 : SP1ConstraintList := U16MSBOperation.constraints Main[41] { msb := Main[235] } E2
  let E308 : Fin KB := Main[182] - 1
  let E309 : Fin KB := Main[182] * E308
  let E310 : Fin KB := Main[183] - 1
  let E311 : Fin KB := Main[183] * E310
  let E312 : Fin KB := Main[184] - 1
  let E313 : Fin KB := Main[184] * E312
  let E314 : Fin KB := Main[185] - 1
  let E315 : Fin KB := Main[185] * E314
  let E316 : Fin KB := Main[186] - 1
  let E317 : Fin KB := Main[186] * E316
  let E318 : Fin KB := Main[187] - 1
  let E319 : Fin KB := Main[187] * E318
  let E320 : Fin KB := Main[188] - 1
  let E321 : Fin KB := Main[188] * E320
  let E322 : Fin KB := Main[189] - 1
  let E323 : Fin KB := Main[189] * E322
  let E324 : Fin KB := Main[201] - 1
  let E325 : Fin KB := Main[201] * E324
  let E326 : Fin KB := Main[202] - 1
  let E327 : Fin KB := Main[202] * E326
  let E328 : Fin KB := Main[203] - 1
  let E329 : Fin KB := Main[203] * E328
  let E330 : Fin KB := Main[204] - 1
  let E331 : Fin KB := Main[204] * E330
  let E332 : Fin KB := Main[205] - 1
  let E333 : Fin KB := Main[205] * E332
  let E334 : Fin KB := Main[206] - 1
  let E335 : Fin KB := Main[206] * E334
  let E336 : Fin KB := Main[207] - 1
  let E337 : Fin KB := Main[207] * E336
  let E338 : Fin KB := Main[208] - 1
  let E339 : Fin KB := Main[208] * E338
  let E340 : Fin KB := Main[209] - 1
  let E341 : Fin KB := Main[209] * E340
  let E342 : Fin KB := Main[239] - 1
  let E343 : Fin KB := Main[239] * E342
  let E344 : Fin KB := Main[236] - 1
  let E345 : Fin KB := Main[236] * E344
  let E346 : Fin KB := Main[237] - 1
  let E347 : Fin KB := Main[237] * E346
  let E348 : Fin KB := Main[238] - 1
  let E349 : Fin KB := Main[238] * E348
  let E350 : Fin KB := Main[240] - 1
  let E351 : Fin KB := Main[240] * E350
  let E352 : Fin KB := Main[241] - 1
  let E353 : Fin KB := Main[241] * E352
  let E354 : Fin KB := Main[244] - 1
  let E355 : Fin KB := Main[244] * E354
  let E356 : Fin KB := Main[242] - 1
  let E357 : Fin KB := Main[242] * E356
  let E358 : Fin KB := Main[243] - 1
  let E359 : Fin KB := Main[243] * E358
  let E360 : Fin KB := Main[202] + Main[204]
  let E361 : Fin KB := E360 + Main[201]
  let E362 : Fin KB := E361 + Main[203]
  let E363 : Fin KB := E362 + Main[205]
  let E364 : Fin KB := E363 + Main[206]
  let E365 : Fin KB := E364 + Main[207]
  let E366 : Fin KB := E365 + Main[208]
  let E367 : Fin KB := 1 - E366
  let E368 : Fin KB := Main[202] * 16
  let E369 : Fin KB := Main[204] * 18
  let E370 : Fin KB := E368 + E369
  let E371 : Fin KB := Main[201] * 15
  let E372 : Fin KB := E370 + E371
  let E373 : Fin KB := Main[203] * 17
  let E374 : Fin KB := E372 + E373
  let E375 : Fin KB := Main[205] * 25
  let E376 : Fin KB := E374 + E375
  let E377 : Fin KB := Main[206] * 27
  let E378 : Fin KB := E376 + E377
  let E379 : Fin KB := Main[207] * 26
  let E380 : Fin KB := E378 + E379
  let E381 : Fin KB := Main[208] * 28
  let E382 : Fin KB := E380 + E381
  let E383 : Fin KB := Main[202] * 5
  let E384 : Fin KB := Main[204] * 7
  let E385 : Fin KB := E383 + E384
  let E386 : Fin KB := Main[201] * 4
  let E387 : Fin KB := E385 + E386
  let E388 : Fin KB := Main[203] * 6
  let E389 : Fin KB := E387 + E388
  let E390 : Fin KB := Main[205] * 4
  let E391 : Fin KB := E389 + E390
  let E392 : Fin KB := Main[206] * 6
  let E393 : Fin KB := E391 + E392
  let E394 : Fin KB := Main[207] * 5
  let E395 : Fin KB := E393 + E394
  let E396 : Fin KB := Main[208] * 7
  let E397 : Fin KB := E395 + E396
  let E398 : Fin KB := Main[202] * 1
  let E399 : Fin KB := Main[204] * 1
  let E400 : Fin KB := E398 + E399
  let E401 : Fin KB := Main[201] * 1
  let E402 : Fin KB := E400 + E401
  let E403 : Fin KB := Main[203] * 1
  let E404 : Fin KB := E402 + E403
  let E405 : Fin KB := Main[205] * 1
  let E406 : Fin KB := E404 + E405
  let E407 : Fin KB := Main[206] * 1
  let E408 : Fin KB := E406 + E407
  let E409 : Fin KB := Main[207] * 1
  let E410 : Fin KB := E408 + E409
  let E411 : Fin KB := Main[208] * 1
  let E412 : Fin KB := E410 + E411
  let E413 : Fin KB := Main[202] * 51
  let E414 : Fin KB := Main[204] * 51
  let E415 : Fin KB := E413 + E414
  let E416 : Fin KB := Main[201] * 51
  let E417 : Fin KB := E415 + E416
  let E418 : Fin KB := Main[203] * 51
  let E419 : Fin KB := E417 + E418
  let E420 : Fin KB := Main[205] * 59
  let E421 : Fin KB := E419 + E420
  let E422 : Fin KB := Main[206] * 59
  let E423 : Fin KB := E421 + E422
  let E424 : Fin KB := Main[207] * 59
  let E425 : Fin KB := E423 + E424
  let E426 : Fin KB := Main[208] * 59
  let E427 : Fin KB := E425 + E426
  let E428 : Fin KB := Main[202] * 8
  let E429 : Fin KB := Main[204] * 8
  let E430 : Fin KB := E428 + E429
  let E431 : Fin KB := Main[201] * 8
  let E432 : Fin KB := E430 + E431
  let E433 : Fin KB := Main[203] * 8
  let E434 : Fin KB := E432 + E433
  let E435 : Fin KB := Main[205] * 8
  let E436 : Fin KB := E434 + E435
  let E437 : Fin KB := Main[206] * 8
  let E438 : Fin KB := E436 + E437
  let E439 : Fin KB := Main[207] * 8
  let E440 : Fin KB := E438 + E439
  let E441 : Fin KB := Main[208] * 8
  let E442 : Fin KB := E440 + E441
  let E443 : Fin KB := Main[3] + 4
  let CS17 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E443, Main[4], Main[5]] 8 Main[244]
  let E444 : Fin KB := Main[1] * 65536
  let E445 : Fin KB := Main[2] + E444
  let CS18 : SP1ConstraintList := RTypeReader.constraints Main[0] E445 #v[Main[3], Main[4], Main[5]] E382 #v[E442, E427, E397, E412] #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } Main[244]
  CS0 ++ CS1 ++ CS2 ++ CS3 ++ CS4 ++ CS5 ++ CS6 ++ CS7 ++ CS8 ++ CS9 ++ CS10 ++ CS11 ++ CS12 ++ CS13 ++ CS14 ++ CS15 ++ CS16 ++ CS17 ++ CS18 ++ [
    (.assertZero E13),
    (.assertZero E15),
    (.assertZero E17),
    (.assertZero E19),
    (.assertZero E20),
    (.assertZero E21),
    (.assertZero E22),
    (.assertZero E23),
    (.assertZero E29),
    (.assertZero E35),
    (.assertZero E41),
    (.assertZero E47),
    (.assertZero E48),
    (.assertZero E49),
    (.assertZero E51),
    (.assertZero E54),
    (.assertZero E57),
    (.assertZero E59),
    (.assertZero E61),
    (.assertZero E64),
    (.assertZero E67),
    (.assertZero E69),
    (.assertZero E70),
    (.assertZero E71),
    (.assertZero E73),
    (.assertZero E76),
    (.assertZero E79),
    (.assertZero E81),
    (.assertZero E83),
    (.assertZero E86),
    (.assertZero E89),
    (.assertZero E91),
    (.assertZero E96),
    (.assertZero E99),
    (.assertZero E103),
    (.assertZero E105),
    (.assertZero E107),
    (.assertZero E109),
    (.assertZero E111),
    (.assertZero E113),
    (.assertZero E115),
    (.assertZero E117),
    (.assertZero E119),
    (.assertZero E154),
    (.assertZero E157),
    (.assertZero E160),
    (.assertZero E163),
    (.assertZero E167),
    (.assertZero E171),
    (.assertZero E175),
    (.assertZero E179),
    (.send (.byte (ByteOpcode.ofNat 6) E123 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E127 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E131 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E135 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E139 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E143 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E147 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) E151 16 0) Main[244]),
    (.assertZero E184),
    (.assertZero E189),
    (.assertZero E194),
    (.assertZero E199),
    (.assertZero E204),
    (.assertZero E209),
    (.assertZero E214),
    (.assertZero E219),
    (.assertZero E225),
    (.assertZero E228),
    (.assertZero E230),
    (.assertZero E232),
    (.assertZero E234),
    (.assertZero E236),
    (.assertZero E238),
    (.assertZero E240),
    (.assertZero E242),
    (.assertZero E244),
    (.assertZero E247),
    (.assertZero E250),
    (.assertZero E253),
    (.assertZero E256),
    (.assertZero E259),
    (.assertZero E262),
    (.assertZero E265),
    (.assertZero E268),
    (.send (.byte (ByteOpcode.ofNat 6) Main[60] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[61] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[62] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[63] 16 0) Main[244]),
    (.assertZero E270),
    (.assertZero E272),
    (.assertZero E274),
    (.assertZero E276),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[57] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[58] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[59] 16 0) Main[244]),
    (.assertZero E278),
    (.assertZero E280),
    (.assertZero E282),
    (.assertZero E284),
    (.assertZero E286),
    (.assertZero E288),
    (.assertZero E299),
    (.assertZero E300),
    (.assertZero E301),
    (.assertZero E302),
    (.assertZero E305),
    (.assertZero E307),
    (.send (.byte (ByteOpcode.ofNat 6) Main[40] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[41] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[42] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[43] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[52] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] 16 0) Main[244]),
    (.assertZero E309),
    (.assertZero E311),
    (.assertZero E313),
    (.assertZero E315),
    (.assertZero E317),
    (.assertZero E319),
    (.assertZero E321),
    (.assertZero E323),
    (.send (.byte (ByteOpcode.ofNat 6) Main[68] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[69] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[70] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[71] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[72] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[73] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[74] 16 0) Main[244]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[75] 16 0) Main[244]),
    (.assertZero E325),
    (.assertZero E327),
    (.assertZero E329),
    (.assertZero E331),
    (.assertZero E333),
    (.assertZero E335),
    (.assertZero E337),
    (.assertZero E339),
    (.assertZero E341),
    (.assertZero E343),
    (.assertZero E345),
    (.assertZero E347),
    (.assertZero E349),
    (.assertZero E351),
    (.assertZero E353),
    (.assertZero E355),
    (.assertZero E357),
    (.assertZero E359),
    (.assertZero E367),
    (.assertZero Main[13]),
  ]

end constraints

-- DivRem has 8 variant one-hot flags; indices in the generated constraints are complex.
-- Using placeholder indices. User needs to verify.
@[simp] def is_div (Main : Vector (Fin KB) 246) := Main[238] = 1
@[simp] def is_divu (Main : Vector (Fin KB) 246) := Main[239] = 1
@[simp] def is_rem (Main : Vector (Fin KB) 246) := Main[240] = 1
@[simp] def is_remu (Main : Vector (Fin KB) 246) := Main[241] = 1
@[simp] def is_divw (Main : Vector (Fin KB) 246) := Main[242] = 1
@[simp] def is_divuw (Main : Vector (Fin KB) 246) := Main[243] = 1
@[simp] def is_remw (Main : Vector (Fin KB) 246) := Main[244] = 1
@[simp] def is_remuw (Main : Vector (Fin KB) 246) := Main[245] = 1




@[simp]
def sp1_op_a {Main : Vector (Fin KB) 246} (_ : (constraints Main).allHold) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

@[simp]
def sp1_op_b {Main : Vector (Fin KB) 246} (_ : (constraints Main).allHold) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

@[simp]
def sp1_op_c {Main : Vector (Fin KB) 246} (_ : (constraints Main).allHold) : BitVec 5 :=
  BitVec.ofNat 5 Main[21]

end DivRem
