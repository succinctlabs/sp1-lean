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
@[irreducible] def constraints (Main : Vector (Fin KB) 247) : SP1ConstraintList :=
  let E0 : Fin KB := Main[206] + Main[207]
  let E1 : Fin KB := E0 + Main[208]
  let E2 : Fin KB := E1 + Main[209]
  let E3 : Fin KB := Main[203] + Main[205]
  let E4 : Fin KB := E3 + Main[202]
  let E5 : Fin KB := E4 + Main[204]
  let E6 : Fin KB := Main[206] + Main[207]
  let E7 : Fin KB := Main[208] + Main[209]
  let E8 : Fin KB := Main[202] + Main[204]
  let E9 : Fin KB := E8 + Main[206]
  let E10 : Fin KB := E9 + Main[207]
  let E11 : Fin KB := 1 - E2
  let E12 : Fin KB := Main[245] * E11
  let E13 : Fin KB := Main[240] - E12
  let E14 : Fin KB := Main[233] * E10
  let E15 : Fin KB := E14 - Main[237]
  let E16 : Fin KB := Main[234] * E10
  let E17 : Fin KB := E16 - Main[241]
  let E18 : Fin KB := Main[235] * E10
  let E19 : Fin KB := E18 - Main[242]
  let E20 : Fin KB := Main[15] - Main[33]
  let E21 : Fin KB := Main[22] - Main[37]
  let E22 : Fin KB := Main[16] - Main[34]
  let E23 : Fin KB := Main[23] - Main[38]
  let E24 : Fin KB := 1 - E2
  let E25 : Fin KB := Main[17] * E24
  let E26 : Fin KB := Main[237] * E2
  let E27 : Fin KB := E26 * 65535
  let E28 : Fin KB := E25 + E27
  let E29 : Fin KB := Main[35] - E28
  let E30 : Fin KB := 1 - E2
  let E31 : Fin KB := Main[24] * E30
  let E32 : Fin KB := Main[242] * E2
  let E33 : Fin KB := E32 * 65535
  let E34 : Fin KB := E31 + E33
  let E35 : Fin KB := Main[39] - E34
  let E36 : Fin KB := 1 - E2
  let E37 : Fin KB := Main[18] * E36
  let E38 : Fin KB := Main[237] * E2
  let E39 : Fin KB := E38 * 65535
  let E40 : Fin KB := E37 + E39
  let E41 : Fin KB := Main[36] - E40
  let E42 : Fin KB := 1 - E2
  let E43 : Fin KB := Main[25] * E42
  let E44 : Fin KB := Main[242] * E2
  let E45 : Fin KB := E44 * 65535
  let E46 : Fin KB := E43 + E45
  let E47 : Fin KB := Main[40] - E46
  let E48 : Fin KB := Main[45] - Main[41]
  let E49 : Fin KB := Main[46] - Main[42]
  let E50 : Fin KB := Main[47] - 0
  let E51 : Fin KB := E7 * E50
  let E52 : Fin KB := Main[236] * 65535
  let E53 : Fin KB := Main[47] - E52
  let E54 : Fin KB := E6 * E53
  let E55 : Fin KB := Main[236] * 65535
  let E56 : Fin KB := Main[43] - E55
  let E57 : Fin KB := E2 * E56
  let E58 : Fin KB := Main[47] - Main[43]
  let E59 : Fin KB := E5 * E58
  let E60 : Fin KB := Main[48] - 0
  let E61 : Fin KB := E7 * E60
  let E62 : Fin KB := Main[236] * 65535
  let E63 : Fin KB := Main[48] - E62
  let E64 : Fin KB := E6 * E63
  let E65 : Fin KB := Main[236] * 65535
  let E66 : Fin KB := Main[44] - E65
  let E67 : Fin KB := E2 * E66
  let E68 : Fin KB := Main[48] - Main[44]
  let E69 : Fin KB := E5 * E68
  let E70 : Fin KB := Main[49] - Main[53]
  let E71 : Fin KB := Main[50] - Main[54]
  let E72 : Fin KB := Main[51] - 0
  let E73 : Fin KB := E7 * E72
  let E74 : Fin KB := Main[234] * 65535
  let E75 : Fin KB := Main[51] - E74
  let E76 : Fin KB := E6 * E75
  let E77 : Fin KB := Main[234] * 65535
  let E78 : Fin KB := Main[55] - E77
  let E79 : Fin KB := E2 * E78
  let E80 : Fin KB := Main[51] - Main[55]
  let E81 : Fin KB := E5 * E80
  let E82 : Fin KB := Main[52] - 0
  let E83 : Fin KB := E7 * E82
  let E84 : Fin KB := Main[234] * 65535
  let E85 : Fin KB := Main[52] - E84
  let E86 : Fin KB := E6 * E85
  let E87 : Fin KB := Main[234] * 65535
  let E88 : Fin KB := Main[56] - E87
  let E89 : Fin KB := E2 * E88
  let E90 : Fin KB := Main[52] - Main[56]
  let E91 : Fin KB := E5 * E90
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[69], Main[70], Main[71], Main[72]] #v[Main[45], Main[46], Main[47], Main[48]] #v[Main[37], Main[38], Main[39], Main[40]] { carry := #v[Main[77], Main[78], Main[79], Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91], Main[92]], product := #v[Main[93], Main[94], Main[95], Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107], Main[108]], b_lower_byte := { low_bytes := #v[Main[109], Main[110], Main[111], Main[112]] }, c_lower_byte := { low_bytes := #v[Main[113], Main[114], Main[115], Main[116]] }, b_msb := Main[117], c_msb := Main[118], product_msb := { msb := Main[119] }, b_sign_extend := Main[120], c_sign_extend := Main[121] } Main[245] Main[245] 0 0 0 0
  let E92 : Fin KB := Main[202] + Main[204]
  let E93 : Fin KB := Main[203] + Main[205]
  let CS1 : SP1ConstraintList := MulOperation.constraints #v[Main[73], Main[74], Main[75], Main[76]] #v[Main[45], Main[46], Main[47], Main[48]] #v[Main[37], Main[38], Main[39], Main[40]] { carry := #v[Main[122], Main[123], Main[124], Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136], Main[137]], product := #v[Main[138], Main[139], Main[140], Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152], Main[153]], b_lower_byte := { low_bytes := #v[Main[154], Main[155], Main[156], Main[157]] }, c_lower_byte := { low_bytes := #v[Main[158], Main[159], Main[160], Main[161]] }, b_msb := Main[162], c_msb := Main[163], product_msb := { msb := Main[164] }, b_sign_extend := Main[165], c_sign_extend := Main[166] } Main[240] 0 E92 0 E93 0
  let CS2 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[0, 0, 0, 32768] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[211], result := Main[212] }, { inverse := Main[213], result := Main[214] }, { inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }], is_zero_first_half := Main[219], is_zero_second_half := Main[220], result := Main[221] } } Main[240]
  let CS3 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[22], Main[23], Main[24], Main[25]] #v[65535, 65535, 65535, 65535] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[222], result := Main[223] }, { inverse := Main[224], result := Main[225] }, { inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }], is_zero_first_half := Main[230], is_zero_second_half := Main[231], result := Main[232] } } Main[240]
  let CS4 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], 0, 0] #v[0, 32768, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[211], result := Main[212] }, { inverse := Main[213], result := Main[214] }, { inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }], is_zero_first_half := Main[219], is_zero_second_half := Main[220], result := Main[221] } } E2
  let CS5 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[22], Main[23], 0, 0] #v[65535, 65535, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[222], result := Main[223] }, { inverse := Main[224], result := Main[225] }, { inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }], is_zero_first_half := Main[230], is_zero_second_half := Main[231], result := Main[232] } } E2
  let E94 : Fin KB := Main[221] * Main[232]
  let E95 : Fin KB := E94 * E10
  let E96 : Fin KB := Main[210] - E95
  let E97 : Fin KB := 1 - Main[210]
  let E98 : Fin KB := Main[237] * E97
  let E99 : Fin KB := Main[238] - E98
  let E100 : Fin KB := 1 - Main[237]
  let E101 : Fin KB := 1 - Main[210]
  let E102 : Fin KB := E100 * E101
  let E103 : Fin KB := Main[239] - E102
  let E104 : Fin KB := Main[41] - Main[33]
  let E105 : Fin KB := Main[210] * E104
  let E106 : Fin KB := Main[53] - 0
  let E107 : Fin KB := Main[210] * E106
  let E108 : Fin KB := Main[42] - Main[34]
  let E109 : Fin KB := Main[210] * E108
  let E110 : Fin KB := Main[54] - 0
  let E111 : Fin KB := Main[210] * E110
  let E112 : Fin KB := Main[43] - Main[35]
  let E113 : Fin KB := Main[210] * E112
  let E114 : Fin KB := Main[55] - 0
  let E115 : Fin KB := Main[210] * E114
  let E116 : Fin KB := Main[44] - Main[36]
  let E117 : Fin KB := Main[210] * E116
  let E118 : Fin KB := Main[56] - 0
  let E119 : Fin KB := Main[210] * E118
  let E120 : Fin KB := Main[241] * 65535
  let E121 : Fin KB := Main[69] + Main[49]
  let E122 : Fin KB := Main[183] * 65536
  let E123 : Fin KB := E121 - E122
  let E124 : Fin KB := Main[70] + Main[50]
  let E125 : Fin KB := Main[184] * 65536
  let E126 : Fin KB := E124 - E125
  let E127 : Fin KB := E126 + Main[183]
  let E128 : Fin KB := Main[71] + Main[51]
  let E129 : Fin KB := Main[185] * 65536
  let E130 : Fin KB := E128 - E129
  let E131 : Fin KB := E130 + Main[184]
  let E132 : Fin KB := Main[72] + Main[52]
  let E133 : Fin KB := Main[186] * 65536
  let E134 : Fin KB := E132 - E133
  let E135 : Fin KB := E134 + Main[185]
  let E136 : Fin KB := Main[73] + E120
  let E137 : Fin KB := Main[187] * 65536
  let E138 : Fin KB := E136 - E137
  let E139 : Fin KB := E138 + Main[186]
  let E140 : Fin KB := Main[74] + E120
  let E141 : Fin KB := Main[188] * 65536
  let E142 : Fin KB := E140 - E141
  let E143 : Fin KB := E142 + Main[187]
  let E144 : Fin KB := Main[75] + E120
  let E145 : Fin KB := Main[189] * 65536
  let E146 : Fin KB := E144 - E145
  let E147 : Fin KB := E146 + Main[188]
  let E148 : Fin KB := Main[76] + E120
  let E149 : Fin KB := Main[190] * 65536
  let E150 : Fin KB := E148 - E149
  let E151 : Fin KB := E150 + Main[189]
  let E152 : Fin KB := Main[210] - 1
  let E153 : Fin KB := Main[33] - E123
  let E154 : Fin KB := E152 * E153
  let E155 : Fin KB := Main[210] - 1
  let E156 : Fin KB := Main[34] - E127
  let E157 : Fin KB := E155 * E156
  let E158 : Fin KB := Main[210] - 1
  let E159 : Fin KB := Main[35] - E131
  let E160 : Fin KB := E158 * E159
  let E161 : Fin KB := Main[210] - 1
  let E162 : Fin KB := Main[36] - E135
  let E163 : Fin KB := E161 * E162
  let E164 : Fin KB := Main[210] - 1
  let E165 : Fin KB := Main[237] * 65535
  let E166 : Fin KB := E165 - E139
  let E167 : Fin KB := E164 * E166
  let E168 : Fin KB := Main[210] - 1
  let E169 : Fin KB := Main[237] * 65535
  let E170 : Fin KB := E169 - E143
  let E171 : Fin KB := E168 * E170
  let E172 : Fin KB := Main[210] - 1
  let E173 : Fin KB := Main[237] * 65535
  let E174 : Fin KB := E173 - E147
  let E175 : Fin KB := E172 * E174
  let E176 : Fin KB := Main[210] - 1
  let E177 : Fin KB := Main[237] * 65535
  let E178 : Fin KB := E177 - E151
  let E179 : Fin KB := E176 * E178
  let E180 : Fin KB := Main[203] + Main[202]
  let E181 : Fin KB := E180 + Main[206]
  let E182 : Fin KB := E181 + Main[208]
  let E183 : Fin KB := Main[41] - Main[29]
  let E184 : Fin KB := E182 * E183
  let E185 : Fin KB := Main[205] + Main[204]
  let E186 : Fin KB := E185 + Main[207]
  let E187 : Fin KB := E186 + Main[209]
  let E188 : Fin KB := Main[53] - Main[29]
  let E189 : Fin KB := E187 * E188
  let E190 : Fin KB := Main[203] + Main[202]
  let E191 : Fin KB := E190 + Main[206]
  let E192 : Fin KB := E191 + Main[208]
  let E193 : Fin KB := Main[42] - Main[30]
  let E194 : Fin KB := E192 * E193
  let E195 : Fin KB := Main[205] + Main[204]
  let E196 : Fin KB := E195 + Main[207]
  let E197 : Fin KB := E196 + Main[209]
  let E198 : Fin KB := Main[54] - Main[30]
  let E199 : Fin KB := E197 * E198
  let E200 : Fin KB := Main[203] + Main[202]
  let E201 : Fin KB := E200 + Main[206]
  let E202 : Fin KB := E201 + Main[208]
  let E203 : Fin KB := Main[43] - Main[31]
  let E204 : Fin KB := E202 * E203
  let E205 : Fin KB := Main[205] + Main[204]
  let E206 : Fin KB := E205 + Main[207]
  let E207 : Fin KB := E206 + Main[209]
  let E208 : Fin KB := Main[55] - Main[31]
  let E209 : Fin KB := E207 * E208
  let E210 : Fin KB := Main[203] + Main[202]
  let E211 : Fin KB := E210 + Main[206]
  let E212 : Fin KB := E211 + Main[208]
  let E213 : Fin KB := Main[44] - Main[32]
  let E214 : Fin KB := E212 * E213
  let E215 : Fin KB := Main[205] + Main[204]
  let E216 : Fin KB := E215 + Main[207]
  let E217 : Fin KB := E216 + Main[209]
  let E218 : Fin KB := Main[56] - Main[32]
  let E219 : Fin KB := E217 * E218
  let E220 : Fin KB := 0 + Main[53]
  let E221 : Fin KB := E220 + Main[54]
  let E222 : Fin KB := E221 + Main[55]
  let E223 : Fin KB := E222 + Main[56]
  let E224 : Fin KB := Main[237] - 1
  let E225 : Fin KB := Main[241] * E224
  let E226 : Fin KB := 1 - Main[241]
  let E227 : Fin KB := E226 * Main[237]
  let E228 : Fin KB := E223 * E227
  let CS6 : SP1ConstraintList := IsZeroWordOperation.constraints #v[Main[37], Main[38], Main[39], Main[40]] { is_zero_limb := #v[{ inverse := Main[191], result := Main[192] }, { inverse := Main[193], result := Main[194] }, { inverse := Main[195], result := Main[196] }, { inverse := Main[197], result := Main[198] }], is_zero_first_half := Main[199], is_zero_second_half := Main[200], result := Main[201] } Main[245]
  let E229 : Fin KB := Main[41] - 65535
  let E230 : Fin KB := Main[201] * E229
  let E231 : Fin KB := Main[42] - 65535
  let E232 : Fin KB := Main[201] * E231
  let E233 : Fin KB := Main[43] - 65535
  let E234 : Fin KB := Main[201] * E233
  let E235 : Fin KB := Main[44] - 65535
  let E236 : Fin KB := Main[201] * E235
  let E237 : Fin KB := Main[49] - Main[33]
  let E238 : Fin KB := Main[201] * E237
  let E239 : Fin KB := Main[50] - Main[34]
  let E240 : Fin KB := Main[201] * E239
  let E241 : Fin KB := Main[51] - Main[35]
  let E242 : Fin KB := Main[201] * E241
  let E243 : Fin KB := Main[52] - Main[36]
  let E244 : Fin KB := Main[201] * E243
  let E245 : Fin KB := Main[242] - 1
  let E246 : Fin KB := Main[37] - Main[61]
  let E247 : Fin KB := E245 * E246
  let E248 : Fin KB := Main[241] - 1
  let E249 : Fin KB := Main[49] - Main[57]
  let E250 : Fin KB := E248 * E249
  let E251 : Fin KB := Main[242] - 1
  let E252 : Fin KB := Main[38] - Main[62]
  let E253 : Fin KB := E251 * E252
  let E254 : Fin KB := Main[241] - 1
  let E255 : Fin KB := Main[50] - Main[58]
  let E256 : Fin KB := E254 * E255
  let E257 : Fin KB := Main[242] - 1
  let E258 : Fin KB := Main[39] - Main[63]
  let E259 : Fin KB := E257 * E258
  let E260 : Fin KB := Main[241] - 1
  let E261 : Fin KB := Main[51] - Main[59]
  let E262 : Fin KB := E260 * E261
  let E263 : Fin KB := Main[242] - 1
  let E264 : Fin KB := Main[40] - Main[64]
  let E265 : Fin KB := E263 * E264
  let E266 : Fin KB := Main[241] - 1
  let E267 : Fin KB := Main[52] - Main[60]
  let E268 : Fin KB := E266 * E267
  let CS7 : SP1ConstraintList := AddOperation.constraints #v[Main[37], Main[38], Main[39], Main[40]] #v[Main[61], Main[62], Main[63], Main[64]] { value := #v[Main[167], Main[168], Main[169], Main[170]] } Main[243]
  let E269 : Fin KB := 0 - Main[167]
  let E270 : Fin KB := Main[243] * E269
  let E271 : Fin KB := 0 - Main[168]
  let E272 : Fin KB := Main[243] * E271
  let E273 : Fin KB := 0 - Main[169]
  let E274 : Fin KB := Main[243] * E273
  let E275 : Fin KB := 0 - Main[170]
  let E276 : Fin KB := Main[243] * E275
  let CS8 : SP1ConstraintList := AddOperation.constraints #v[Main[49], Main[50], Main[51], Main[52]] #v[Main[57], Main[58], Main[59], Main[60]] { value := #v[Main[171], Main[172], Main[173], Main[174]] } Main[244]
  let E277 : Fin KB := 0 - Main[171]
  let E278 : Fin KB := Main[244] * E277
  let E279 : Fin KB := 0 - Main[172]
  let E280 : Fin KB := Main[244] * E279
  let E281 : Fin KB := 0 - Main[173]
  let E282 : Fin KB := Main[244] * E281
  let E283 : Fin KB := 0 - Main[174]
  let E284 : Fin KB := Main[244] * E283
  let E285 : Fin KB := Main[242] * Main[245]
  let E286 : Fin KB := Main[243] - E285
  let E287 : Fin KB := Main[241] * Main[245]
  let E288 : Fin KB := Main[244] - E287
  let E289 : Fin KB := Main[201] * 1
  let E290 : Fin KB := 1 - Main[201]
  let E291 : Fin KB := E290 * Main[61]
  let E292 : Fin KB := E289 + E291
  let E293 : Fin KB := 1 - Main[201]
  let E294 : Fin KB := E293 * Main[62]
  let E295 : Fin KB := 1 - Main[201]
  let E296 : Fin KB := E295 * Main[63]
  let E297 : Fin KB := 1 - Main[201]
  let E298 : Fin KB := E297 * Main[64]
  let E299 : Fin KB := Main[65] - E292
  let E300 : Fin KB := Main[66] - E294
  let E301 : Fin KB := Main[67] - E296
  let E302 : Fin KB := Main[68] - E298
  let E303 : Fin KB := 1 - Main[201]
  let E304 : Fin KB := E303 * Main[245]
  let E305 : Fin KB := E304 - Main[246]
  let CS9 : SP1ConstraintList := LtOperationUnsigned.constraints #v[Main[57], Main[58], Main[59], Main[60]] #v[Main[65], Main[66], Main[67], Main[68]] { u16_compare_operation := { bit := Main[175] }, u16_flags := #v[Main[176], Main[177], Main[178], Main[179]], not_eq_inv := Main[180], comparison_limbs := #v[Main[181], Main[182]] } Main[246]
  let E306 : Fin KB := 1 - Main[175]
  let E307 : Fin KB := Main[246] * E306
  let CS10 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[233] } Main[240]
  let CS11 : SP1ConstraintList := U16MSBOperation.constraints Main[25] { msb := Main[235] } Main[240]
  let CS12 : SP1ConstraintList := U16MSBOperation.constraints Main[56] { msb := Main[234] } Main[240]
  let CS13 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[233] } E2
  let CS14 : SP1ConstraintList := U16MSBOperation.constraints Main[23] { msb := Main[235] } E2
  let CS15 : SP1ConstraintList := U16MSBOperation.constraints Main[54] { msb := Main[234] } E2
  let CS16 : SP1ConstraintList := U16MSBOperation.constraints Main[42] { msb := Main[236] } E2
  let E308 : Fin KB := Main[183] - 1
  let E309 : Fin KB := Main[183] * E308
  let E310 : Fin KB := Main[184] - 1
  let E311 : Fin KB := Main[184] * E310
  let E312 : Fin KB := Main[185] - 1
  let E313 : Fin KB := Main[185] * E312
  let E314 : Fin KB := Main[186] - 1
  let E315 : Fin KB := Main[186] * E314
  let E316 : Fin KB := Main[187] - 1
  let E317 : Fin KB := Main[187] * E316
  let E318 : Fin KB := Main[188] - 1
  let E319 : Fin KB := Main[188] * E318
  let E320 : Fin KB := Main[189] - 1
  let E321 : Fin KB := Main[189] * E320
  let E322 : Fin KB := Main[190] - 1
  let E323 : Fin KB := Main[190] * E322
  let E324 : Fin KB := Main[202] - 1
  let E325 : Fin KB := Main[202] * E324
  let E326 : Fin KB := Main[203] - 1
  let E327 : Fin KB := Main[203] * E326
  let E328 : Fin KB := Main[204] - 1
  let E329 : Fin KB := Main[204] * E328
  let E330 : Fin KB := Main[205] - 1
  let E331 : Fin KB := Main[205] * E330
  let E332 : Fin KB := Main[206] - 1
  let E333 : Fin KB := Main[206] * E332
  let E334 : Fin KB := Main[207] - 1
  let E335 : Fin KB := Main[207] * E334
  let E336 : Fin KB := Main[208] - 1
  let E337 : Fin KB := Main[208] * E336
  let E338 : Fin KB := Main[209] - 1
  let E339 : Fin KB := Main[209] * E338
  let E340 : Fin KB := Main[210] - 1
  let E341 : Fin KB := Main[210] * E340
  let E342 : Fin KB := Main[240] - 1
  let E343 : Fin KB := Main[240] * E342
  let E344 : Fin KB := Main[237] - 1
  let E345 : Fin KB := Main[237] * E344
  let E346 : Fin KB := Main[238] - 1
  let E347 : Fin KB := Main[238] * E346
  let E348 : Fin KB := Main[239] - 1
  let E349 : Fin KB := Main[239] * E348
  let E350 : Fin KB := Main[241] - 1
  let E351 : Fin KB := Main[241] * E350
  let E352 : Fin KB := Main[242] - 1
  let E353 : Fin KB := Main[242] * E352
  let E354 : Fin KB := Main[245] - 1
  let E355 : Fin KB := Main[245] * E354
  let E356 : Fin KB := Main[243] - 1
  let E357 : Fin KB := Main[243] * E356
  let E358 : Fin KB := Main[244] - 1
  let E359 : Fin KB := Main[244] * E358
  let E360 : Fin KB := Main[203] + Main[205]
  let E361 : Fin KB := E360 + Main[202]
  let E362 : Fin KB := E361 + Main[204]
  let E363 : Fin KB := E362 + Main[206]
  let E364 : Fin KB := E363 + Main[207]
  let E365 : Fin KB := E364 + Main[208]
  let E366 : Fin KB := E365 + Main[209]
  let E367 : Fin KB := 1 - E366
  let E368 : Fin KB := Main[203] * 16
  let E369 : Fin KB := Main[205] * 18
  let E370 : Fin KB := E368 + E369
  let E371 : Fin KB := Main[202] * 15
  let E372 : Fin KB := E370 + E371
  let E373 : Fin KB := Main[204] * 17
  let E374 : Fin KB := E372 + E373
  let E375 : Fin KB := Main[206] * 48
  let E376 : Fin KB := E374 + E375
  let E377 : Fin KB := Main[207] * 50
  let E378 : Fin KB := E376 + E377
  let E379 : Fin KB := Main[208] * 49
  let E380 : Fin KB := E378 + E379
  let E381 : Fin KB := Main[209] * 51
  let E382 : Fin KB := E380 + E381
  let E383 : Fin KB := Main[203] * 5
  let E384 : Fin KB := Main[205] * 7
  let E385 : Fin KB := E383 + E384
  let E386 : Fin KB := Main[202] * 4
  let E387 : Fin KB := E385 + E386
  let E388 : Fin KB := Main[204] * 6
  let E389 : Fin KB := E387 + E388
  let E390 : Fin KB := Main[206] * 4
  let E391 : Fin KB := E389 + E390
  let E392 : Fin KB := Main[207] * 6
  let E393 : Fin KB := E391 + E392
  let E394 : Fin KB := Main[208] * 5
  let E395 : Fin KB := E393 + E394
  let E396 : Fin KB := Main[209] * 7
  let E397 : Fin KB := E395 + E396
  let E398 : Fin KB := Main[203] * 1
  let E399 : Fin KB := Main[205] * 1
  let E400 : Fin KB := E398 + E399
  let E401 : Fin KB := Main[202] * 1
  let E402 : Fin KB := E400 + E401
  let E403 : Fin KB := Main[204] * 1
  let E404 : Fin KB := E402 + E403
  let E405 : Fin KB := Main[206] * 1
  let E406 : Fin KB := E404 + E405
  let E407 : Fin KB := Main[207] * 1
  let E408 : Fin KB := E406 + E407
  let E409 : Fin KB := Main[208] * 1
  let E410 : Fin KB := E408 + E409
  let E411 : Fin KB := Main[209] * 1
  let E412 : Fin KB := E410 + E411
  let E413 : Fin KB := Main[203] * 51
  let E414 : Fin KB := Main[205] * 51
  let E415 : Fin KB := E413 + E414
  let E416 : Fin KB := Main[202] * 51
  let E417 : Fin KB := E415 + E416
  let E418 : Fin KB := Main[204] * 51
  let E419 : Fin KB := E417 + E418
  let E420 : Fin KB := Main[206] * 59
  let E421 : Fin KB := E419 + E420
  let E422 : Fin KB := Main[207] * 59
  let E423 : Fin KB := E421 + E422
  let E424 : Fin KB := Main[208] * 59
  let E425 : Fin KB := E423 + E424
  let E426 : Fin KB := Main[209] * 59
  let E427 : Fin KB := E425 + E426
  let E428 : Fin KB := Main[203] * 8
  let E429 : Fin KB := Main[205] * 8
  let E430 : Fin KB := E428 + E429
  let E431 : Fin KB := Main[202] * 8
  let E432 : Fin KB := E430 + E431
  let E433 : Fin KB := Main[204] * 8
  let E434 : Fin KB := E432 + E433
  let E435 : Fin KB := Main[206] * 8
  let E436 : Fin KB := E434 + E435
  let E437 : Fin KB := Main[207] * 8
  let E438 : Fin KB := E436 + E437
  let E439 : Fin KB := Main[208] * 8
  let E440 : Fin KB := E438 + E439
  let E441 : Fin KB := Main[3] + 4
  let CS17 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E441, Main[4], Main[5]] 8 Main[245]
  let E442 : Fin KB := Main[1] * 65536
  let E443 : Fin KB := Main[2] + E442
  let CS18 : SP1ConstraintList := RTypeReader.constraints Main[0] E443 #v[Main[3], Main[4], Main[5]] E382 #v[E440, E427, E397, E412] #v[Main[29], Main[30], Main[31], Main[32]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } }, is_trusted := Main[28] } Main[245]
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
    (.send (.byte (ByteOpcode.ofNat 6) E123 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E127 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E131 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E135 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E139 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E143 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E147 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) E151 16 0) Main[245]),
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[61] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[62] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[63] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[64] 16 0) Main[245]),
    (.assertZero E270),
    (.assertZero E272),
    (.assertZero E274),
    (.assertZero E276),
    (.send (.byte (ByteOpcode.ofNat 6) Main[57] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[58] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[59] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[60] 16 0) Main[245]),
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[41] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[42] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[43] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[44] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[53] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[54] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[55] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] 16 0) Main[245]),
    (.assertZero E309),
    (.assertZero E311),
    (.assertZero E313),
    (.assertZero E315),
    (.assertZero E317),
    (.assertZero E319),
    (.assertZero E321),
    (.assertZero E323),
    (.send (.byte (ByteOpcode.ofNat 6) Main[69] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[70] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[71] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[72] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[73] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[74] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[75] 16 0) Main[245]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[76] 16 0) Main[245]),
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
  ]

end constraints

set_option maxRecDepth 1000000 in
lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[69], Main[70], Main[71], Main[72]]
      #v[Main[45], Main[46], Main[47], Main[48]] #v[Main[37], Main[38], Main[39], Main[40]]
      {
        carry := #v[Main[77], Main[78], Main[79], Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91], Main[92]],
        product := #v[Main[93], Main[94], Main[95], Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107], Main[108]],
        b_lower_byte := { low_bytes := #v[Main[109], Main[110], Main[111], Main[112]] },
        c_lower_byte := { low_bytes := #v[Main[113], Main[114], Main[115], Main[116]] },
        b_msb := Main[117],
        c_msb := Main[118],
        product_msb := { msb := Main[119] },
        b_sign_extend := Main[120],
        c_sign_extend := Main[121]
      }
      Main[245] Main[245] 0 0 0 0) ∧
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[73], Main[74], Main[75], Main[76]]
      #v[Main[45], Main[46], Main[47], Main[48]]
      #v[Main[37], Main[38], Main[39], Main[40]]
      {
        carry := #v[Main[122], Main[123], Main[124], Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136], Main[137]],
        product := #v[Main[138], Main[139], Main[140], Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152], Main[153]],
        b_lower_byte := { low_bytes := #v[Main[154], Main[155], Main[156], Main[157]] },
        c_lower_byte := { low_bytes := #v[Main[158], Main[159], Main[160], Main[161]] },
        b_msb := Main[162],
        c_msb := Main[163],
        product_msb := { msb := Main[164] },
        b_sign_extend := Main[165],
        c_sign_extend := Main[166]
      }
      Main[240] 0 (Main[202] + Main[204]) 0 (Main[203] + Main[205]) 0) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[0, 0, 0, 32768]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[211], result := Main[212] }, { inverse := Main[213], result := Main[214] }, { inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }],
          is_zero_first_half := Main[219],
          is_zero_second_half := Main[220],
          result := Main[221]
        }
      }
      Main[240]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[22], Main[23], Main[24], Main[25]]
      #v[65535, 65535, 65535, 65535]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[222], result := Main[223] }, { inverse := Main[224], result := Main[225] }, { inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }],
          is_zero_first_half := Main[230],
          is_zero_second_half := Main[231],
          result := Main[232]
        }
      }
      Main[240]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], 0, 0]
      #v[0, 32768, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[211], result := Main[212] }, { inverse := Main[213], result := Main[214] }, { inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }],
          is_zero_first_half := Main[219],
          is_zero_second_half := Main[220],
          result := Main[221]
        }
      }
      (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[22], Main[23], 0, 0]
      #v[65535, 65535, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[222], result := Main[223] }, { inverse := Main[224], result := Main[225] }, { inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }],
          is_zero_first_half := Main[230],
          is_zero_second_half := Main[231],
          result := Main[232]
        }
      }
      (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp
    (IsZeroWordOperation.constraints
      #v[Main[37], Main[38], Main[39], Main[40]]
      {
        is_zero_limb := #v[{ inverse := Main[191], result := Main[192] }, { inverse := Main[193], result := Main[194] }, { inverse := Main[195], result := Main[196] }, { inverse := Main[197], result := Main[198] }],
        is_zero_first_half := Main[199],
        is_zero_second_half := Main[200],
        result := Main[201]
      }
      Main[245]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[37], Main[38], Main[39], Main[40]]
      #v[Main[61], Main[62], Main[63], Main[64]]
      { value := #v[Main[167], Main[168], Main[169], Main[170]] }
      Main[243]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[49], Main[50], Main[51], Main[52]]
      #v[Main[57], Main[58], Main[59], Main[60]]
      { value := #v[Main[171], Main[172], Main[173], Main[174]] }
      Main[244]) ∧
    List.Forall SP1Constraint.toProp
    (LtOperationUnsigned.constraints
      #v[Main[57], Main[58], Main[59], Main[60]]
      #v[Main[65], Main[66], Main[67], Main[68]]
      {
          u16_compare_operation := { bit := Main[175] },
          u16_flags := #v[Main[176], Main[177], Main[178], Main[179]]
          not_eq_inv := Main[180],
          comparison_limbs := #v[Main[181], Main[182]]
      }
      Main[246]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[18] { msb := Main[233] } Main[240]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[25] { msb := Main[235] } Main[240]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[56] { msb := Main[234] } Main[240]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[16] { msb := Main[233] } (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[23] { msb := Main[235] } (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[54] { msb := Main[234] } (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[42] { msb := Main[236] } (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    List.Forall SP1Constraint.toProp
      (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
        #v[Main[3] + 4, Main[4], Main[5]] 8 Main[245]) ∧
    List.Forall SP1Constraint.toProp
        (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]]
          (Main[203] * 16 + Main[205] * 18 + Main[202] * 15 + Main[204] * 17 + Main[206] * 48 + Main[207] * 50 + Main[208] * 49 + Main[209] * 51)
          #v[Main[203] * 8 + Main[205] * 8 + Main[202] * 8 + Main[204] * 8 + Main[206] * 8 + Main[207] * 8 + Main[208] * 8,
            Main[203] * 51 + Main[205] * 51 + Main[202] * 51 + Main[204] * 51 + Main[206] * 59 + Main[207] * 59 + Main[208] * 59 + Main[209] * 59,
            Main[203] * 5 + Main[205] * 7 + Main[202] * 4 + Main[204] * 6 + Main[206] * 4 + Main[207] * 6 + Main[208] * 5 + Main[209] * 7,
            Main[203] + Main[205] + Main[202] + Main[204] + Main[206] + Main[207] + Main[208] + Main[209]]
          #v[Main[29], Main[30], Main[31], Main[32]]
          { op_a := Main[6],
            op_a_memory :=
              { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
            op_a_0 := Main[13], op_b := Main[14],
            op_b_memory :=
              { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
            op_c := Main[21],
            op_c_memory :=
              { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } },
            is_trusted := Main[28] }
          Main[245]) ∧
    Main[240] = Main[245] * (1 - (Main[206] + Main[207] + Main[208] + Main[209])) ∧
    Main[237] = Main[233] * (Main[202] + Main[204] + Main[206] + Main[207]) ∧
    Main[241] = Main[234] * (Main[202] + Main[204] + Main[206] + Main[207]) ∧
    Main[242] = Main[235] * (Main[202] + Main[204] + Main[206] + Main[207]) ∧
    Main[15] = Main[33] ∧
    Main[22] = Main[37] ∧
    Main[16] = Main[34] ∧
    Main[23] = Main[38] ∧
    Main[35] = Main[17] * (1 - (Main[206] + Main[207] + Main[208] + Main[209])) + Main[237] * (Main[206] + Main[207] + Main[208] + Main[209]) * 65535 ∧
    Main[39] = Main[24] * (1 - (Main[206] + Main[207] + Main[208] + Main[209])) + Main[242] * (Main[206] + Main[207] + Main[208] + Main[209]) * 65535 ∧
    Main[36] = Main[18] * (1 - (Main[206] + Main[207] + Main[208] + Main[209])) + Main[237] * (Main[206] + Main[207] + Main[208] + Main[209]) * 65535 ∧
    Main[40] = Main[25] * (1 - (Main[206] + Main[207] + Main[208] + Main[209])) + Main[242] * (Main[206] + Main[207] + Main[208] + Main[209]) * 65535 ∧
    Main[45] = Main[41] ∧
    Main[46] = Main[42] ∧
    (Main[208] + Main[209] = 0 ∨ Main[47] = 0) ∧
    (Main[206] + Main[207] = 0 ∨ Main[47] = Main[236] * 65535) ∧
    (Main[206] + Main[207] + Main[208] + Main[209] = 0 ∨ Main[43] = Main[236] * 65535) ∧
    (Main[203] + Main[205] + Main[202] + Main[204] = 0 ∨ Main[47] = Main[43]) ∧
    (Main[208] + Main[209] = 0 ∨ Main[48] = 0) ∧
    (Main[206] + Main[207] = 0 ∨ Main[48] = Main[236] * 65535) ∧
    (Main[206] + Main[207] + Main[208] + Main[209] = 0 ∨ Main[44] = Main[236] * 65535) ∧
    (Main[203] + Main[205] + Main[202] + Main[204] = 0 ∨ Main[48] = Main[44]) ∧
    Main[49] = Main[53] ∧
    Main[50] = Main[54] ∧
    (Main[208] + Main[209] = 0 ∨ Main[51] = 0) ∧
    (Main[206] + Main[207] = 0 ∨ Main[51] = Main[234] * 65535) ∧
    (Main[206] + Main[207] + Main[208] + Main[209] = 0 ∨ Main[55] = Main[234] * 65535) ∧
    (Main[203] + Main[205] + Main[202] + Main[204] = 0 ∨ Main[51] = Main[55]) ∧
    (Main[208] + Main[209] = 0 ∨ Main[52] = 0) ∧
    (Main[206] + Main[207] = 0 ∨ Main[52] = Main[234] * 65535) ∧
    (Main[206] + Main[207] + Main[208] + Main[209] = 0 ∨ Main[56] = Main[234] * 65535) ∧
    (Main[203] + Main[205] + Main[202] + Main[204] = 0 ∨ Main[52] = Main[56]) ∧
    Main[210] = Main[221] * Main[232] * (Main[202] + Main[204] + Main[206] + Main[207]) ∧
    Main[238] = Main[237] * (1 - Main[210]) ∧
    Main[239] = (1 - Main[237]) * (1 - Main[210]) ∧
    (Main[210] = 0 ∨ Main[41] = Main[33]) ∧
    (Main[210] = 0 ∨ Main[53] = 0) ∧
    (Main[210] = 0 ∨ Main[42] = Main[34]) ∧
    (Main[210] = 0 ∨ Main[54] = 0) ∧
    (Main[210] = 0 ∨ Main[43] = Main[35]) ∧
    (Main[210] = 0 ∨ Main[55] = 0) ∧
    (Main[210] = 0 ∨ Main[44] = Main[36]) ∧
    (Main[210] = 0 ∨ Main[56] = 0) ∧
    (Main[210] = 1 ∨ Main[33] = Main[69] + Main[49] - Main[183] * 65536) ∧
    (Main[210] = 1 ∨ Main[34] = Main[70] + Main[50] - Main[184] * 65536 + Main[183]) ∧
    (Main[210] = 1 ∨ Main[35] = Main[71] + Main[51] - Main[185] * 65536 + Main[184]) ∧
    (Main[210] = 1 ∨ Main[36] = Main[72] + Main[52] - Main[186] * 65536 + Main[185]) ∧
    (Main[210] = 1 ∨ Main[237] * 65535 = Main[73] + Main[241] * 65535 - Main[187] * 65536 + Main[186]) ∧
    (Main[210] = 1 ∨ Main[237] * 65535 = Main[74] + Main[241] * 65535 - Main[188] * 65536 + Main[187]) ∧
    (Main[210] = 1 ∨ Main[237] * 65535 =  Main[75] + Main[241] * 65535 - Main[189] * 65536 + Main[188]) ∧
    (Main[210] = 1 ∨ Main[237] * 65535 = Main[76] + Main[241] * 65535 - Main[190] * 65536 + Main[189]) ∧
    (¬Main[245] = 0 → (Main[69] + Main[49] - Main[183] * 65536).val < 65536) ∧
    (¬Main[245] = 0 → (Main[70] + Main[50] - Main[184] * 65536 + Main[183]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[71] + Main[51] - Main[185] * 65536 + Main[184]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[72] + Main[52] - Main[186] * 65536 + Main[185]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[73] + Main[241] * 65535 - Main[187] * 65536 + Main[186]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[74] + Main[241] * 65535 - Main[188] * 65536 + Main[187]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[75] + Main[241] * 65535 - Main[189] * 65536 + Main[188]).val < 65536) ∧
    (¬Main[245] = 0 → (Main[76] + Main[241] * 65535 - Main[190] * 65536 + Main[189]).val < 65536) ∧
    (Main[203] + Main[202] + Main[206] + Main[208] = 0 ∨ Main[41] = Main[29]) ∧
    (Main[205] + Main[204] + Main[207] + Main[209] = 0 ∨ Main[53] = Main[29]) ∧
    (Main[203] + Main[202] + Main[206] + Main[208] = 0 ∨ Main[42] = Main[30]) ∧
    (Main[205] + Main[204] + Main[207] + Main[209] = 0 ∨ Main[54] = Main[30]) ∧
    (Main[203] + Main[202] + Main[206] + Main[208] = 0 ∨ Main[43] = Main[31]) ∧
    (Main[205] + Main[204] + Main[207] + Main[209] = 0 ∨ Main[55] = Main[31]) ∧
    (Main[203] + Main[202] + Main[206] + Main[208] = 0 ∨ Main[44] = Main[32]) ∧
    (Main[205] + Main[204] + Main[207] + Main[209] = 0 ∨ Main[56] = Main[32]) ∧
    (Main[241] = 0 ∨ Main[237] = 1) ∧
    (Main[53] + Main[54] + Main[55] + Main[56] = 0 ∨ Main[241] = 1 ∨ Main[237] = 0) ∧
    (Main[201] = 0 ∨ Main[41] = 65535) ∧
    (Main[201] = 0 ∨ Main[42] = 65535) ∧
    (Main[201] = 0 ∨ Main[43] = 65535) ∧
    (Main[201] = 0 ∨ Main[44] = 65535) ∧
    (Main[201] = 0 ∨ Main[49] = Main[33]) ∧
    (Main[201] = 0 ∨ Main[50] = Main[34]) ∧
    (Main[201] = 0 ∨ Main[51] = Main[35]) ∧
    (Main[201] = 0 ∨ Main[52] = Main[36]) ∧
    (Main[242] = 1 ∨ Main[37] = Main[61]) ∧
    (Main[241] = 1 ∨ Main[49] = Main[57]) ∧
    (Main[242] = 1 ∨ Main[38] = Main[62]) ∧
    (Main[241] = 1 ∨ Main[50] = Main[58]) ∧
    (Main[242] = 1 ∨ Main[39] = Main[63]) ∧
    (Main[241] = 1 ∨ Main[51] = Main[59]) ∧
    (Main[242] = 1 ∨ Main[40] = Main[64]) ∧
    (Main[241] = 1 ∨ Main[52] = Main[60]) ∧
    (¬Main[245] = 0 → Main[61].val < 65536) ∧
    (¬Main[245] = 0 → Main[62].val < 65536) ∧
    (¬Main[245] = 0 → Main[63].val < 65536) ∧
    (¬Main[245] = 0 → Main[64].val < 65536) ∧
    (Main[243] = 0 ∨ Main[167] = 0) ∧
    (Main[243] = 0 ∨ Main[168] = 0) ∧
    (Main[243] = 0 ∨ Main[169] = 0) ∧
    (Main[243] = 0 ∨ Main[170] = 0) ∧
    (¬Main[245] = 0 → Main[57].val < 65536) ∧
    (¬Main[245] = 0 → Main[58].val < 65536) ∧
    (¬Main[245] = 0 → Main[59].val < 65536) ∧
    (¬Main[245] = 0 → Main[60].val < 65536) ∧
    (Main[244] = 0 ∨ Main[171] = 0) ∧
    (Main[244] = 0 ∨ Main[172] = 0) ∧
    (Main[244] = 0 ∨ Main[173] = 0) ∧
    (Main[244] = 0 ∨ Main[174] = 0) ∧
    Main[243] = Main[242] * Main[245] ∧
    Main[244] = Main[241] * Main[245] ∧
    Main[65] = Main[201] + (1 - Main[201]) * Main[61] ∧
    Main[66] = (1 - Main[201]) * Main[62] ∧
    Main[67] = (1 - Main[201]) * Main[63] ∧
    Main[68] = (1 - Main[201]) * Main[64] ∧
    Main[246] = (1 - Main[201]) * Main[245] ∧
    (Main[246] = 0 ∨ Main[175] = 1) ∧
    (¬Main[245] = 0 → Main[41].val < 65536) ∧
    (¬Main[245] = 0 → Main[42].val < 65536) ∧
    (¬Main[245] = 0 → Main[43].val < 65536) ∧
    (¬Main[245] = 0 → Main[44].val < 65536) ∧
    (¬Main[245] = 0 → Main[53].val < 65536) ∧
    (¬Main[245] = 0 → Main[54].val < 65536) ∧
    (¬Main[245] = 0 → Main[55].val < 65536) ∧
    (¬Main[245] = 0 → Main[56].val < 65536) ∧
    (Main[183] = 0 ∨ Main[183] = 1) ∧
    (Main[184] = 0 ∨ Main[184] = 1) ∧
    (Main[185] = 0 ∨ Main[185] = 1) ∧
    (Main[186] = 0 ∨ Main[186] = 1) ∧
    (Main[187] = 0 ∨ Main[187] = 1) ∧
    (Main[188] = 0 ∨ Main[188] = 1) ∧
    (Main[189] = 0 ∨ Main[189] = 1) ∧
    (Main[190] = 0 ∨ Main[190] = 1) ∧
    (¬Main[245] = 0 → Main[69].val < 65536) ∧
    (¬Main[245] = 0 → Main[70].val < 65536) ∧
    (¬Main[245] = 0 → Main[71].val < 65536) ∧
    (¬Main[245] = 0 → Main[72].val < 65536) ∧
    (¬Main[245] = 0 → Main[73].val < 65536) ∧
    (¬Main[245] = 0 → Main[74].val < 65536) ∧
    (¬Main[245] = 0 → Main[75].val < 65536) ∧
    (¬Main[245] = 0 → Main[76].val < 65536) ∧
    (Main[202] = 0 ∨ Main[202] = 1) ∧
    (Main[203] = 0 ∨ Main[203] = 1) ∧
    (Main[204] = 0 ∨ Main[204] = 1) ∧
    (Main[205] = 0 ∨ Main[205] = 1) ∧
    (Main[206] = 0 ∨ Main[206] = 1) ∧
    (Main[207] = 0 ∨ Main[207] = 1) ∧
    (Main[208] = 0 ∨ Main[208] = 1) ∧
    (Main[209] = 0 ∨ Main[209] = 1) ∧
    (Main[210] = 0 ∨ Main[210] = 1) ∧
    (Main[240] = 0 ∨ Main[240] = 1) ∧
    (Main[237] = 0 ∨ Main[237] = 1) ∧
    (Main[238] = 0 ∨ Main[238] = 1) ∧
    (Main[239] = 0 ∨ Main[239] = 1) ∧
    (Main[241] = 0 ∨ Main[241] = 1) ∧
    (Main[242] = 0 ∨ Main[242] = 1) ∧
    (Main[245] = 0 ∨ Main[245] = 1) ∧
    (Main[243] = 0 ∨ Main[243] = 1) ∧
    (Main[244] = 0 ∨ Main[244] = 1) ∧
    Main[203] + Main[205] + Main[202] + Main[204] + Main[206] + Main[207] + Main[208] + Main[209] = 1
  := by
    simp [constraints, sub_eq_zero, and_assoc]
    iterate 3 rw [eq_comm (a := _ * (Main[202] + Main[204] + Main[206] + Main[207]))]
    iterate 3 rw [eq_comm (a := (1 : Fin KB))]
    rw [eq_comm (a := _ * _) (b := Main[246])]
    simp
    repeat (first | (congr! 1; exact neg_eq_zero) | (congr! 1))

set_option maxRecDepth 1000000 in
lemma allHold_constraints_alu_ops :
  List.Forall SP1Constraint.toProp (constraints Main) →
  List.Forall SP1Constraint.toProp
    (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]]
      (Main[203] * 16 + Main[205] * 18 + Main[202] * 15 + Main[204] * 17 + Main[206] * 48 + Main[207] * 50 + Main[208] * 49 + Main[209] * 51)
      #v[Main[203] * 8 + Main[205] * 8 + Main[202] * 8 + Main[204] * 8 + Main[206] * 8 + Main[207] * 8 + Main[208] * 8,
        Main[203] * 51 + Main[205] * 51 + Main[202] * 51 + Main[204] * 51 + Main[206] * 59 + Main[207] * 59 + Main[208] * 59 + Main[209] * 59,
        Main[203] * 5 + Main[205] * 7 + Main[202] * 4 + Main[204] * 6 + Main[206] * 4 + Main[207] * 6 + Main[208] * 5 + Main[209] * 7,
        Main[203] + Main[205] + Main[202] + Main[204] + Main[206] + Main[207] + Main[208] + Main[209]]
      #v[Main[29], Main[30], Main[31], Main[32]]
      { op_a := Main[6],
        op_a_memory :=
          { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
            access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
        op_a_0 := Main[13], op_b := Main[14],
        op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
        op_c := Main[21],
        op_c_memory :=
          { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
            access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } },
        is_trusted := Main[28] }
      Main[245]) ∧
    (Main[202] = 0 ∨ Main[202] = 1) ∧
    (Main[203] = 0 ∨ Main[203] = 1) ∧
    (Main[204] = 0 ∨ Main[204] = 1) ∧
    (Main[205] = 0 ∨ Main[205] = 1) ∧
    (Main[206] = 0 ∨ Main[206] = 1) ∧
    (Main[207] = 0 ∨ Main[207] = 1) ∧
    (Main[208] = 0 ∨ Main[208] = 1) ∧
    (Main[209] = 0 ∨ Main[209] = 1) ∧
    Main[203] + Main[205] + Main[202] + Main[204] + Main[206] + Main[207] + Main[208] + Main[209] = 1
  := by
    intro cstrs; rw [allHold_constraints_iff] at cstrs
    simp_all only [Fin.isValue, Nat.cast_ofNat, Nat.cast_one, and_self, and_true]
    simp_all only [Nat.cast_one, Fin.isValue, mul_eq_zero, not_false_eq_true, implies_true, and_true, true_and]

section field_arithmetic

lemma KB_bool_to_le {x : Fin KB} : x = (0 : Fin KB) ∨ x = (1 : Fin KB) ↔ (0 : Fin KB) ≤ x ∧ x ≤ (1 : Fin KB) := by grind

end field_arithmetic

section opcodes

@[simp] def is_real := Main[245] = 1

@[simp] def is_div := Main[202] = 1
@[simp] def is_divu := Main[203] = 1
@[simp] def is_rem := Main[204] = 1
@[simp] def is_remu := Main[205] = 1
@[simp] def is_divw := Main[206] = 1
@[simp] def is_remw := Main[207] = 1
@[simp] def is_divuw := Main[208] = 1
@[simp] def is_remuw := Main[209] = 1

lemma single_op : List.Forall SP1Constraint.toProp (constraints Main) →
  (Main[202] = 1 → Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[203] = 1 → Main[202] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[204] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[205] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[206] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[207] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[208] = 0 ∧ Main[209] = 0) ∧
  (Main[208] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[209] = 0) ∧
  (Main[209] = 1 → Main[202] = 0 ∧ Main[203] = 0 ∧ Main[204] = 0 ∧ Main[205] = 0 ∧ Main[206] = 0 ∧ Main[207] = 0 ∧ Main[208] = 0)
   := by
  intro cstrs
  have := allHold_constraints_alu_ops Main cstrs
  obtain ⟨ alu, b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw, b_one_of_ops ⟩ := this
  clear alu cstrs
  rw [KB_bool_to_le] at *
  split_ands <;> grind

end opcodes

section entailed_constraints

lemma register_bounds :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Main[6] < 32 ∧ Main[14] < 32 ∧ Main[21] < 32 ∧ Main[3] < 65536
    := by
  intro cstrs is_real
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨ alu, b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw, b_one_of_ops ⟩ := cstrs
  simp_all only [DivRem.is_real, Fin.isValue, Nat.cast_ofNat]
  rw [RTypeReader.allHold_constraints_iff_is_real (by simp)] at alu
  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, rest ⟩ := alu; clear rest
  simp_all
  rcases b_is_div; rcases b_is_divu; rcases b_is_rem; rcases b_is_remu
  rcases b_is_divw; rcases b_is_divuw; rcases b_is_remw; rcases b_is_remuw
  all_goals
    simp_all [Opcode.ofNat, Nat.ble, Nat.beq]

lemma op_a_is_0 :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Main[6] = 0 → Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧ Main[32] = 0 := by
  intro cstrs is_real is_zero
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨ alu, rest ⟩ := cstrs; clear rest; simp_all
  rw [RTypeReader.allHold_constraints_iff_is_real (by simp)] at alu
  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, h9 ⟩ := alu
  simp_all

lemma ops_U64_b_c :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main →
      Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] ∧
      Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] := by
  intro cstrs is_real
  apply allHold_constraints_alu_ops at cstrs
  obtain ⟨ alu, rest ⟩ := cstrs; clear rest; simp_all
  rw [RTypeReader.allHold_constraints_iff_is_real (by simp)] at alu
  obtain ⟨ h0, h1, h2, h3, h4, h5, b_imm, h7, h8 ⟩ := alu
  simp_all

end entailed_constraints

section operands

@[simp]
def sp1_op_a : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[6] ?_
  change Main[6] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_b : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[14] ?_
  change Main[14] < 32
  have := register_bounds Main cstrs real
  tauto

@[simp]
def sp1_op_c : List.Forall SP1Constraint.toProp (constraints Main) → is_real Main → BitVec 5 := by
  intro cstrs real
  refine BitVec.ofNatLT Main[21] ?_
  change Main[21] < 32
  have := register_bounds Main cstrs real

  tauto

end operands

section auxiliaries

lemma div_mod_decomposition_w {a b c : Fin KB} :
  a.val < 65536 → c.val < 2130706433 / 65536 → (a = b - c * 65536 ↔ a = b % 65536 ∧ c = b / 65536) := by
  intro ub_a ub_c
  constructor
  . intro eq_a
    simp [Fin.lt_def, Fin.ext_iff] at *
    have lb_b : c * 65536 ≤ b := by
      by_contra lb_b
      simp [Fin.lt_def, Fin.sub_def, Fin.mul_def] at *
      rw [Nat.mod_eq_of_lt (a := (c : ℕ) * 65536) (by omega)] at eq_a lb_b
      omega
    rw [Fin.sub_val_of_le lb_b] at eq_a
    simp [Fin.mul_def] at eq_a
    rw [Nat.mod_eq_of_lt (by omega)] at eq_a
    omega
  . intro ⟨ eq_a, eq_c ⟩
    simp_all
    symm; rw [sub_eq_iff_eq_add]; symm
    rw [mul_comm, add_comm]
    simp [Fin.ext_iff, Fin.mul_def, Fin.add_def, Fin.mod_def]
    omega

lemma tdiv_tmod_unique_full {b c q r : ℤ} (hcnz : c ≠ 0) :
  q = b.tdiv c ∧ r = b.tmod c ↔
  b = q * c + r ∧
  |r| < |c| ∧
  (r = 0 ∨ r.sign = b.sign) := by
  have hmod1 := @Int.tdiv_tmod_unique b c r q
  have hmod2 := @Int.tdiv_tmod_unique' b c r q
  rw [@eq_comm (a := q), @eq_comm (a := r), @eq_comm (a := b), add_comm, mul_comm]
  repeat rw [Int.natCast_natAbs] at *; repeat rw [Int.abs_cases] at *
  by_cases hb_split : 0 ≤ b
  . simp_all; intro heq; clear hmod1 hmod2
    constructor <;> intro ⟨ h0, h1 ⟩
    . simp_all
      by_cases hr_split : r = 0 <;> [ simp_all; right ]
      rw [Int.sign_eq_one_of_pos (by omega)]
      rw [Int.sign_eq_one_of_pos]
      suffices : ¬ b = 0
      . omega
      . intro bz; simp_all
        apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
        all_goals
          have : c * q > r := by split_ifs at * <;> nlinarith
          omega
    . rcases h1 with rz | h_sign <;> [ omega; skip ]
      split_ifs with hc_split <;> split_ifs at h0 with hr_split <;> simp_all
      all_goals
        rw [Int.sign_eq_neg_one_of_neg (by assumption)] at h_sign
        symm at h_sign; rw [Int.sign_eq_neg_one_iff_neg] at h_sign
        omega
  . rw [hmod2 (by omega) hcnz]; simp_all; intro heq; clear hmod2
    constructor <;> intro ⟨ h0, h1 ⟩
    . constructor
      . by_cases hr_split : r = 0 <;> [ simp_all; skip ]
        rw [if_neg (by omega)]
        omega
      . by_cases hr_split : r = 0 <;> [ simp_all; right ]
        rw [Int.sign_eq_neg_one_of_neg (by omega)]
        rw [Int.sign_eq_neg_one_of_neg hb_split]
    . rcases h1 with rz | h_sign <;> [ omega; skip ]
      rw [Int.sign_eq_neg_one_of_neg hb_split] at h_sign
      rw [Int.sign_eq_neg_one_iff_neg] at h_sign
      rw [if_neg (by omega)] at h0
      omega

lemma tdiv_tmod_unique_full_nat {b c q r : ℕ} (hcnz : c ≠ 0) :
  q = ((b : ℤ).tdiv c).toNat ∧ r = ((b : ℤ).tmod c).toNat ↔
  b = q * c + r ∧ r < c := by
  have hmod := @Int.tdiv_tmod_unique b c r q
  simp_all [Int.tmod_eq_emod]
  rw [@eq_comm (a := q), @eq_comm (a := r), @eq_comm (a := b), add_comm, mul_comm]
  trans (r : ℤ) + c * q = b ∧ r < c
  . rw [← hmod]
    rw [Int.ofNat_ediv_ofNat, ← Int.natCast_emod]
    rw [Int.toNat_natCast, Int.toNat_natCast, Int.natCast_inj, Int.natCast_inj]
  . omega

lemma sum_zero_abs {wx wy : Word (Fin KB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx.isNegative →
    Word.toBitVec64 #v[0, 0, 0, 0] = Word.toBitVec64 wx + Word.toBitVec64 wy →
    (wx.toInt = -2^63 → wy.toInt = -2^63) ∧
    (¬ wx.toInt = -2^63 → wy.toInt = |wx.toInt|) := by
  intro neg_wx sum_zero
  rw [Word.isNegative_toInt is64_wx] at neg_wx
  rw [Int.abs_cases, if_neg (by omega)]
  simp [← BitVec.toInt_inj] at sum_zero
  rw [Word.toBitVec64_toInt is64_wx, Word.toBitVec64_toInt is64_wy] at sum_zero
  simp [Word.toBitVec64, Word.toNat] at sum_zero
  apply Word.isU64_toInt at is64_wx
  apply Word.isU64_toInt at is64_wy
  constructor <;> intro hwx <;> [ (simp [hwx] at *; simp_all); skip ]
  all_goals
    rw [Int.bmod_eq_emod] at sum_zero
    split_ifs at sum_zero with h_bmod <;> omega

lemma extractLsb_is_toInt {x : BitVec 128} (hlb : -9223372036854775808 ≤ x.toInt) (hub : x.toInt < 9223372036854775808) :
  (BitVec.extractLsb 63 0 x).toInt = x.toInt := by
    by_cases case : 0 ≤ x.toInt <;> simp at case
    . simp [BitVec.toInt] at *; split_ifs at * <;> omega
    . trans (BitVec.signExtend 128 (BitVec.extractLsb 63 0 x)).toInt
      . rw [BitVec.toInt_signExtend_of_le (by simp)]
      . rw [BitVec.toInt_inj]
        simp [BitVec.toInt] at *; split_ifs at * <;> [ omega; simp at * ]
        suffices : 340282366920938463454151235394913435648#128 ≤ x
        . bv_decide
        . simp [BitVec.le_def]; omega

end auxiliaries

attribute [-simp] mul_eq_zero not_and

section div_rem

set_option linter.unusedVariables false in
lemma div_rem
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : Fin KB)
  (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
  (sop1 : is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop2 : is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop3 : is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop4 : is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop5 : is_divw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop6 : is_remw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop7 : is_divuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_remuw = 0)
  (sop8 : is_remuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0)
  (eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw)
  (eq_b_neg : b_neg = msb_b * (is_div + is_rem + is_divw + is_remw))
  (eq_rem_neg : rem_neg = msb_rem * (is_div + is_rem + is_divw + is_remw))
  (eq_c_neg : c_neg = msb_c * (is_div + is_rem + is_divw + is_remw))
  (eq_lb0 : lb0 = b0)
  (eq_lc0 : lc0 = c0)
  (eq_lb1 : lb1 = b1)
  (eq_lc1 : lc1 = c1)
  (eq_lb2 : lb2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc2 : lc2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_lb3 : lb3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc3 : lc3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_qbc0 : qbc0 = q0)
  (eq_qbc1 : qbc1 = q1)
  (w_eq_qbc2_uw : is_divuw + is_remuw = 0 ∨ qbc2 = 0)
  (w_eq_qbc2_w : is_divw + is_remw = 0 ∨ qbc2 = msb_quot * 65535)
  (w_eq_q2_w : is_word = 0 ∨ q2 = msb_quot * 65535)
  (eq_qbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc2 = q2)
  (w_eq_qbc3_uw : is_divuw + is_remuw = 0 ∨ qbc3 = 0)
  (w_eq_qbc3_w : is_divw + is_remw = 0 ∨ qbc3 = msb_quot * 65535)
  (w_eq_q3_w : is_word = 0 ∨ q3 = msb_quot * 65535)
  (eq_qbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc3 = q3)
  (eq_rbc0 : rbc0 = r0)
  (eq_rbc1 : rbc1 = r1)
  (w_eq_rbc2_uw : is_divuw + is_remuw = 0 ∨ rbc2 = 0)
  (w_eq_rbc2_w : is_divw + is_remw = 0 ∨ rbc2 = msb_rem * 65535)
  (w_eq_r2_w : is_word = 0 ∨ r2 = msb_rem * 65535)
  (eq_rbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc2 = r2)
  (w_eq_rbc3_uw : is_divuw + is_remuw = 0 ∨ rbc3 = 0)
  (w_eq_rbc3_w : is_divw + is_remw = 0 ∨ rbc3 = msb_rem * 65535)
  (w_eq_r3_w : is_word = 0 ∨ r3 = msb_rem * 65535)
  (eq_rbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc3 = r3)
  (eq_is_overflow : is_overflow = is_overflow_b * is_overflow_c * (is_div + is_rem + is_divw + is_remw))
  (eq_b_neg_not_overflow : b_neg_not_overflow = b_neg * (1 - is_overflow))
  (eq_not_b_neg_not_overflow : b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow))
  (of_eq_q0 : is_overflow = 0 ∨ q0 = b0)
  (of_eq_r0 : is_overflow = 0 ∨ r0 = 0)
  (of_eq_q1 : is_overflow = 0 ∨ q1 = b1)
  (of_eq_r1 : is_overflow = 0 ∨ r1 = 0)
  (of_eq_q2 : is_overflow = 0 ∨ q2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r2 : is_overflow = 0 ∨ r2 = 0)
  (of_eq_q3 : is_overflow = 0 ∨ q3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r3 : is_overflow = 0 ∨ r3 = 0)
  (nof_eq_ctqpr0 : is_overflow = 1 ∨ b0 = ctq0 + r0 - cry0 * 65536)
  (nof_eq_ctqpr1 : is_overflow = 1 ∨ b1 = ctq1 + r1 - cry1 * 65536 + cry0)
  (nof_eq_ctqpr2 : is_overflow = 1 ∨ b2 * (1 - is_word) + b_neg * is_word * 65535 = ctq2 + rbc2 - cry2 * 65536 + cry1)
  (nof_eq_ctqpr3 : is_overflow = 1 ∨ b3 * (1 - is_word) + b_neg * is_word * 65535 = ctq3 + rbc3 - cry3 * 65536 + cry2)
  (nof_eq_ctqpr4 : is_overflow = 1 ∨ ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3 = b_neg * 65535)
  (nof_eq_ctqpr5 : is_overflow = 1 ∨ ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4 = b_neg * 65535)
  (nof_eq_ctqpr6 : is_overflow = 1 ∨ ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5 = b_neg * 65535)
  (nof_eq_ctqpr7 : is_overflow = 1 ∨ ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6 = b_neg * 65535)
  (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
  (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
  (u16_ctqpr2 : (ctq2 + rbc2 - cry2 * 65536 + cry1).val < 65536)
  (u16_ctqpr3 : (ctq3 + rbc3 - cry3 * 65536 + cry2).val < 65536)
  (u16_ctqpr4 : (ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3).val < 65536)
  (u16_ctqpr5 : (ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4).val < 65536)
  (u16_ctqpr6 : (ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5).val < 65536)
  (u16_ctqpr7 : (ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6).val < 65536)
  (eq_d_a0 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a0 = q0)
  (eq_r_a0 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a0 = r0)
  (eq_d_a1 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a1 = q1)
  (eq_r_a1 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a1 = r1)
  (eq_d_a2 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a2 = q2)
  (eq_r_a2 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a2 = r2)
  (eq_d_a3 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a3 = q3)
  (eq_r_a3 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a3 = r3)
  (r_neg_b_neg : rem_neg = 0 ∨ b_neg = 1)
  (r_pos_b_pos : r0 + r1 + r2 + r3 = 0 ∨ rem_neg = 1 ∨ b_neg = 0)
  (c0_eq_q0 : is_c_0 = 0 ∨ q0 = 65535)
  (c0_eq_q1 : is_c_0 = 0 ∨ q1 = 65535)
  (c0_eq_q2 : is_c_0 = 0 ∨ q2 = 65535)
  (c0_eq_q3 : is_c_0 = 0 ∨ q3 = 65535)
  (c0_eq_r0 : is_c_0 = 0 ∨ r0 = b0)
  (c0_eq_r1 : is_c_0 = 0 ∨ r1 = b1)
  (c0_eq_r2 : is_c_0 = 0 ∨ rbc2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (c0_eq_r3 : is_c_0 = 0 ∨ rbc3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (cn_ac0 : c_neg = 1 ∨ ac0 = c0)
  (rn_ar0 : rem_neg = 1 ∨ ar0 = r0)
  (cn_ac1 : c_neg = 1 ∨ ac1 = c1)
  (rn_ar1 : rem_neg = 1 ∨ ar1 = r1)
  (cn_ac2 : c_neg = 1 ∨ ac2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar2 : rem_neg = 1 ∨ ar2 = rbc2)
  (cn_ac3 : c_neg = 1 ∨ ac3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar3 : rem_neg = 1 ∨ ar3 = rbc3)
  (u16_ac0 : ac0.val < 65536)
  (u16_ac1 : ac1.val < 65536)
  (u16_ac2 : ac2.val < 65536)
  (u16_ac3 : ac3.val < 65536)
  (eq_cnop0 : c_neg = 0 ∨ cnop0 = 0)
  (eq_cnop1 : c_neg = 0 ∨ cnop1 = 0)
  (eq_cnop2 : c_neg = 0 ∨ cnop2 = 0)
  (eq_cnop3 : c_neg = 0 ∨ cnop3 = 0)
  (u16_ar0 : ar0.val < 65536)
  (u16_ar1 : ar1.val < 65536)
  (u16_ar2 : ar2.val < 65536)
  (u16_ar3 : ar3.val < 65536)
  (eq_rnop0 : rem_neg = 0 ∨ rnop0 = 0)
  (eq_rnop1 : rem_neg = 0 ∨ rnop1 = 0)
  (eq_rnop2 : rem_neg = 0 ∨ rnop2 = 0)
  (eq_rnop3 : rem_neg = 0 ∨ rnop3 = 0)
  (eq_abs_c_alu_event : abs_c_alu_event = c_neg)
  (eq_abs_rem_alu_event : abs_rem_alu_event = rem_neg)
  (eq_maco10 : maco10 = is_c_0 + (1 - is_c_0) * ac0)
  (eq_maco11 : maco11 = (1 - is_c_0) * ac1)
  (eq_maco12 : maco12 = (1 - is_c_0) * ac2)
  (eq_maco13 : maco13 = (1 - is_c_0) * ac3)
  (eq_arlt : is_c_0 = 1 ∨ arlt = 1)
  (u16_q0 : q0.val < 65536)
  (u16_q1 : q1.val < 65536)
  (u16_q2 : q2.val < 65536)
  (u16_q3 : q3.val < 65536)
  (u16_r0 : r0.val < 65536)
  (u16_r1 : r1.val < 65536)
  (u16_r2 : r2.val < 65536)
  (u16_r3 : r3.val < 65536)
  (b_cry0 : cry0 = 0 ∨ cry0 = 1)
  (b_cry1 : cry1 = 0 ∨ cry1 = 1)
  (b_cry2 : cry2 = 0 ∨ cry2 = 1)
  (b_cry3 : cry3 = 0 ∨ cry3 = 1)
  (b_cry4 : cry4 = 0 ∨ cry4 = 1)
  (b_cry5 : cry5 = 0 ∨ cry5 = 1)
  (b_cry6 : cry6 = 0 ∨ cry6 = 1)
  (b_cry7 : cry7 = 0 ∨ cry7 = 1)
  (u16_ctq0 : ctq0.val < 65536)
  (u16_ctq1 : ctq1.val < 65536)
  (u16_ctq2 : ctq2.val < 65536)
  (u16_ctq3 : ctq3.val < 65536)
  (u16_ctq4 : ctq4.val < 65536)
  (u16_ctq5 : ctq5.val < 65536)
  (u16_ctq6 : ctq6.val < 65536)
  (u16_ctq7 : ctq7.val < 65536)
  (b_is_div : is_div = 0 ∨ is_div = 1)
  (b_is_divu : is_divu = 0 ∨ is_divu = 1)
  (b_is_rem : is_rem = 0 ∨ is_rem = 1)
  (b_is_remu : is_remu = 0 ∨ is_remu = 1)
  (b_is_divw : is_divw = 0 ∨ is_divw = 1)
  (b_is_remw : is_remw = 0 ∨ is_remw = 1)
  (b_is_divuw : is_divuw = 0 ∨ is_divuw = 1)
  (b_is_remuw : is_remuw = 0 ∨ is_remuw = 1)
  (b_is_overflow : is_overflow = 0 ∨ is_overflow = 1)
  (b_is_real_not_word : is_word = 0 ∨ is_word = 1)
  (b_b_neg : b_neg = 0 ∨ b_neg = 1)
  (b_b_neg_not_overflow : b_neg_not_overflow = 0 ∨ b_neg_not_overflow = 1)
  (b_b_not_neg_not_overflow : b_not_neg_not_overflow = 0 ∨ b_not_neg_not_overflow = 1)
  (b_rem_neg : rem_neg = 0 ∨ rem_neg = 1)
  (b_c_neg : c_neg = 0 ∨ c_neg = 1)
  (b_one_of_ops : is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = #v[0, 32768, 0, 0] then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = #v[65535, 65535, 0, 0] then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = #v[0, 0, 0, 0] then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = #v[0, 0, 0, 32768] then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = #v[65535, 65535, 65535, 65535] then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_div + is_rem = 1 →
    ⟨ Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRS
      := by
    intro div_rem
    obtain ⟨ z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw ⟩ : is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0 := by
      clear *- div_rem sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops
      rcases b_is_div <;> rcases b_is_rem <;> simp_all
    simp [z_divu, z_remu, z_divw, z_remw, z_divuw, z_remuw, div_rem] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3
    subst abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, _root_.cond_eq_ite]
    split_ifs at div_zero with nzc <;> simp [div_zero] at *
    . obtain ⟨zc0, zc1, zc2, zc3⟩ := nzc
      simp [zc0, zc1, zc2, zc3] at *
      have : (Word.toBitVec64 #v[0, 0, 0, 0]).toInt = 0 := by simp [Word.toBitVec64, Word.toNat]
      simp [this, c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3]
      simp only [Word.toBitVec64, Word.toNat_def]
      simp [-Fin.coe_ofNat_eq_mod]; rw [Fin.coe_ofNat_eq_mod]
    . simp [eq_arlt] at *
      rw [if_neg]; rotate_left
      . rw [Word.toBitVec64_toInt is_U64_c]
        intro zc; apply Word.toInt_nneg_reconstruct is_U64_c (by rfl) at zc; simp at zc
        apply nzc; exact zc
      . repeat rw [Word.toBitVec64_toInt is_U64_b]
        repeat rw [Word.toBitVec64_toInt is_U64_c]
        rcases b_is_overflow with nof | of; rotate_left
        . simp [of] at *
          split_ifs at overflow_b with ofb <;> simp [overflow_b] at *
          split_ifs at overflow_c with ofc <;> simp [overflow_c] at *
          obtain ⟨eb0, eb1, eb2, eb3⟩ := ofb
          obtain ⟨ec0, ec1, ec2, ec3⟩ := ofc
          simp [of_eq_q0, of_eq_q1, of_eq_q2, of_eq_q3, of_eq_r0, of_eq_r1, of_eq_r2, of_eq_r3]
          simp [eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3]
          simp only [Word.toBitVec64, Word.toInt, Word.isNegative, Word.toNat_def, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
          simp
        . simp [nof] at *
          rw [if_neg]; rotate_left
          . intro ⟨ h_eq_b, h_eq_c ⟩
            have : (#v[b0, b1, b2, b3] : Word (Fin KB)) = #v[0, 0, 0, 32768] := by
              rw [Word.eq_toInt_eq is_U64_b, h_eq_b]
              simp [Word.toInt, Word.isNegative, Word.toNat]
              apply Word.isU64_of_cases <;> simp
            simp at this; rw [if_pos (by exact this)] at overflow_b; simp [overflow_b] at *; clear this
            have : (#v[c0, c1, c2, c3] : Word (Fin KB)) = #v[65535, 65535, 65535, 65535] := by
              rw [Word.eq_toInt_eq is_U64_c, h_eq_c]
              simp [Word.toInt, Word.isNegative, Word.toNat]
              apply Word.isU64_of_cases <;> simp
            simp at this; rw [if_pos (by exact this)] at overflow_c; simp [overflow_c] at *
          . have is_U64_r : Word.isU64 #v[r0, r1, r2, r3] := by apply Word.isU64_of_cases <;> simpa
            have is_U64_q : Word.isU64 #v[q0, q1, q2, q3] := by apply Word.isU64_of_cases <;> simpa
            suffices :
              Word.toInt #v[q0, q1, q2, q3] = (Word.toInt #v[b0, b1, b2, b3]).tdiv (Word.toInt #v[c0, c1, c2, c3]) ∧
              Word.toInt #v[r0, r1, r2, r3] = (Word.toInt #v[b0, b1, b2, b3]).tmod (Word.toInt #v[c0, c1, c2, c3])
            . obtain ⟨ hdiv, hrem ⟩ := this
              rw [← hdiv, ← hrem]
              simp [← BitVec.toInt_inj]
              rw [Word.toBitVec64_toInt is_U64_q, Word.toBitVec64_toInt is_U64_r]
              rw [Int.bmod_eq_of_le (Word.toInt_lb is_U64_q) (Word.toInt_ub is_U64_q), Int.bmod_eq_of_le (Word.toInt_lb is_U64_r) (Word.toInt_ub is_U64_r)]
              trivial
            . have is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3] := by apply Word.isU64_of_cases <;> simpa
              have is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3] := by apply Word.isU64_of_cases <;> simpa
              have sgn_msb_b : msb_b = 1 → (Word.toInt #v[b0, b1, b2, b3]).sign = -1 := by
                intro h_msb_b; rw [Word.sign_cases is_U64_b]; simp [h_msb_b] at *
                intro hneg; simp [Word.isNegative] at hneg
                omega
              have sgn_msb_c : msb_c = 1 → (Word.toInt #v[c0, c1, c2, c3]).sign = -1 := by
                intro h_msb_c; rw [Word.sign_cases is_U64_c]; simp [h_msb_c] at *
                intro hneg; simp [Word.isNegative] at hneg
                omega
              have sgn_msb_rem : msb_rem = 1 → (Word.toInt #v[r0, r1, r2, r3]).sign = -1 := by
                intro h_msb_b; rw [Word.sign_cases is_U64_r]; simp [h_msb_b] at *
                intro hneg; simp [Word.isNegative] at hneg
                omega
              have cnz : Word.toInt #v[c0, c1, c2, c3] ≠ 0 := by
                intro zc; apply Word.toInt_nneg_reconstruct is_U64_c (by simp) at zc
                simp at zc; apply nzc; exact zc

              -- First condition
              have h_prod : Word.toInt #v[b0, b1, b2, b3] = Word.toInt #v[q0, q1, q2, q3] * Word.toInt #v[c0, c1, c2, c3] + Word.toInt #v[r0, r1, r2, r3] := by
                clear *- is_U64_b is_U64_c is_U64_q is_U64_r
                        u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                        b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
                        eq_msb_b eq_msb_c eq_msb_rem r_neg_b_neg r_pos_b_pos
                        nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                        main_mul_low main_mul_high
                obtain ⟨ is_U64_ctql, ctq_low ⟩ := main_mul_low
                obtain ⟨ is_U64_ctqh, ctq_high ⟩ := main_mul_high
                have ctq := combine_MUL_MULH is_U64_ctql is_U64_ctqh is_U64_q is_U64_c ctq_low ctq_high
                simp at ctq
                have eq_eb : (#v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535, msb_b * 65535, msb_b * 65535] : DWord (Fin KB)) = Word.extend #v[b0, b1, b2, b3] true := by
                  clear *- is_U64_b eq_msb_b
                  simp [Word.extend, Word.isNegative]
                  aesop
                have eq_er : (#v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535] : DWord (Fin KB)) = Word.extend #v[r0, r1, r2, r3] true := by
                  clear *- is_U64_r eq_msb_rem
                  simp [Word.extend, Word.isNegative]
                  aesop
                suffices bv_ctqr:
                  DWord.toBitVec128 #v[b0, b1, b2, b3, msb_b * 65535, msb_b * 65535, msb_b * 65535, msb_b * 65535] =
                    DWord.toBitVec128 #v[ctq0, ctq1, ctq2, ctq3, ctq4, ctq5, ctq6, ctq7] +
                    DWord.toBitVec128 #v[r0, r1, r2, r3, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535, msb_rem * 65535]
                . rw [eq_eb, eq_er] at bv_ctqr
                  rw [ctq] at bv_ctqr
                  repeat rw [Word.extend_true_is_signExtend (by assumption)] at bv_ctqr
                  simp [← BitVec.toInt_inj] at bv_ctqr
                  repeat rw [BitVec.toInt_signExtend_of_le (by simp)] at bv_ctqr
                  repeat rw [Word.toBitVec64_toInt (by assumption)] at bv_ctqr
                  have lbq := Word.toInt_lb is_U64_q
                  have ubq := Word.toInt_ub is_U64_q
                  have lbr := Word.toInt_lb is_U64_r
                  have ubr := Word.toInt_ub is_U64_r
                  have lbc := Word.toInt_lb is_U64_c
                  have ubc := Word.toInt_ub is_U64_c
                  rw [bv_ctqr]
                  apply Int.bmod_eq_of_le <;> simp <;> nlinarith
                . have is_U16_msb_b : (msb_b * 65535).val < 65536 := by clear *- eq_msb_b; split_ifs at eq_msb_b <;> simp_all
                  have is_U16_msb_rem : (msb_rem * 65535).val < 65536 := by clear *- eq_msb_rem; split_ifs at eq_msb_rem <;> simp_all
                  clear is_U64_c eq_msb_b eq_msb_c eq_msb_rem ctq_low ctq_high ctq eq_is_word r_neg_b_neg r_pos_b_pos eq_eb eq_er
                  apply Word.lt_cases_of_isU64 at is_U64_b
                  apply Word.lt_cases_of_isU64 at is_U64_r
                  apply Word.lt_cases_of_isU64 at is_U64_q
                  apply Word.lt_cases_of_isU64 at is_U64_ctql
                  apply Word.lt_cases_of_isU64 at is_U64_ctqh
                  simp at *
                  rw [eq_comm] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                  rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                                               nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                  rw [div_mod_decomposition_w (by omega) (by omega)] at nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                  conv =>
                    lhs; simp [DWord.toBitVec128, DWord.toNat]
                    simp [nof_eq_ctqpr0.1, nof_eq_ctqpr1.1, nof_eq_ctqpr2.1, nof_eq_ctqpr3.1, nof_eq_ctqpr3.2]
                    conv => arg 2; arg 2; simp [nof_eq_ctqpr7.1]
                    conv => arg 2; arg 1; arg 2; simp [nof_eq_ctqpr6.1]
                    conv => arg 2; arg 1; arg 1; arg 2; simp [nof_eq_ctqpr5.1]
                    conv => arg 2; arg 1; arg 1; arg 1; arg 2; simp [nof_eq_ctqpr4.1]
                    simp [nof_eq_ctqpr0.2, nof_eq_ctqpr1.2, nof_eq_ctqpr2.2, nof_eq_ctqpr3.2, nof_eq_ctqpr4.2, nof_eq_ctqpr5.2, nof_eq_ctqpr6.2, nof_eq_ctqpr7.2]

                  simp [Fin.val_add]
                  iterate 8 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
                  have joins : forall (i : Fin 8) (a b : ℕ), a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) = (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
                    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
                  have divs : forall (i : Fin 8) (a b : ℕ), (a + b / (65536 ^ i.val)) / 65536 = (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
                    clear *-; intro i a b; fin_cases i <;> norm_num <;> omega

                  have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
                  have j4 := joins 4; have j5 := joins 5; have j6 := joins 6; have j7 := joins 7
                  have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
                  have d4 := divs 4; have d5 := divs 5; have d6 := divs 6; have d7 := divs 7
                  simp at *

                  rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7]
                  clear j1 j2 j3 j4 j5 j6 j7 d1 d2 d3 d4 d5 d6 d7 joins divs

                  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
                  repeat rw [BitVec.toNat_add]
                  iterate 2 rw [DWord.toBitVec128_toNat (by apply DWord.isU128_of_cases <;> simp <;> omega)]
                  simp [DWord.toNat]; ring_nf

              -- Second condition
              have h_abs : |Word.toInt #v[r0, r1, r2, r3]| < |Word.toInt #v[c0, c1, c2, c3]| := by
                clear *- is_U64_c is_U64_r is_U64_ac is_U64_ar b_c_neg b_rem_neg eq_msb_c eq_msb_rem
                        rem_neg_sum_zero c_neg_sum_zero sgn_msb_c sgn_msb_rem abs_check cnz
                        rn_ar0 rn_ar1 rn_ar2 rn_ar3 cn_ac0 cn_ac1 cn_ac2 cn_ac3
                        eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3
                have h_eq_nmax : - 2^63 = Word.toInt #v[0, 0, 0, 32768] := by simp [Word.toInt, Word.isNegative, Word.toNat]
                rcases b_rem_neg with rem_nneg | rem_neg <;> rcases b_c_neg with c_nneg | c_neg
                . simp [rem_nneg, c_nneg] at *; simp_all
                  simp [Word.toInt, Word.isNegative]
                  iterate 2 rw [if_neg (by omega)]
                  simpa
                . simp [rem_nneg, c_neg] at *; simp_all
                  obtain ⟨ _, heqz ⟩ := c_neg_sum_zero
                  apply sum_zero_abs is_U64_c is_U64_ac (by rw [Word.isNegative_toInt is_U64_c]; assumption) at heqz
                  obtain ⟨ hc_lb, hc_nlb ⟩ := heqz
                  by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = -2 ^ 63
                  . rw [is_c_lb]; simp
                    simp [Word.toInt, Word.isNegative, Word.toNat]
                    rw [abs_of_nonneg (by omega)]
                    apply Word.lt_cases_of_isU64 at is_U64_r
                    simp at is_U64_r; omega
                  . apply hc_nlb at is_c_lb
                    have is_c_lb' := is_c_lb
                    rw [Word.toInt] at is_c_lb; rw [if_neg] at is_c_lb; rw [← is_c_lb]
                    rw [Word.toInt]; rw [if_neg (by simpa [Word.isNegative])]; simpa
                    rw [Word.isNegative_toInt is_U64_ac, is_c_lb']
                    simp
                . simp [rem_neg, c_nneg] at *; simp_all
                  obtain ⟨ _, heqz_rem ⟩ := rem_neg_sum_zero
                  apply sum_zero_abs is_U64_r is_U64_ar (by rw [Word.isNegative_toInt is_U64_r]; assumption) at heqz_rem
                  simp [h_eq_nmax] at heqz_rem
                  by_cases is_rem_lb : Word.toInt #v[r0, r1, r2, r3] = Word.toInt #v[0, 0, 0, 32768] <;> simp_all
                  . rw [← Word.eq_toInt_eq (by assumption) (by apply Word.isU64_of_cases <;> simp)] at heqz_rem
                    simp_all
                    simp [Word.toNat] at abs_check
                    apply Word.lt_cases_of_isU64 at is_U64_c
                    simp_all; omega
                  . rw [← h_eq_nmax] at is_rem_lb
                    rw [← heqz_rem]
                    simp [Word.toInt]
                    rw [if_neg, if_neg]
                    . simpa
                    . unfold Word.isNegative; simp; omega
                    . simp [Word.isNegative_toInt is_U64_ar]
                      rw [heqz_rem]; simp
                . simp [rem_neg, c_neg] at *; subst rnop0 rnop1 rnop2 rnop3 cnop0 cnop1 cnop2 cnop3
                  obtain ⟨ _, heqz_c ⟩ := c_neg_sum_zero
                  obtain ⟨ _, heqz_rem ⟩ := rem_neg_sum_zero
                  apply sum_zero_abs is_U64_c is_U64_ac (by rw [Word.isNegative_toInt is_U64_c]; assumption) at heqz_c
                  apply sum_zero_abs is_U64_r is_U64_ar (by rw [Word.isNegative_toInt is_U64_r]; assumption) at heqz_rem
                  simp [h_eq_nmax] at heqz_c heqz_rem
                  by_cases is_rem_lb : Word.toInt #v[r0, r1, r2, r3] = Word.toInt #v[0, 0, 0, 32768] <;>
                  by_cases is_c_lb : Word.toInt #v[c0, c1, c2, c3] = Word.toInt #v[0, 0, 0, 32768] <;>
                  simp_all
                  . rw [← Word.eq_toInt_eq (by assumption) (by apply Word.isU64_of_cases <;> simp)] at heqz_c
                    rw [← Word.eq_toInt_eq (by assumption) (by apply Word.isU64_of_cases <;> simp)] at heqz_rem
                    simp_all
                  . rw [← Word.eq_toInt_eq (by assumption) (by apply Word.isU64_of_cases <;> simp)] at heqz_rem
                    simp_all
                    rw [Word.toNat] at abs_check; simp at abs_check
                    have ac_neg : 32768 ≤ ac3 := by clear *- abs_check is_U64_ac; apply Word.lt_cases_of_isU64 at is_U64_ac; simp [Word.toNat] at *; omega
                    have ac_neg' : Word.toInt #v[ac0, ac1, ac2, ac3] < 0 := by rw [← Word.isNegative_toInt is_U64_ac]; simpa [Word.isNegative]
                    have := abs_nonneg (Word.toInt #v[c0, c1, c2, c3])
                    omega
                  . rw [← Word.eq_toInt_eq (by assumption) (by apply Word.isU64_of_cases <;> simp)] at heqz_c
                    simp [← h_eq_nmax] at is_rem_lb ⊢
                    rw [Int.abs_cases, if_neg (by omega)]
                    have := Word.isU64_toInt is_U64_r
                    omega
                  . rw [← heqz_c, ← heqz_rem]; simp [Word.toInt]
                    iterate 2 rw [if_neg]
                    . omega
                    . simp_all [Word.isNegative_toInt is_U64_ac]
                    . simp_all [Word.isNegative_toInt is_U64_ar]

              -- Third condition
              have h_sign : (Word.toInt #v[r0, r1, r2, r3] = 0 ∨ (Word.toInt #v[r0, r1, r2, r3]).sign = (Word.toInt #v[b0, b1, b2, b3]).sign) := by
                rcases b_b_neg with b_msb_nneg | b_msb_neg
                . simp [b_msb_nneg] at *
                  simp [r_neg_b_neg] at *
                  by_cases rz : Word.toInt #v[r0, r1, r2, r3] = 0 <;> [ simp_all; right ]
                  rw [Word.sign_cases is_U64_b, Word.sign_cases is_U64_r]
                  simp [Word.isNegative]
                  split_ifs with hr hb hw hb hw <;> try omega
                  have rpos : Word.toInt #v[r0, r1, r2, r3] > 0 := by simp [Word.toInt, Word.isNegative, Word.toNat] at rz ⊢; split_ifs; omega
                  rw [h_prod] at hw; simp
                  set q := Word.toInt #v[q0, q1, q2, q3]
                  set c := Word.toInt #v[c0, c1, c2, c3]
                  set r := Word.toInt #v[r0, r1, r2, r3]
                  clear *- rpos h_abs hw
                  simp [Int.abs_cases] at h_abs; rw [if_pos (by omega)] at h_abs
                  apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
                  all_goals
                    have : c * q > r := by split_ifs at * <;> nlinarith
                    nlinarith
                . simp [b_msb_neg] at *
                  simp [Int.sign_eq_neg_one_of_neg sgn_msb_b]
                  clear *- u16_r0 u16_r1 u16_r2 u16_r3 r_pos_b_pos sgn_msb_rem
                  rcases r_pos_b_pos with hrz | hmsb <;> [ left; simp_all ]
                  simp [Word.toInt, Word.isNegative, Word.toNat]
                  omega

              rw [tdiv_tmod_unique_full cnz]
              split_ands <;> assumption

set_option maxRecDepth 1000000 in
lemma spec.div :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_div Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRS).1
  := by
  intro cstrs h_is_real h_is_div
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_div] at h_is_div

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4

  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_div]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := div_rem a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop1 h_is_div
    simp [h_is_div, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c

set_option maxRecDepth 1000000 in
lemma spec.rem :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_rem Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRS).2
  := by
  intro cstrs h_is_real h_is_rem
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_rem] at h_is_rem

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_rem]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := div_rem a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop3 h_is_rem
    simp [h_is_rem, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c

end div_rem

section divu_remu

set_option linter.unusedVariables false in
lemma divu_remu
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : Fin KB)
  (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
  (sop1 : is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop2 : is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop3 : is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop4 : is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop5 : is_divw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop6 : is_remw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop7 : is_divuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_remuw = 0)
  (sop8 : is_remuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0)
  (eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw)
  (eq_b_neg : b_neg = msb_b * (is_div + is_rem + is_divw + is_remw))
  (eq_rem_neg : rem_neg = msb_rem * (is_div + is_rem + is_divw + is_remw))
  (eq_c_neg : c_neg = msb_c * (is_div + is_rem + is_divw + is_remw))
  (eq_lb0 : lb0 = b0)
  (eq_lc0 : lc0 = c0)
  (eq_lb1 : lb1 = b1)
  (eq_lc1 : lc1 = c1)
  (eq_lb2 : lb2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc2 : lc2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_lb3 : lb3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc3 : lc3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_qbc0 : qbc0 = q0)
  (eq_qbc1 : qbc1 = q1)
  (w_eq_qbc2_uw : is_divuw + is_remuw = 0 ∨ qbc2 = 0)
  (w_eq_qbc2_w : is_divw + is_remw = 0 ∨ qbc2 = msb_quot * 65535)
  (w_eq_q2_w : is_word = 0 ∨ q2 = msb_quot * 65535)
  (eq_qbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc2 = q2)
  (w_eq_qbc3_uw : is_divuw + is_remuw = 0 ∨ qbc3 = 0)
  (w_eq_qbc3_w : is_divw + is_remw = 0 ∨ qbc3 = msb_quot * 65535)
  (w_eq_q3_w : is_word = 0 ∨ q3 = msb_quot * 65535)
  (eq_qbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc3 = q3)
  (eq_rbc0 : rbc0 = r0)
  (eq_rbc1 : rbc1 = r1)
  (w_eq_rbc2_uw : is_divuw + is_remuw = 0 ∨ rbc2 = 0)
  (w_eq_rbc2_w : is_divw + is_remw = 0 ∨ rbc2 = msb_rem * 65535)
  (w_eq_r2_w : is_word = 0 ∨ r2 = msb_rem * 65535)
  (eq_rbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc2 = r2)
  (w_eq_rbc3_uw : is_divuw + is_remuw = 0 ∨ rbc3 = 0)
  (w_eq_rbc3_w : is_divw + is_remw = 0 ∨ rbc3 = msb_rem * 65535)
  (w_eq_r3_w : is_word = 0 ∨ r3 = msb_rem * 65535)
  (eq_rbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc3 = r3)
  (eq_is_overflow : is_overflow = is_overflow_b * is_overflow_c * (is_div + is_rem + is_divw + is_remw))
  (eq_b_neg_not_overflow : b_neg_not_overflow = b_neg * (1 - is_overflow))
  (eq_not_b_neg_not_overflow : b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow))
  (of_eq_q0 : is_overflow = 0 ∨ q0 = b0)
  (of_eq_r0 : is_overflow = 0 ∨ r0 = 0)
  (of_eq_q1 : is_overflow = 0 ∨ q1 = b1)
  (of_eq_r1 : is_overflow = 0 ∨ r1 = 0)
  (of_eq_q2 : is_overflow = 0 ∨ q2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r2 : is_overflow = 0 ∨ r2 = 0)
  (of_eq_q3 : is_overflow = 0 ∨ q3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r3 : is_overflow = 0 ∨ r3 = 0)
  (nof_eq_ctqpr0 : is_overflow = 1 ∨ b0 = ctq0 + r0 - cry0 * 65536)
  (nof_eq_ctqpr1 : is_overflow = 1 ∨ b1 = ctq1 + r1 - cry1 * 65536 + cry0)
  (nof_eq_ctqpr2 : is_overflow = 1 ∨ b2 * (1 - is_word) + b_neg * is_word * 65535 = ctq2 + rbc2 - cry2 * 65536 + cry1)
  (nof_eq_ctqpr3 : is_overflow = 1 ∨ b3 * (1 - is_word) + b_neg * is_word * 65535 = ctq3 + rbc3 - cry3 * 65536 + cry2)
  (nof_eq_ctqpr4 : is_overflow = 1 ∨ ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3 = b_neg * 65535)
  (nof_eq_ctqpr5 : is_overflow = 1 ∨ ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4 = b_neg * 65535)
  (nof_eq_ctqpr6 : is_overflow = 1 ∨ ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5 = b_neg * 65535)
  (nof_eq_ctqpr7 : is_overflow = 1 ∨ ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6 = b_neg * 65535)
  (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
  (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
  (u16_ctqpr2 : (ctq2 + rbc2 - cry2 * 65536 + cry1).val < 65536)
  (u16_ctqpr3 : (ctq3 + rbc3 - cry3 * 65536 + cry2).val < 65536)
  (u16_ctqpr4 : (ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3).val < 65536)
  (u16_ctqpr5 : (ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4).val < 65536)
  (u16_ctqpr6 : (ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5).val < 65536)
  (u16_ctqpr7 : (ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6).val < 65536)
  (eq_d_a0 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a0 = q0)
  (eq_r_a0 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a0 = r0)
  (eq_d_a1 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a1 = q1)
  (eq_r_a1 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a1 = r1)
  (eq_d_a2 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a2 = q2)
  (eq_r_a2 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a2 = r2)
  (eq_d_a3 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a3 = q3)
  (eq_r_a3 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a3 = r3)
  (r_neg_b_neg : rem_neg = 0 ∨ b_neg = 1)
  (r_pos_b_pos : r0 + r1 + r2 + r3 = 0 ∨ rem_neg = 1 ∨ b_neg = 0)
  (c0_eq_q0 : is_c_0 = 0 ∨ q0 = 65535)
  (c0_eq_q1 : is_c_0 = 0 ∨ q1 = 65535)
  (c0_eq_q2 : is_c_0 = 0 ∨ q2 = 65535)
  (c0_eq_q3 : is_c_0 = 0 ∨ q3 = 65535)
  (c0_eq_r0 : is_c_0 = 0 ∨ r0 = b0)
  (c0_eq_r1 : is_c_0 = 0 ∨ r1 = b1)
  (c0_eq_r2 : is_c_0 = 0 ∨ rbc2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (c0_eq_r3 : is_c_0 = 0 ∨ rbc3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (cn_ac0 : c_neg = 1 ∨ ac0 = c0)
  (rn_ar0 : rem_neg = 1 ∨ ar0 = r0)
  (cn_ac1 : c_neg = 1 ∨ ac1 = c1)
  (rn_ar1 : rem_neg = 1 ∨ ar1 = r1)
  (cn_ac2 : c_neg = 1 ∨ ac2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar2 : rem_neg = 1 ∨ ar2 = rbc2)
  (cn_ac3 : c_neg = 1 ∨ ac3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar3 : rem_neg = 1 ∨ ar3 = rbc3)
  (u16_ac0 : ac0.val < 65536)
  (u16_ac1 : ac1.val < 65536)
  (u16_ac2 : ac2.val < 65536)
  (u16_ac3 : ac3.val < 65536)
  (eq_cnop0 : c_neg = 0 ∨ cnop0 = 0)
  (eq_cnop1 : c_neg = 0 ∨ cnop1 = 0)
  (eq_cnop2 : c_neg = 0 ∨ cnop2 = 0)
  (eq_cnop3 : c_neg = 0 ∨ cnop3 = 0)
  (u16_ar0 : ar0.val < 65536)
  (u16_ar1 : ar1.val < 65536)
  (u16_ar2 : ar2.val < 65536)
  (u16_ar3 : ar3.val < 65536)
  (eq_rnop0 : rem_neg = 0 ∨ rnop0 = 0)
  (eq_rnop1 : rem_neg = 0 ∨ rnop1 = 0)
  (eq_rnop2 : rem_neg = 0 ∨ rnop2 = 0)
  (eq_rnop3 : rem_neg = 0 ∨ rnop3 = 0)
  (eq_abs_c_alu_event : abs_c_alu_event = c_neg)
  (eq_abs_rem_alu_event : abs_rem_alu_event = rem_neg)
  (eq_maco10 : maco10 = is_c_0 + (1 - is_c_0) * ac0)
  (eq_maco11 : maco11 = (1 - is_c_0) * ac1)
  (eq_maco12 : maco12 = (1 - is_c_0) * ac2)
  (eq_maco13 : maco13 = (1 - is_c_0) * ac3)
  (eq_arlt : is_c_0 = 1 ∨ arlt = 1)
  (u16_q0 : q0.val < 65536)
  (u16_q1 : q1.val < 65536)
  (u16_q2 : q2.val < 65536)
  (u16_q3 : q3.val < 65536)
  (u16_r0 : r0.val < 65536)
  (u16_r1 : r1.val < 65536)
  (u16_r2 : r2.val < 65536)
  (u16_r3 : r3.val < 65536)
  (b_cry0 : cry0 = 0 ∨ cry0 = 1)
  (b_cry1 : cry1 = 0 ∨ cry1 = 1)
  (b_cry2 : cry2 = 0 ∨ cry2 = 1)
  (b_cry3 : cry3 = 0 ∨ cry3 = 1)
  (b_cry4 : cry4 = 0 ∨ cry4 = 1)
  (b_cry5 : cry5 = 0 ∨ cry5 = 1)
  (b_cry6 : cry6 = 0 ∨ cry6 = 1)
  (b_cry7 : cry7 = 0 ∨ cry7 = 1)
  (u16_ctq0 : ctq0.val < 65536)
  (u16_ctq1 : ctq1.val < 65536)
  (u16_ctq2 : ctq2.val < 65536)
  (u16_ctq3 : ctq3.val < 65536)
  (u16_ctq4 : ctq4.val < 65536)
  (u16_ctq5 : ctq5.val < 65536)
  (u16_ctq6 : ctq6.val < 65536)
  (u16_ctq7 : ctq7.val < 65536)
  (b_is_div : is_div = 0 ∨ is_div = 1)
  (b_is_divu : is_divu = 0 ∨ is_divu = 1)
  (b_is_rem : is_rem = 0 ∨ is_rem = 1)
  (b_is_remu : is_remu = 0 ∨ is_remu = 1)
  (b_is_divw : is_divw = 0 ∨ is_divw = 1)
  (b_is_remw : is_remw = 0 ∨ is_remw = 1)
  (b_is_divuw : is_divuw = 0 ∨ is_divuw = 1)
  (b_is_remuw : is_remuw = 0 ∨ is_remuw = 1)
  (b_is_overflow : is_overflow = 0 ∨ is_overflow = 1)
  (b_is_real_not_word : is_word = 0 ∨ is_word = 1)
  (b_b_neg : b_neg = 0 ∨ b_neg = 1)
  (b_b_neg_not_overflow : b_neg_not_overflow = 0 ∨ b_neg_not_overflow = 1)
  (b_b_not_neg_not_overflow : b_not_neg_not_overflow = 0 ∨ b_not_neg_not_overflow = 1)
  (b_rem_neg : rem_neg = 0 ∨ rem_neg = 1)
  (b_c_neg : c_neg = 0 ∨ c_neg = 1)
  (b_one_of_ops : is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = #v[0, 32768, 0, 0] then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = #v[65535, 65535, 0, 0] then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = #v[0, 0, 0, 0] then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = #v[0, 0, 0, 32768] then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = #v[65535, 65535, 65535, 65535] then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_divu + is_remu = 1 →
    ⟨ Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRU
      := by
    intro divu_remu
    obtain ⟨ z_div, z_rem, z_divw, z_remw, z_divuw, z_remuw ⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0 := by
      clear *- divu_remu sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops
      rcases b_is_divu <;> rcases b_is_remu <;> simp_all
    simp [z_div, z_rem, z_divw, z_remw, z_divuw, z_remuw, divu_remu] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    simp [eq_is_overflow] at *
    subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 b_neg_not_overflow b_not_neg_not_overflow
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite]
    split_ifs at div_zero with nzc <;> simp [div_zero] at *
    . obtain ⟨zc0, zc1, zc2, zc3⟩ := nzc
      subst c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3
      simp [Word.toBitVec64_toNat is_U64_b]
      simp [Word.toBitVec64, Word.toNat]
      rfl
    . subst arlt maco10 maco11 maco12 maco13 is_c_0; simp at *
      rw [if_neg]; rotate_left
      . rw [Word.toBitVec64_toNat is_U64_c]
        intro zc; apply Word.toNat_reconstruct is_U64_c at zc
        aesop
      . repeat rw [Word.toBitVec64_toNat is_U64_b]
        repeat rw [Word.toBitVec64_toNat is_U64_c]
        have is_U64_r : Word.isU64 #v[r0, r1, r2, r3] := by apply Word.isU64_of_cases <;> simpa
        have is_U64_q : Word.isU64 #v[q0, q1, q2, q3] := by apply Word.isU64_of_cases <;> simpa
        suffices :
          Word.toNat #v[q0, q1, q2, q3] = (((Word.toNat #v[b0, b1, b2, b3]) : ℤ).tdiv (Word.toNat #v[c0, c1, c2, c3])).toNat ∧
          Word.toNat #v[r0, r1, r2, r3] = (((Word.toNat #v[b0, b1, b2, b3]) : ℤ).tmod (Word.toNat #v[c0, c1, c2, c3])).toNat
        . obtain ⟨ hdiv, hrem ⟩ := this
          simp at hdiv; rw [← hdiv, ← hrem]
          simp [← BitVec.toNat_inj]
          rw [Word.toBitVec64_toNat is_U64_q, Word.toBitVec64_toNat is_U64_r]
          rw [Nat.mod_eq_of_lt (by apply Word.toNat_lt_of_isU64 is_U64_q)]
          rw [Nat.mod_eq_of_lt (by apply Word.toNat_lt_of_isU64 is_U64_r)]
          trivial
        . have cnz : Word.toNat #v[c0, c1, c2, c3] ≠ 0 := by
            intro zc; apply Word.toNat_reconstruct is_U64_c at zc
            simp at zc; apply nzc; exact zc
          rw [tdiv_tmod_unique_full_nat cnz]
          split_ands <;> [ skip; assumption ]
          clear *- is_U64_b is_U64_c is_U64_q is_U64_r
                  u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                  b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
                  eq_msb_b eq_msb_c eq_msb_rem r_neg_b_neg r_pos_b_pos
                  nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                  main_mul_low main_mul_high
          obtain ⟨ is_U64_ctql, ctq_low ⟩ := main_mul_low
          obtain ⟨ is_U64_ctqh, ctq_high ⟩ := main_mul_high
          have ctq := combine_MUL_MULHU is_U64_ctql is_U64_ctqh is_U64_q is_U64_c ctq_low ctq_high
          simp at ctq
          have eq_eb : (#v[b0, b1, b2, b3, 0, 0, 0, 0] : DWord (Fin KB)) = Word.extend #v[b0, b1, b2, b3] false := by simp [Word.extend]
          have eq_er : (#v[r0, r1, r2, r3, 0, 0, 0, 0] : DWord (Fin KB)) = Word.extend #v[r0, r1, r2, r3] false := by simp [Word.extend]
          suffices bv_ctqr:
            DWord.toBitVec128 #v[b0, b1, b2, b3, 0, 0, 0, 0] =
              DWord.toBitVec128 #v[ctq0, ctq1, ctq2, ctq3, ctq4, ctq5, ctq6, ctq7] +
              DWord.toBitVec128 #v[r0, r1, r2, r3, 0, 0, 0, 0]
          . have := Word.toNat_lt_of_isU64 is_U64_b
            have := Word.toNat_lt_of_isU64 is_U64_q
            have := Word.toNat_lt_of_isU64 is_U64_c
            have := Word.toNat_lt_of_isU64 is_U64_r
            rw [eq_eb, eq_er] at bv_ctqr
            rw [ctq] at bv_ctqr
            repeat rw [Word.extend_false_is_setWidth (by assumption)] at bv_ctqr
            rw [← BitVec.toNat_inj, BitVec.toNat_setWidth] at bv_ctqr
            rw [Word.toBitVec64_toNat (by assumption), Nat.mod_eq_of_lt (by omega)] at bv_ctqr
            rw [bv_ctqr, BitVec.toNat_add, BitVec.toNat_mul]
            simp; repeat rw [Word.toBitVec64_toNat (by assumption)]
            apply Nat.mod_eq_of_lt (by nlinarith)
          . clear is_U64_c eq_msb_b eq_msb_c eq_msb_rem ctq_low ctq_high ctq eq_is_word r_neg_b_neg r_pos_b_pos eq_eb eq_er
            apply Word.lt_cases_of_isU64 at is_U64_b
            apply Word.lt_cases_of_isU64 at is_U64_r
            apply Word.lt_cases_of_isU64 at is_U64_q
            apply Word.lt_cases_of_isU64 at is_U64_ctql
            apply Word.lt_cases_of_isU64 at is_U64_ctqh
            simp at *
            rw [eq_comm] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
            rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                                          nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
            rw [div_mod_decomposition_w (by omega) (by omega)] at nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
            conv =>
              lhs; simp [DWord.toBitVec128, DWord.toNat]
              simp [nof_eq_ctqpr0.1, nof_eq_ctqpr1.1, nof_eq_ctqpr2.1, nof_eq_ctqpr3.1, nof_eq_ctqpr3.2]
              conv => arg 2; arg 2; simp [nof_eq_ctqpr7.1]
              conv => arg 2; arg 1; arg 2; simp [nof_eq_ctqpr6.1]
              conv => arg 2; arg 1; arg 1; arg 2; simp [nof_eq_ctqpr5.1]
              conv => arg 2; arg 1; arg 1; arg 1; arg 2; simp [nof_eq_ctqpr4.1]
              simp [nof_eq_ctqpr0.2, nof_eq_ctqpr1.2, nof_eq_ctqpr2.2, nof_eq_ctqpr3.2, nof_eq_ctqpr4.2, nof_eq_ctqpr5.2, nof_eq_ctqpr6.2, nof_eq_ctqpr7.2]

            simp [Fin.val_add]
            iterate 4 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
            have joins : forall (i : Fin 4) (a b : ℕ), a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) = (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
              clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
            have divs : forall (i : Fin 4) (a b : ℕ), (a + b / (65536 ^ i.val)) / 65536 = (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
              clear *-; intro i a b; fin_cases i <;> norm_num <;> omega

            have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
            have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
            simp at *

            rw [j1, d1, j2, d2, j3]
            clear j1 j2 j3 d1 d2 d3 joins divs

            simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
            repeat rw [BitVec.toNat_add]
            iterate 2 rw [DWord.toBitVec128_toNat (by apply DWord.isU128_of_cases <;> simp <;> omega)]
            simp [DWord.toNat]; ring_nf

            rcases b_cry3 with of | nof <;> subst cry3 <;> simp at *
            . have : ctq4 = 0 := by clear *- nof_eq_ctqpr4 is_U64_ctqh; obtain ⟨ _, h ⟩ := nof_eq_ctqpr4; clear h; grind
              subst ctq4; simp at *
              subst cry4; simp at *
              have : ctq5 = 0 := by clear *- nof_eq_ctqpr5 is_U64_ctqh; obtain ⟨ _, h ⟩ := nof_eq_ctqpr5; clear h; grind
              subst ctq5; simp at *
              subst cry5; simp at *
              have : ctq6 = 0 := by clear *- nof_eq_ctqpr6 is_U64_ctqh; obtain ⟨ _, h ⟩ := nof_eq_ctqpr6; clear h; grind
              subst ctq6; simp at *
              subst cry6; simp at *
              have : ctq7 = 0 := by clear *- nof_eq_ctqpr7 is_U64_ctqh; obtain ⟨ _, h ⟩ := nof_eq_ctqpr7; clear h; grind
              subst ctq7; simp at *
              subst cry7; simp at *
              omega
            . have : ctq4 = 65535 := by clear *- nof_eq_ctqpr4 is_U64_ctqh; obtain ⟨ hlt, h ⟩ := nof_eq_ctqpr4; clear h; simp [Fin.ext_iff, Fin.val_add] at *; rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)] at hlt; omega
              subst ctq4; simp at *
              subst cry4; simp at *
              have : ctq5 = 65535 := by clear *- nof_eq_ctqpr5 is_U64_ctqh; obtain ⟨ hlt, h ⟩ := nof_eq_ctqpr5; clear h; simp [Fin.ext_iff, Fin.val_add] at *; rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)] at hlt; omega
              subst ctq5; simp at *
              subst cry5; simp at *
              have : ctq6 = 65535 := by clear *- nof_eq_ctqpr6 is_U64_ctqh; obtain ⟨ hlt, h ⟩ := nof_eq_ctqpr6; clear h; simp [Fin.ext_iff, Fin.val_add] at *; rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)] at hlt; omega
              subst ctq6; simp at *
              subst cry6; simp at *
              have : ctq7 = 65535 := by clear *- nof_eq_ctqpr7 is_U64_ctqh; obtain ⟨ hlt, h ⟩ := nof_eq_ctqpr7; clear h; simp [Fin.ext_iff, Fin.val_add] at *; rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)] at hlt; omega
              subst ctq7; simp at *
              subst cry7; simp at *
              omega

set_option maxRecDepth 1000000 in
lemma spec.divu :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_divu Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRU).1
  := by
  intro cstrs h_is_real h_is_divu
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_divu] at h_is_divu

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_divu]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divu_remu a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop2 h_is_divu
    simp [h_is_divu, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c

set_option maxRecDepth 1000000 in
lemma spec.remu :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_remu Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRU).2
  := by
  intro cstrs h_is_real h_is_remu
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_remu] at h_is_remu

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_remu]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divu_remu a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop4 h_is_remu
    simp [h_is_remu, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c
  . apply Word.isU64_of_cases <;> simp <;> omega
  . exact is_U64_c

end divu_remu

section divw_remw

set_option linter.unusedVariables false in
lemma divw_remw
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : Fin KB)
  (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
  (sop1 : is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop2 : is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop3 : is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop4 : is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop5 : is_divw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop6 : is_remw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop7 : is_divuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_remuw = 0)
  (sop8 : is_remuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0)
  (eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw)
  (eq_b_neg : b_neg = msb_b * (is_div + is_rem + is_divw + is_remw))
  (eq_rem_neg : rem_neg = msb_rem * (is_div + is_rem + is_divw + is_remw))
  (eq_c_neg : c_neg = msb_c * (is_div + is_rem + is_divw + is_remw))
  (eq_lb0 : lb0 = b0)
  (eq_lc0 : lc0 = c0)
  (eq_lb1 : lb1 = b1)
  (eq_lc1 : lc1 = c1)
  (eq_lb2 : lb2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc2 : lc2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_lb3 : lb3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc3 : lc3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_qbc0 : qbc0 = q0)
  (eq_qbc1 : qbc1 = q1)
  (w_eq_qbc2_uw : is_divuw + is_remuw = 0 ∨ qbc2 = 0)
  (w_eq_qbc2_w : is_divw + is_remw = 0 ∨ qbc2 = msb_quot * 65535)
  (w_eq_q2_w : is_word = 0 ∨ q2 = msb_quot * 65535)
  (eq_qbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc2 = q2)
  (w_eq_qbc3_uw : is_divuw + is_remuw = 0 ∨ qbc3 = 0)
  (w_eq_qbc3_w : is_divw + is_remw = 0 ∨ qbc3 = msb_quot * 65535)
  (w_eq_q3_w : is_word = 0 ∨ q3 = msb_quot * 65535)
  (eq_qbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc3 = q3)
  (eq_rbc0 : rbc0 = r0)
  (eq_rbc1 : rbc1 = r1)
  (w_eq_rbc2_uw : is_divuw + is_remuw = 0 ∨ rbc2 = 0)
  (w_eq_rbc2_w : is_divw + is_remw = 0 ∨ rbc2 = msb_rem * 65535)
  (w_eq_r2_w : is_word = 0 ∨ r2 = msb_rem * 65535)
  (eq_rbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc2 = r2)
  (w_eq_rbc3_uw : is_divuw + is_remuw = 0 ∨ rbc3 = 0)
  (w_eq_rbc3_w : is_divw + is_remw = 0 ∨ rbc3 = msb_rem * 65535)
  (w_eq_r3_w : is_word = 0 ∨ r3 = msb_rem * 65535)
  (eq_rbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc3 = r3)
  (eq_is_overflow : is_overflow = is_overflow_b * is_overflow_c * (is_div + is_rem + is_divw + is_remw))
  (eq_b_neg_not_overflow : b_neg_not_overflow = b_neg * (1 - is_overflow))
  (eq_not_b_neg_not_overflow : b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow))
  (of_eq_q0 : is_overflow = 0 ∨ q0 = b0)
  (of_eq_r0 : is_overflow = 0 ∨ r0 = 0)
  (of_eq_q1 : is_overflow = 0 ∨ q1 = b1)
  (of_eq_r1 : is_overflow = 0 ∨ r1 = 0)
  (of_eq_q2 : is_overflow = 0 ∨ q2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r2 : is_overflow = 0 ∨ r2 = 0)
  (of_eq_q3 : is_overflow = 0 ∨ q3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r3 : is_overflow = 0 ∨ r3 = 0)
  (nof_eq_ctqpr0 : is_overflow = 1 ∨ b0 = ctq0 + r0 - cry0 * 65536)
  (nof_eq_ctqpr1 : is_overflow = 1 ∨ b1 = ctq1 + r1 - cry1 * 65536 + cry0)
  (nof_eq_ctqpr2 : is_overflow = 1 ∨ b2 * (1 - is_word) + b_neg * is_word * 65535 = ctq2 + rbc2 - cry2 * 65536 + cry1)
  (nof_eq_ctqpr3 : is_overflow = 1 ∨ b3 * (1 - is_word) + b_neg * is_word * 65535 = ctq3 + rbc3 - cry3 * 65536 + cry2)
  (nof_eq_ctqpr4 : is_overflow = 1 ∨ ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3 = b_neg * 65535)
  (nof_eq_ctqpr5 : is_overflow = 1 ∨ ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4 = b_neg * 65535)
  (nof_eq_ctqpr6 : is_overflow = 1 ∨ ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5 = b_neg * 65535)
  (nof_eq_ctqpr7 : is_overflow = 1 ∨ ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6 = b_neg * 65535)
  (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
  (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
  (u16_ctqpr2 : (ctq2 + rbc2 - cry2 * 65536 + cry1).val < 65536)
  (u16_ctqpr3 : (ctq3 + rbc3 - cry3 * 65536 + cry2).val < 65536)
  (u16_ctqpr4 : (ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3).val < 65536)
  (u16_ctqpr5 : (ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4).val < 65536)
  (u16_ctqpr6 : (ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5).val < 65536)
  (u16_ctqpr7 : (ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6).val < 65536)
  (eq_d_a0 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a0 = q0)
  (eq_r_a0 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a0 = r0)
  (eq_d_a1 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a1 = q1)
  (eq_r_a1 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a1 = r1)
  (eq_d_a2 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a2 = q2)
  (eq_r_a2 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a2 = r2)
  (eq_d_a3 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a3 = q3)
  (eq_r_a3 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a3 = r3)
  (r_neg_b_neg : rem_neg = 0 ∨ b_neg = 1)
  (r_pos_b_pos : r0 + r1 + r2 + r3 = 0 ∨ rem_neg = 1 ∨ b_neg = 0)
  (c0_eq_q0 : is_c_0 = 0 ∨ q0 = 65535)
  (c0_eq_q1 : is_c_0 = 0 ∨ q1 = 65535)
  (c0_eq_q2 : is_c_0 = 0 ∨ q2 = 65535)
  (c0_eq_q3 : is_c_0 = 0 ∨ q3 = 65535)
  (c0_eq_r0 : is_c_0 = 0 ∨ r0 = b0)
  (c0_eq_r1 : is_c_0 = 0 ∨ r1 = b1)
  (c0_eq_r2 : is_c_0 = 0 ∨ rbc2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (c0_eq_r3 : is_c_0 = 0 ∨ rbc3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (cn_ac0 : c_neg = 1 ∨ ac0 = c0)
  (rn_ar0 : rem_neg = 1 ∨ ar0 = r0)
  (cn_ac1 : c_neg = 1 ∨ ac1 = c1)
  (rn_ar1 : rem_neg = 1 ∨ ar1 = r1)
  (cn_ac2 : c_neg = 1 ∨ ac2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar2 : rem_neg = 1 ∨ ar2 = rbc2)
  (cn_ac3 : c_neg = 1 ∨ ac3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar3 : rem_neg = 1 ∨ ar3 = rbc3)
  (u16_ac0 : ac0.val < 65536)
  (u16_ac1 : ac1.val < 65536)
  (u16_ac2 : ac2.val < 65536)
  (u16_ac3 : ac3.val < 65536)
  (eq_cnop0 : c_neg = 0 ∨ cnop0 = 0)
  (eq_cnop1 : c_neg = 0 ∨ cnop1 = 0)
  (eq_cnop2 : c_neg = 0 ∨ cnop2 = 0)
  (eq_cnop3 : c_neg = 0 ∨ cnop3 = 0)
  (u16_ar0 : ar0.val < 65536)
  (u16_ar1 : ar1.val < 65536)
  (u16_ar2 : ar2.val < 65536)
  (u16_ar3 : ar3.val < 65536)
  (eq_rnop0 : rem_neg = 0 ∨ rnop0 = 0)
  (eq_rnop1 : rem_neg = 0 ∨ rnop1 = 0)
  (eq_rnop2 : rem_neg = 0 ∨ rnop2 = 0)
  (eq_rnop3 : rem_neg = 0 ∨ rnop3 = 0)
  (eq_abs_c_alu_event : abs_c_alu_event = c_neg)
  (eq_abs_rem_alu_event : abs_rem_alu_event = rem_neg)
  (eq_maco10 : maco10 = is_c_0 + (1 - is_c_0) * ac0)
  (eq_maco11 : maco11 = (1 - is_c_0) * ac1)
  (eq_maco12 : maco12 = (1 - is_c_0) * ac2)
  (eq_maco13 : maco13 = (1 - is_c_0) * ac3)
  (eq_arlt : is_c_0 = 1 ∨ arlt = 1)
  (u16_q0 : q0.val < 65536)
  (u16_q1 : q1.val < 65536)
  (u16_q2 : q2.val < 65536)
  (u16_q3 : q3.val < 65536)
  (u16_r0 : r0.val < 65536)
  (u16_r1 : r1.val < 65536)
  (u16_r2 : r2.val < 65536)
  (u16_r3 : r3.val < 65536)
  (b_cry0 : cry0 = 0 ∨ cry0 = 1)
  (b_cry1 : cry1 = 0 ∨ cry1 = 1)
  (b_cry2 : cry2 = 0 ∨ cry2 = 1)
  (b_cry3 : cry3 = 0 ∨ cry3 = 1)
  (b_cry4 : cry4 = 0 ∨ cry4 = 1)
  (b_cry5 : cry5 = 0 ∨ cry5 = 1)
  (b_cry6 : cry6 = 0 ∨ cry6 = 1)
  (b_cry7 : cry7 = 0 ∨ cry7 = 1)
  (u16_ctq0 : ctq0.val < 65536)
  (u16_ctq1 : ctq1.val < 65536)
  (u16_ctq2 : ctq2.val < 65536)
  (u16_ctq3 : ctq3.val < 65536)
  (u16_ctq4 : ctq4.val < 65536)
  (u16_ctq5 : ctq5.val < 65536)
  (u16_ctq6 : ctq6.val < 65536)
  (u16_ctq7 : ctq7.val < 65536)
  (b_is_div : is_div = 0 ∨ is_div = 1)
  (b_is_divu : is_divu = 0 ∨ is_divu = 1)
  (b_is_rem : is_rem = 0 ∨ is_rem = 1)
  (b_is_remu : is_remu = 0 ∨ is_remu = 1)
  (b_is_divw : is_divw = 0 ∨ is_divw = 1)
  (b_is_remw : is_remw = 0 ∨ is_remw = 1)
  (b_is_divuw : is_divuw = 0 ∨ is_divuw = 1)
  (b_is_remuw : is_remuw = 0 ∨ is_remuw = 1)
  (b_is_overflow : is_overflow = 0 ∨ is_overflow = 1)
  (b_is_real_not_word : is_word = 0 ∨ is_word = 1)
  (b_b_neg : b_neg = 0 ∨ b_neg = 1)
  (b_b_neg_not_overflow : b_neg_not_overflow = 0 ∨ b_neg_not_overflow = 1)
  (b_b_not_neg_not_overflow : b_not_neg_not_overflow = 0 ∨ b_not_neg_not_overflow = 1)
  (b_rem_neg : rem_neg = 0 ∨ rem_neg = 1)
  (b_c_neg : c_neg = 0 ∨ c_neg = 1)
  (b_one_of_ops : is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = #v[0, 32768, 0, 0] then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = #v[65535, 65535, 0, 0] then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = #v[0, 0, 0, 0] then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = #v[0, 0, 0, 32768] then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = #v[65535, 65535, 65535, 65535] then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_divw + is_remw = 1 →
    ⟨ Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRWS
      := by
    intro divw_remw
    obtain ⟨ z_div, z_rem, z_divu, z_remu, z_divuw, z_remuw ⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divuw = 0 ∧ is_remuw = 0 := by
      clear *- divw_remw sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops
      rcases b_is_divw <;> rcases b_is_remw <;> simp_all
    simp [z_div, z_rem, z_divu, z_remu, z_divuw, z_remuw, divw_remw] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3
    subst abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    have div_zero' : is_c_0 = if c0 = 0 ∧ c1 = 0 then 1 else 0 := by rw [div_zero, w_eq_msb_c]; clear *-; aesop
    clear div_zero
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toInt_setWidth]
    rw [Word.setWidth_eq_low is_U64_b, Word.setWidth_eq_low is_U64_c]
    have is_U32_bl := Word.isU64_low_isU32 is_U64_b
    have is_U32_cl := Word.isU64_low_isU32 is_U64_c
    simp [Word.low] at *
    rw [HWord.toBitVec32_toInt is_U32_bl, HWord.toBitVec32_toInt is_U32_cl]
    have ext_q : #v[q0, q1, q2, q3] = HWord.extend #v[q0, q1] true := by simp [HWord.extend, HWord.isNegative]; subst q2 q3 msb_quot; split_ifs <;> simp
    have ext_r : #v[r0, r1, r2, r3] = HWord.extend #v[r0, r1] true := by simp [HWord.extend, HWord.isNegative]; subst r2 r3 msb_rem; split_ifs <;> simp
    rw [ext_q, ext_r]
    repeat rw [HWord.extend_true_is_signExtend (by apply HWord.isU32_of_cases <;> simpa)]
    have lb_b := HWord.toInt_lb is_U32_bl; have ub_b := HWord.toInt_ub is_U32_bl
    have lb_c := HWord.toInt_lb is_U32_cl; have ub_c := HWord.toInt_ub is_U32_cl
    split_ifs at div_zero' with nzc <;> simp [div_zero'] at *
    . obtain ⟨zc0, zc1⟩ := nzc
      simp [zc0, zc1] at *
      have : HWord.toInt #v[0, 0] = 0 := by simp [HWord.toInt, HWord.isNegative, HWord.toNat]
      simp [this, c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3]
      split_ands
      . simp [HWord.toBitVec32, HWord.toNat]
      . simp only [← BitVec.toInt_inj]
        rw [BitVec.toInt_signExtend_of_le (by simp), HWord.toBitVec32_toInt is_U32_bl]
        simp; rw [Int.bmod_eq_of_le] <;> simp <;> omega
    . subst arlt maco10 maco11 maco12 maco13
      rw [if_neg]; rotate_left
      . intro zc; simp [HWord.toInt, HWord.isNegative, HWord.toNat] at zc; apply nzc
        apply HWord.lt_cases_of_isU32 at is_U32_cl; simp at is_U32_cl; omega
      . rcases b_is_overflow with nof | of; rotate_left
        . simp [of] at *
          split_ifs at w_overflow_b with ofb <;> simp [w_overflow_b] at *
          split_ifs at w_overflow_c with ofc <;> simp [w_overflow_c] at *
          obtain ⟨eb0, eb1⟩ := ofb
          obtain ⟨ec0, ec1⟩ := ofc
          simp [of_eq_q0, of_eq_q1, of_eq_r0, of_eq_r1, eb0, eb1, ec0, ec1] at *
          simp only [HWord.toBitVec32, HWord.toInt, HWord.isNegative, HWord.toNat]
          simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
          simp
        . simp [nof] at *
          rw [if_neg]; rotate_left
          . intro ⟨ h_eq_b, h_eq_c ⟩
            have : (#v[b0, b1] : HWord (Fin KB)) = #v[0, 32768] := by
              rw [HWord.eq_toInt_eq is_U32_bl, h_eq_b]
              simp [HWord.toInt, HWord.isNegative, HWord.toNat]
              apply HWord.isU32_of_cases <;> simp
            simp at this
            rw [if_pos (by exact this)] at w_overflow_b; simp [w_overflow_b] at *; clear this
            have : (#v[c0, c1] : HWord (Fin KB)) = #v[65535, 65535] := by
              rw [HWord.eq_toInt_eq is_U32_cl, h_eq_c]
              simp [HWord.toInt, HWord.isNegative, HWord.toNat]
              apply HWord.isU32_of_cases <;> simp
            simp at this; rw [if_pos (by exact this)] at w_overflow_c; simp [w_overflow_c] at *
          . have is_U32_rl : HWord.isU32 #v[r0, r1] := by apply HWord.isU32_of_cases <;> simpa
            have is_U32_ql : HWord.isU32 #v[q0, q1] := by apply HWord.isU32_of_cases <;> simpa
            have lb_q := HWord.toInt_lb is_U32_ql; have ub_q := HWord.toInt_ub is_U32_ql
            have lb_r := HWord.toInt_lb is_U32_rl; have ub_r := HWord.toInt_ub is_U32_rl
            suffices :
              HWord.toInt #v[q0, q1] = (HWord.toInt #v[b0, b1]).tdiv (HWord.toInt #v[c0, c1]) ∧
              HWord.toInt #v[r0, r1] = (HWord.toInt #v[b0, b1]).tmod (HWord.toInt #v[c0, c1])
            . obtain ⟨ hdiv, hrem ⟩ := this
              rw [← hdiv, ← hrem]
              simp [← BitVec.toInt_inj]
              repeat rw [BitVec.toInt_signExtend_of_le (by simp)]
              rw [HWord.toBitVec32_toInt is_U32_ql, HWord.toBitVec32_toInt is_U32_rl]
              iterate 2 rw [Int.bmod_eq_of_le (by omega) (by omega)]
              trivial
            . have sgn_msb_b : msb_b = 1 → (HWord.toInt #v[b0, b1]).sign = -1 := by
                intro h_msb_b; rw [HWord.sign_cases is_U32_bl]; simp [h_msb_b] at *
                intro hneg; simp [HWord.isNegative] at hneg
                omega
              have sgn_msb_c : msb_c = 1 → (HWord.toInt #v[c0, c1]).sign = -1 := by
                intro h_msb_c; rw [HWord.sign_cases is_U32_cl]; simp [h_msb_c] at *
                intro hneg; simp [HWord.isNegative] at hneg
                omega
              have sgn_msb_rem : msb_rem = 1 → (HWord.toInt #v[r0, r1]).sign = -1 := by
                intro h_msb_b; rw [HWord.sign_cases is_U32_rl]; simp [h_msb_b] at *
                intro hneg; simp [HWord.isNegative] at hneg
                omega
              have cnz : HWord.toInt #v[c0, c1] ≠ 0 := by
                intro zc; apply nzc; apply HWord.lt_cases_of_isU32 at is_U32_cl
                clear *- zc is_U32_cl; simp [HWord.toInt, HWord.isNegative, HWord.toNat] at *
                split_ifs at zc <;> omega

              -- First condition
              have h_prod : HWord.toInt #v[b0, b1] = HWord.toInt #v[q0, q1] * HWord.toInt #v[c0, c1] + HWord.toInt #v[r0, r1] := by
                clear *- is_U32_bl is_U32_cl is_U32_ql is_U32_rl
                         u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3
                         b_cry0 b_cry1 b_cry2 b_cry3
                         w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot r_neg_b_neg r_pos_b_pos
                         nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                         main_mul_low main_mul_high lb_b ub_b lb_c ub_c lb_q ub_q lb_r ub_r
                obtain ⟨ is_U64_ctql, ctq_low ⟩ := main_mul_low
                have eq_eb : (#v[b0, b1, msb_b * 65535, msb_b * 65535] : Word (Fin KB)) = HWord.extend #v[b0, b1] true := by simp [HWord.extend, HWord.isNegative, w_eq_msb_b]
                have eq_er : (#v[r0, r1, msb_rem * 65535, msb_rem * 65535] : Word (Fin KB)) = HWord.extend #v[r0, r1] true := by simp [HWord.extend, HWord.isNegative, w_eq_msb_rem]
                suffices bv_ctqr:
                  Word.toBitVec64 #v[b0, b1, msb_b * 65535, msb_b * 65535] =
                    Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] +
                    Word.toBitVec64 #v[r0, r1, msb_rem * 65535, msb_rem * 65535]
                . rw [eq_eb, eq_er] at bv_ctqr
                  simp [execute_MUL_pure, -BitVec.extractLsb] at ctq_low
                  have : BitVec.extractLsb 63 0 ((Word.toBitVec64 #v[q0, q1, msb_quot * 65535, msb_quot * 65535]).extend 128 False * (Word.toBitVec64 #v[c0, c1, msb_c * 65535, msb_c * 65535]).extend 128 False) = BitVec.extractLsb 63 0 ((Word.toBitVec64 #v[q0, q1, msb_quot * 65535, msb_quot * 65535]).extend 128 True * (Word.toBitVec64 #v[c0, c1, msb_c * 65535, msb_c * 65535]).extend 128 True) := by simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
                  rw [this] at ctq_low; clear this
                  have : #v[q0, q1, msb_quot * 65535, msb_quot * 65535] = HWord.extend #v[q0, q1] true := by simp [HWord.extend]; simp [w_eq_msb_quot, HWord.isNegative]
                  rw [this] at ctq_low; clear this
                  have : #v[c0, c1, msb_c * 65535, msb_c * 65535] = HWord.extend #v[c0, c1] true := by simp [HWord.extend]; simp [w_eq_msb_c, HWord.isNegative]
                  rw [this] at ctq_low; clear this
                  simp only [← BitVec.toInt_inj] at ctq_low
                  have : ((HWord.extend #v[q0, q1] true).toBitVec64.extend 128 True * (HWord.extend #v[c0, c1] true).toBitVec64.extend 128 True).toInt = HWord.toInt #v[q0, q1] * HWord.toInt #v[c0, c1] := by
                    iterate 2 rw [HWord.extend_true_is_signExtend (by assumption)]
                    simp [BitVec.extend, BitVec.toInt_signExtend_of_le]
                    iterate 2 rw [HWord.toBitVec32_toInt (by assumption)]
                    rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                  rw [extractLsb_is_toInt (by rw [this]; nlinarith) (by rw [this]; nlinarith)] at ctq_low
                  rw [this] at ctq_low; clear this
                  simp [← BitVec.toInt_inj, ctq_low] at bv_ctqr
                  iterate 2 rw [HWord.extend_true_is_signExtend (by assumption), BitVec.toInt_signExtend_of_le (by simp), HWord.toBitVec32_toInt (by assumption)] at bv_ctqr
                  rw [bv_ctqr]
                  rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
                . clear is_U32_cl is_U32_ql lb_b ub_b lb_c ub_c lb_q ub_q lb_r ub_r ctq_low eq_eb eq_er w_eq_msb_c w_eq_msb_quot r_neg_b_neg r_pos_b_pos eq_is_word main_mul_high
                  apply HWord.lt_cases_of_isU32 at is_U32_bl
                  apply HWord.lt_cases_of_isU32 at is_U32_rl
                  apply Word.lt_cases_of_isU64 at is_U64_ctql
                  have : (msb_rem * 65535).val < 65536 := by rw [w_eq_msb_rem]; split_ifs <;> simp
                  simp at *
                  rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                  rw [div_mod_decomposition_w (by omega) (by omega)] at nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                  trans Word.toBitVec64 #v[b0, b1, (ctq2 + msb_rem * 65535 + cry1) % 65536, (ctq3 + msb_rem * 65535 + cry2) % 65536]
                  . rw [← nof_eq_ctqpr2.1, ← nof_eq_ctqpr3.1]
                  . conv => lhs; simp [Word.toBitVec64, Word.toNat]
                            simp [nof_eq_ctqpr0.1, nof_eq_ctqpr1.1]
                            simp [nof_eq_ctqpr0.2, nof_eq_ctqpr1.2, nof_eq_ctqpr2.2, nof_eq_ctqpr3.2]
                    simp [Fin.val_add]
                    iterate 4 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
                    have joins : forall (i : Fin 4) (a b : ℕ), a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) = (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
                      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
                    have divs : forall (i : Fin 4) (a b : ℕ), (a + b / (65536 ^ i.val)) / 65536 = (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
                      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega

                    have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
                    have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
                    simp at *

                    rw [j1, d1, j2, d2, j3]
                    clear j1 j2 j3 d1 d2 d3 joins divs

                    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
                    repeat rw [BitVec.toNat_add]
                    iterate 2 rw [Word.toBitVec64_toNat (by apply Word.isU64_of_cases <;> simp <;> try omega)]
                    simp [Word.toNat]; ring_nf

              -- Second condition
              have h_abs : |HWord.toInt #v[r0, r1]| < |HWord.toInt #v[c0, c1]| := by
                have is_U64_ar : Word.isU64 #v[ar0, ar1, ar2, ar3] := by apply Word.isU64_of_cases <;> simpa
                have is_U64_ac : Word.isU64 #v[ac0, ac1, ac2, ac3] := by apply Word.isU64_of_cases <;> simpa
                have h_eq_nmax : - 2^31 = HWord.toInt #v[0, 32768] := by simp [HWord.toInt, HWord.isNegative, HWord.toNat]
                have cls := HWord.lt_cases_of_isU32 is_U32_cl
                have rls := HWord.lt_cases_of_isU32 is_U32_rl
                have lb_r := HWord.toInt_lb is_U32_rl; have ub_r := HWord.toInt_ub is_U32_rl
                clear is_U64_b is_U64_c u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7
                      u16_q0 u16_q1 u16_q2 u16_q3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7
                      b_b_neg_not_overflow b_b_not_neg_not_overflow eq_is_overflow eq_b_neg_not_overflow eq_not_b_neg_not_overflow
                      u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7
                      b_is_divw b_is_remw sop5 sop6 eq_d_a0 eq_d_a1 eq_d_a2 eq_d_a3 eq_r_a0 eq_r_a1 eq_r_a2 eq_r_a3
                      w_eq_q2_w w_eq_q3_w w_eq_msb_b w_eq_msb_quot w_overflow_b w_overflow_c b_b_neg
                      r_neg_b_neg r_pos_b_pos main_mul_low is_U32_bl lb_b ub_b lb_q ub_q ext_q ext_r
                      nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
                      sgn_msb_b h_prod u16_r3
                subst r2 r3
                have u16_c2 : (msb_c * 65535).val < 65536 := by rw [w_eq_msb_c]; split_ifs <;> simp
                rcases b_rem_neg with rem_nneg | rem_neg <;> rcases b_c_neg with c_nneg | c_neg
                . simp [rem_nneg, c_nneg] at *
                  subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3
                  simp [HWord.toInt, HWord.isNegative]
                  iterate 2 rw [if_neg (by omega)]
                  simp [Word.toNat] at abs_check
                  simpa
                . simp [rem_nneg, c_neg] at *
                  subst ar0 ar1 ar2 ar3 cnop0 cnop1 cnop2 cnop3
                  simp at *
                  obtain ⟨ _, heqz ⟩ := c_neg_sum_zero
                  apply sum_zero_abs (by apply Word.isU64_of_cases <;> simp <;> omega) is_U64_ac (by simp [Word.isNegative]) at heqz
                  obtain ⟨ hc_lb, hc_nlb ⟩ := heqz
                  have : Word.toInt #v[c0, c1, 65535, 65535] = HWord.toInt #v[c0, c1] := by
                    rw [Word.toInt, Word.toNat_def, HWord.toInt, HWord.toNat]
                    unfold Word.isNegative HWord.isNegative
                    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
                    simp [if_pos]; omega
                  rw [this] at hc_lb hc_nlb; clear this
                  by_cases is_c_lb : HWord.toInt #v[c0, c1] = -2 ^ 63
                  . omega
                  . have is_c_lb' := is_c_lb
                    apply hc_nlb at is_c_lb'
                    rw [Word.toInt] at is_c_lb'; rw [if_neg] at is_c_lb'; rw [← is_c_lb']
                    . rw [HWord.toInt, if_neg (by simp [HWord.isNegative]; omega)]
                      simp; simp [HWord.toNat, Word.toNat]
                      simp [Word.toNat] at abs_check; exact abs_check
                    . rw [Word.isNegative_toInt is_U64_ac]; simp_all
                . simp [rem_neg, c_nneg] at *
                  subst ac0 ac1 ac2 ac3 rnop0 rnop1 rnop2 rnop3
                  simp at *
                  obtain ⟨ _, heqz ⟩ := rem_neg_sum_zero
                  apply sum_zero_abs (by apply Word.isU64_of_cases <;> simp <;> omega) is_U64_ar (by simp [Word.isNegative]) at heqz
                  obtain ⟨ hr_lb, hr_nlb ⟩ := heqz
                  have : Word.toInt #v[r0, r1, 65535, 65535] = HWord.toInt #v[r0, r1] := by
                    rw [Word.toInt, Word.toNat_def, HWord.toInt, HWord.toNat]
                    unfold Word.isNegative HWord.isNegative
                    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
                    simp [if_pos]; omega
                  rw [this] at hr_lb hr_nlb; clear this
                  by_cases is_rem_lb : HWord.toInt #v[r0, r1] = -2 ^ 63
                  . omega
                  . have is_rem_lb' := is_rem_lb
                    apply hr_nlb at is_rem_lb'
                    rw [Word.toInt] at is_rem_lb'; rw [if_neg] at is_rem_lb'; rw [← is_rem_lb']
                    . rw [HWord.toInt, if_neg (by simp [HWord.isNegative]; omega)]
                      simp; simp [HWord.toNat, Word.toNat]
                      simp [Word.toNat] at abs_check; exact abs_check
                    . rw [Word.isNegative_toInt is_U64_ar]; simp_all
                . simp [rem_neg, c_neg] at *
                  subst rnop0 rnop1 rnop2 rnop3 cnop0 cnop1 cnop2 cnop3
                  obtain ⟨ _, heqz_c ⟩ := c_neg_sum_zero
                  obtain ⟨ _, heqz_rem ⟩ := rem_neg_sum_zero
                  apply sum_zero_abs (by apply Word.isU64_of_cases <;> simp <;> omega) is_U64_ac (by simp [Word.isNegative]) at heqz_c
                  apply sum_zero_abs (by apply Word.isU64_of_cases <;> simp <;> omega) is_U64_ar (by simp [Word.isNegative]) at heqz_rem
                  have eqc : Word.toInt #v[c0, c1, 65535, 65535] = HWord.toInt #v[c0, c1] := by
                    rw [Word.toInt, Word.toNat_def, HWord.toInt, HWord.toNat]
                    unfold Word.isNegative HWord.isNegative
                    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
                    simp [if_pos w_eq_msb_c]; omega
                  have eqr : Word.toInt #v[r0, r1, 65535, 65535] = HWord.toInt #v[r0, r1] := by
                    rw [Word.toInt, Word.toNat_def, HWord.toInt, HWord.toNat]
                    unfold Word.isNegative HWord.isNegative
                    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
                    simp [if_pos]; omega
                  rw [eqc] at heqz_c; rw [eqr] at heqz_rem
                  by_cases is_c_lb : HWord.toInt #v[c0, c1] = -2 ^ 63
                  . by_contra; clear *- lb_c ub_c is_c_lb; omega
                  . by_cases is_r_lb : HWord.toInt #v[r0, r1] = -2 ^ 63
                    . by_contra; clear *- lb_r ub_r is_r_lb; omega
                    . obtain ⟨ hc_lb, hc_nlb ⟩ := heqz_c
                      obtain ⟨ hr_lb, hr_nlb ⟩ := heqz_rem
                      clear hc_lb hr_lb
                      specialize hc_nlb is_c_lb; specialize hr_nlb is_r_lb
                      rw [← hc_nlb, ← hr_nlb]; simp [Word.toInt]
                      iterate 2 rw [if_neg]
                      . omega
                      . simp_all [Word.isNegative_toInt is_U64_ac]
                      . simp_all [Word.isNegative_toInt is_U64_ar]

              -- Third condition
              have h_sign : HWord.toInt #v[r0, r1] = 0 ∨ (HWord.toInt #v[r0, r1]).sign = (HWord.toInt #v[b0, b1]).sign := by
                rcases b_b_neg with b_msb_nneg | b_msb_neg
                . simp [b_msb_nneg] at *
                  simp [r_neg_b_neg] at *
                  by_cases rz : HWord.toInt #v[r0, r1] = 0 <;> [ (left; exact rz); right ]
                  rw [HWord.sign_cases is_U32_bl, HWord.sign_cases is_U32_rl]
                  simp [HWord.isNegative]
                  split_ifs with hr hb hw hb hw <;> try omega
                  have rpos : HWord.toInt #v[r0, r1] > 0 := by simp [HWord.toInt, HWord.isNegative, HWord.toNat] at rz ⊢; split_ifs; omega
                  rw [h_prod] at hw; simp
                  set q := HWord.toInt #v[q0, q1]
                  set c := HWord.toInt #v[c0, c1]
                  set r := HWord.toInt #v[r0, r1]
                  clear *- rpos h_abs hw
                  simp [Int.abs_cases] at h_abs; rw [if_pos (by omega)] at h_abs
                  apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
                  all_goals
                    have : c * q > r := by split_ifs at * <;> nlinarith
                    nlinarith
                . simp [b_msb_neg] at *
                  simp [Int.sign_eq_neg_one_of_neg sgn_msb_b]
                  clear *- u16_r0 u16_r1 u16_r2 u16_r3 r_pos_b_pos sgn_msb_rem
                  rcases r_pos_b_pos with hrz | hmsb <;> [ left; simp_all ]
                  simp [HWord.toInt, HWord.isNegative, HWord.toNat]
                  omega

              rw [tdiv_tmod_unique_full cnz]
              split_ands <;> assumption

set_option maxRecDepth 1000000 in
lemma spec.divw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_divw Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWS).1
  := by
  intro cstrs h_is_real h_is_divw
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_divw] at h_is_divw

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_divw]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divw_remw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop5 h_is_divw
    simp [h_is_divw, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rw [w_eq_msb_c] <;> split_ifs <;> simp
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rcases b_c_neg with eq_msb_c | eq_msb_c <;> rw [eq_msb_c] <;> simp
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rcases b_c_neg with eq_msb_c | eq_msb_c <;> rw [eq_msb_c] <;> simp

set_option maxRecDepth 1000000 in
lemma spec.remw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_remw Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWS).2
  := by
  intro cstrs h_is_real h_is_remw
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_remw] at h_is_remw

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_remw]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divw_remw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop6 h_is_remw
    simp [h_is_remw, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rw [w_eq_msb_c] <;> split_ifs <;> simp
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rcases b_c_neg with eq_msb_c | eq_msb_c <;> rw [eq_msb_c] <;> simp
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> [ omega; omega; skip; skip ] <;> rcases b_c_neg with eq_msb_c | eq_msb_c <;> rw [eq_msb_c] <;> simp

end divw_remw

section divuw_remuw

set_option linter.unusedVariables false in
lemma divuw_remuw
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event : Fin KB)
  (is_U64_b : Word.isU64 #v[b0, b1, b2, b3])
  (is_U64_c : Word.isU64 #v[c0, c1, c2, c3])
  (sop1 : is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop2 : is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop3 : is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop4 : is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop5 : is_divw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_remw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop6 : is_remw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_divuw = 0 ∧ is_remuw = 0)
  (sop7 : is_divuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_remuw = 0)
  (sop8 : is_remuw = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 ∧ is_divuw = 0)
  (eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw)
  (eq_b_neg : b_neg = msb_b * (is_div + is_rem + is_divw + is_remw))
  (eq_rem_neg : rem_neg = msb_rem * (is_div + is_rem + is_divw + is_remw))
  (eq_c_neg : c_neg = msb_c * (is_div + is_rem + is_divw + is_remw))
  (eq_lb0 : lb0 = b0)
  (eq_lc0 : lc0 = c0)
  (eq_lb1 : lb1 = b1)
  (eq_lc1 : lc1 = c1)
  (eq_lb2 : lb2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc2 : lc2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_lb3 : lb3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (eq_lc3 : lc3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (eq_qbc0 : qbc0 = q0)
  (eq_qbc1 : qbc1 = q1)
  (w_eq_qbc2_uw : is_divuw + is_remuw = 0 ∨ qbc2 = 0)
  (w_eq_qbc2_w : is_divw + is_remw = 0 ∨ qbc2 = msb_quot * 65535)
  (w_eq_q2_w : is_word = 0 ∨ q2 = msb_quot * 65535)
  (eq_qbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc2 = q2)
  (w_eq_qbc3_uw : is_divuw + is_remuw = 0 ∨ qbc3 = 0)
  (w_eq_qbc3_w : is_divw + is_remw = 0 ∨ qbc3 = msb_quot * 65535)
  (w_eq_q3_w : is_word = 0 ∨ q3 = msb_quot * 65535)
  (eq_qbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ qbc3 = q3)
  (eq_rbc0 : rbc0 = r0)
  (eq_rbc1 : rbc1 = r1)
  (w_eq_rbc2_uw : is_divuw + is_remuw = 0 ∨ rbc2 = 0)
  (w_eq_rbc2_w : is_divw + is_remw = 0 ∨ rbc2 = msb_rem * 65535)
  (w_eq_r2_w : is_word = 0 ∨ r2 = msb_rem * 65535)
  (eq_rbc2 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc2 = r2)
  (w_eq_rbc3_uw : is_divuw + is_remuw = 0 ∨ rbc3 = 0)
  (w_eq_rbc3_w : is_divw + is_remw = 0 ∨ rbc3 = msb_rem * 65535)
  (w_eq_r3_w : is_word = 0 ∨ r3 = msb_rem * 65535)
  (eq_rbc3 : is_divu + is_remu + is_div + is_rem = 0 ∨ rbc3 = r3)
  (eq_is_overflow : is_overflow = is_overflow_b * is_overflow_c * (is_div + is_rem + is_divw + is_remw))
  (eq_b_neg_not_overflow : b_neg_not_overflow = b_neg * (1 - is_overflow))
  (eq_not_b_neg_not_overflow : b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow))
  (of_eq_q0 : is_overflow = 0 ∨ q0 = b0)
  (of_eq_r0 : is_overflow = 0 ∨ r0 = 0)
  (of_eq_q1 : is_overflow = 0 ∨ q1 = b1)
  (of_eq_r1 : is_overflow = 0 ∨ r1 = 0)
  (of_eq_q2 : is_overflow = 0 ∨ q2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r2 : is_overflow = 0 ∨ r2 = 0)
  (of_eq_q3 : is_overflow = 0 ∨ q3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (of_eq_r3 : is_overflow = 0 ∨ r3 = 0)
  (nof_eq_ctqpr0 : is_overflow = 1 ∨ b0 = ctq0 + r0 - cry0 * 65536)
  (nof_eq_ctqpr1 : is_overflow = 1 ∨ b1 = ctq1 + r1 - cry1 * 65536 + cry0)
  (nof_eq_ctqpr2 : is_overflow = 1 ∨ b2 * (1 - is_word) + b_neg * is_word * 65535 = ctq2 + rbc2 - cry2 * 65536 + cry1)
  (nof_eq_ctqpr3 : is_overflow = 1 ∨ b3 * (1 - is_word) + b_neg * is_word * 65535 = ctq3 + rbc3 - cry3 * 65536 + cry2)
  (nof_eq_ctqpr4 : is_overflow = 1 ∨ ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3 = b_neg * 65535)
  (nof_eq_ctqpr5 : is_overflow = 1 ∨ ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4 = b_neg * 65535)
  (nof_eq_ctqpr6 : is_overflow = 1 ∨ ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5 = b_neg * 65535)
  (nof_eq_ctqpr7 : is_overflow = 1 ∨ ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6 = b_neg * 65535)
  (u16_ctqpr0 : (ctq0 + r0 - cry0 * 65536).val < 65536)
  (u16_ctqpr1 : (ctq1 + r1 - cry1 * 65536 + cry0).val < 65536)
  (u16_ctqpr2 : (ctq2 + rbc2 - cry2 * 65536 + cry1).val < 65536)
  (u16_ctqpr3 : (ctq3 + rbc3 - cry3 * 65536 + cry2).val < 65536)
  (u16_ctqpr4 : (ctq4 + rem_neg * 65535 - cry4 * 65536 + cry3).val < 65536)
  (u16_ctqpr5 : (ctq5 + rem_neg * 65535 - cry5 * 65536 + cry4).val < 65536)
  (u16_ctqpr6 : (ctq6 + rem_neg * 65535 - cry6 * 65536 + cry5).val < 65536)
  (u16_ctqpr7 : (ctq7 + rem_neg * 65535 - cry7 * 65536 + cry6).val < 65536)
  (eq_d_a0 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a0 = q0)
  (eq_r_a0 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a0 = r0)
  (eq_d_a1 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a1 = q1)
  (eq_r_a1 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a1 = r1)
  (eq_d_a2 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a2 = q2)
  (eq_r_a2 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a2 = r2)
  (eq_d_a3 : is_divu + is_div + is_divw + is_divuw = 0 ∨ a3 = q3)
  (eq_r_a3 : is_remu + is_rem + is_remw + is_remuw = 0 ∨ a3 = r3)
  (r_neg_b_neg : rem_neg = 0 ∨ b_neg = 1)
  (r_pos_b_pos : r0 + r1 + r2 + r3 = 0 ∨ rem_neg = 1 ∨ b_neg = 0)
  (c0_eq_q0 : is_c_0 = 0 ∨ q0 = 65535)
  (c0_eq_q1 : is_c_0 = 0 ∨ q1 = 65535)
  (c0_eq_q2 : is_c_0 = 0 ∨ q2 = 65535)
  (c0_eq_q3 : is_c_0 = 0 ∨ q3 = 65535)
  (c0_eq_r0 : is_c_0 = 0 ∨ r0 = b0)
  (c0_eq_r1 : is_c_0 = 0 ∨ r1 = b1)
  (c0_eq_r2 : is_c_0 = 0 ∨ rbc2 = b2 * (1 - is_word) + b_neg * is_word * 65535)
  (c0_eq_r3 : is_c_0 = 0 ∨ rbc3 = b3 * (1 - is_word) + b_neg * is_word * 65535)
  (cn_ac0 : c_neg = 1 ∨ ac0 = c0)
  (rn_ar0 : rem_neg = 1 ∨ ar0 = r0)
  (cn_ac1 : c_neg = 1 ∨ ac1 = c1)
  (rn_ar1 : rem_neg = 1 ∨ ar1 = r1)
  (cn_ac2 : c_neg = 1 ∨ ac2 = c2 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar2 : rem_neg = 1 ∨ ar2 = rbc2)
  (cn_ac3 : c_neg = 1 ∨ ac3 = c3 * (1 - is_word) + c_neg * is_word * 65535)
  (rn_ar3 : rem_neg = 1 ∨ ar3 = rbc3)
  (u16_ac0 : ac0.val < 65536)
  (u16_ac1 : ac1.val < 65536)
  (u16_ac2 : ac2.val < 65536)
  (u16_ac3 : ac3.val < 65536)
  (eq_cnop0 : c_neg = 0 ∨ cnop0 = 0)
  (eq_cnop1 : c_neg = 0 ∨ cnop1 = 0)
  (eq_cnop2 : c_neg = 0 ∨ cnop2 = 0)
  (eq_cnop3 : c_neg = 0 ∨ cnop3 = 0)
  (u16_ar0 : ar0.val < 65536)
  (u16_ar1 : ar1.val < 65536)
  (u16_ar2 : ar2.val < 65536)
  (u16_ar3 : ar3.val < 65536)
  (eq_rnop0 : rem_neg = 0 ∨ rnop0 = 0)
  (eq_rnop1 : rem_neg = 0 ∨ rnop1 = 0)
  (eq_rnop2 : rem_neg = 0 ∨ rnop2 = 0)
  (eq_rnop3 : rem_neg = 0 ∨ rnop3 = 0)
  (eq_abs_c_alu_event : abs_c_alu_event = c_neg)
  (eq_abs_rem_alu_event : abs_rem_alu_event = rem_neg)
  (eq_maco10 : maco10 = is_c_0 + (1 - is_c_0) * ac0)
  (eq_maco11 : maco11 = (1 - is_c_0) * ac1)
  (eq_maco12 : maco12 = (1 - is_c_0) * ac2)
  (eq_maco13 : maco13 = (1 - is_c_0) * ac3)
  (eq_arlt : is_c_0 = 1 ∨ arlt = 1)
  (u16_q0 : q0.val < 65536)
  (u16_q1 : q1.val < 65536)
  (u16_q2 : q2.val < 65536)
  (u16_q3 : q3.val < 65536)
  (u16_r0 : r0.val < 65536)
  (u16_r1 : r1.val < 65536)
  (u16_r2 : r2.val < 65536)
  (u16_r3 : r3.val < 65536)
  (b_cry0 : cry0 = 0 ∨ cry0 = 1)
  (b_cry1 : cry1 = 0 ∨ cry1 = 1)
  (b_cry2 : cry2 = 0 ∨ cry2 = 1)
  (b_cry3 : cry3 = 0 ∨ cry3 = 1)
  (b_cry4 : cry4 = 0 ∨ cry4 = 1)
  (b_cry5 : cry5 = 0 ∨ cry5 = 1)
  (b_cry6 : cry6 = 0 ∨ cry6 = 1)
  (b_cry7 : cry7 = 0 ∨ cry7 = 1)
  (u16_ctq0 : ctq0.val < 65536)
  (u16_ctq1 : ctq1.val < 65536)
  (u16_ctq2 : ctq2.val < 65536)
  (u16_ctq3 : ctq3.val < 65536)
  (u16_ctq4 : ctq4.val < 65536)
  (u16_ctq5 : ctq5.val < 65536)
  (u16_ctq6 : ctq6.val < 65536)
  (u16_ctq7 : ctq7.val < 65536)
  (b_is_div : is_div = 0 ∨ is_div = 1)
  (b_is_divu : is_divu = 0 ∨ is_divu = 1)
  (b_is_rem : is_rem = 0 ∨ is_rem = 1)
  (b_is_remu : is_remu = 0 ∨ is_remu = 1)
  (b_is_divw : is_divw = 0 ∨ is_divw = 1)
  (b_is_remw : is_remw = 0 ∨ is_remw = 1)
  (b_is_divuw : is_divuw = 0 ∨ is_divuw = 1)
  (b_is_remuw : is_remuw = 0 ∨ is_remuw = 1)
  (b_is_overflow : is_overflow = 0 ∨ is_overflow = 1)
  (b_is_real_not_word : is_word = 0 ∨ is_word = 1)
  (b_b_neg : b_neg = 0 ∨ b_neg = 1)
  (b_b_neg_not_overflow : b_neg_not_overflow = 0 ∨ b_neg_not_overflow = 1)
  (b_b_not_neg_not_overflow : b_not_neg_not_overflow = 0 ∨ b_not_neg_not_overflow = 1)
  (b_rem_neg : rem_neg = 0 ∨ rem_neg = 1)
  (b_c_neg : c_neg = 0 ∨ c_neg = 1)
  (b_one_of_ops : is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)
  (w_overflow_b : is_word = 1 → is_overflow_b = if #v[b0, b1, 0, 0] = #v[0, 32768, 0, 0] then 1 else 0)
  (w_overflow_c : is_word = 1 → is_overflow_c = if #v[c0, c1, 0, 0] = #v[65535, 65535, 0, 0] then 1 else 0)
  (div_zero : is_c_0 = if #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] = #v[0, 0, 0, 0] then 1 else 0)
  (c_neg_sum_zero : c_neg = 1 → Word.isU64 #v[cnop0, cnop1, cnop2, cnop3] ∧ Word.toBitVec64 #v[cnop0, cnop1, cnop2, cnop3] = Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535] + Word.toBitVec64 #v[ac0, ac1, ac2, ac3])
  (rem_neg_sum_zero : rem_neg = 1 → Word.isU64 #v[rnop0, rnop1, rnop2, rnop3] ∧ Word.toBitVec64 #v[rnop0, rnop1, rnop2, rnop3] = Word.toBitVec64 #v[r0, r1, rbc2, rbc3] + Word.toBitVec64 #v[ar0, ar1, ar2, ar3])
  (main_mul_low : Word.isU64 #v[ctq0, ctq1, ctq2, ctq3] ∧ Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MUL)
  (main_mul_high : is_word = 0 → (is_div + is_rem = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULH) ∧ (is_divu + is_remu = 1 → Word.isU64 #v[ctq4, ctq5, ctq6, ctq7] ∧ Word.toBitVec64 #v[ctq4, ctq5, ctq6, ctq7] = execute_MUL_pure (Word.toBitVec64 #v[q0, q1, qbc2, qbc3]) (Word.toBitVec64 #v[c0, c1, c2 * (1 - is_word) + c_neg * is_word * 65535, c3 * (1 - is_word) + c_neg * is_word * 65535]) mop.MULHU))
  (overflow_b : is_word = 0 → is_overflow_b = if #v[b0, b1, b2, b3] = #v[0, 0, 0, 32768] then 1 else 0)
  (overflow_c : is_word = 0 → is_overflow_c = if #v[c0, c1, c2, c3] = #v[65535, 65535, 65535, 65535] then 1 else 0)
  (eq_msb_b : is_word = 0 → msb_b = if 32768 ≤ b3 then 1 else 0)
  (eq_msb_c : is_word = 0 → msb_c = if 32768 ≤ c3 then 1 else 0)
  (eq_msb_rem : is_word = 0 → msb_rem = if 32768 ≤ r3 then 1 else 0)
  (w_eq_msb_b : is_word = 1 → msb_b = if 32768 ≤ b1 then 1 else 0)
  (w_eq_msb_c : is_word = 1 → msb_c = if 32768 ≤ c1 then 1 else 0)
  (w_eq_msb_rem : is_word = 1 → msb_rem = if 32768 ≤ r1 then 1 else 0)
  (w_eq_msb_quot : is_word = 1 → msb_quot = if 32768 ≤ q1 then 1 else 0)
  (abs_check : is_c_0 = 0 → arlt = if Word.toNat #v[ar0, ar1, ar2, ar3] < Word.toNat #v[is_c_0 + (1 - is_c_0) * ac0, (1 - is_c_0) * ac1, (1 - is_c_0) * ac2, (1 - is_c_0) * ac3] then 1 else 0) :
    is_divuw + is_remuw = 1 →
    ⟨ Word.toBitVec64 #v[q0, q1, q2, q3], Word.toBitVec64 #v[r0, r1, r2, r3]⟩ = execute_DIV_REM_pure (Word.toBitVec64 #v[b0, b1, b2, b3]) (Word.toBitVec64 #v[c0, c1, c2, c3]) .DRWU
      := by
    intro divuw_remuw
    obtain ⟨ z_div, z_rem, z_divu, z_remu, z_divw, z_remw ⟩ : is_div = 0 ∧ is_rem = 0 ∧ is_divu = 0 ∧ is_remu = 0 ∧ is_divw = 0 ∧ is_remw = 0 := by
      clear *- divuw_remuw sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_one_of_ops
      rcases b_is_divuw <;> rcases b_is_remuw <;> simp_all
    simp [z_div, z_rem, z_divu, z_remu, z_divw, z_remw, divuw_remuw] at *
    simp [eq_is_word] at *
    subst lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 abs_c_alu_event abs_rem_alu_event b_neg rem_neg c_neg
    simp [eq_is_overflow] at *
    subst ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 b_neg_not_overflow b_not_neg_not_overflow; simp at *
    subst maco12 maco13
    simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, Bool.cond_eq_ite, -BitVec.toNat_setWidth]
    rw [Word.setWidth_eq_low is_U64_b, Word.setWidth_eq_low is_U64_c]
    have is_U32_bl := Word.isU64_low_isU32 is_U64_b
    have is_U32_cl := Word.isU64_low_isU32 is_U64_c
    simp [Word.low] at *
    rw [HWord.toBitVec32_toNat is_U32_bl, HWord.toBitVec32_toNat is_U32_cl]
    have ext_q : #v[q0, q1, q2, q3] = HWord.extend #v[q0, q1] true := by simp [HWord.extend, HWord.isNegative]; subst q2 q3 msb_quot; split_ifs <;> simp
    have ext_r : #v[r0, r1, r2, r3] = HWord.extend #v[r0, r1] true := by simp [HWord.extend, HWord.isNegative]; subst r2 r3 msb_rem; split_ifs <;> simp
    rw [ext_q, ext_r]
    repeat rw [HWord.extend_true_is_signExtend (by apply HWord.isU32_of_cases <;> simpa)]
    suffices :
      HWord.toBitVec32 #v[q0, q1] = BitVec.ofNat 32 (if HWord.toNat #v[c0, c1] = 0 then (18446744073709551615 : ℤ) else (HWord.toNat #v[b0, b1]) / (HWord.toNat #v[c0, c1])).toNat ∧
      HWord.toBitVec32 #v[r0, r1] = BitVec.ofNat 32 (((HWord.toNat #v[b0, b1]) : ℤ).tmod ↑(HWord.toNat #v[c0, c1])).toNat
    . split_ands <;> congr 1 <;> [ exact this.1; exact this.2 ]
    . split_ifs at div_zero with nzc <;> simp [div_zero] at *
      . obtain ⟨zc0, zc1⟩ := nzc
        subst c0 c1 q0 q1 q2 q3 r0 r1 r2 r3
        simp [HWord.toBitVec32, HWord.toNat]
        congr
      . subst arlt maco10 maco11 is_c_0; simp at *
        rw [if_neg]; rotate_left
        . intro zc; simp [HWord.toNat] at zc; omega
        . have is_U32_r : HWord.isU32 #v[r0, r1] := by apply HWord.isU32_of_cases <;> simp <;> [ exact u16_r0; exact u16_r1 ]
          have is_U32_q : HWord.isU32 #v[q0, q1] := by apply HWord.isU32_of_cases <;> simp <;> [ exact u16_q0; exact u16_q1 ]
          suffices :
            HWord.toNat #v[q0, q1] = (((HWord.toNat #v[b0, b1]) : ℤ).tdiv (HWord.toNat #v[c0, c1])).toNat ∧
            HWord.toNat #v[r0, r1] = (((HWord.toNat #v[b0, b1]) : ℤ).tmod (HWord.toNat #v[c0, c1])).toNat
          . obtain ⟨ hdiv, hrem ⟩ := this
            simp at hdiv; rw [← hdiv, ← hrem]
            simp [← BitVec.toNat_inj]
            rw [HWord.toBitVec32_toNat is_U32_q, HWord.toBitVec32_toNat is_U32_r]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_lt_of_isU32 is_U32_q)]
            rw [Nat.mod_eq_of_lt (by apply HWord.toNat_lt_of_isU32 is_U32_r)]
            simp
          . have cnz : HWord.toNat #v[c0, c1] ≠ 0 := by
              intro zc; simp [HWord.toNat] at zc; omega
            rw [tdiv_tmod_unique_full_nat cnz]
            split_ands <;> [ skip; (simp [HWord.toNat]; simp [Word.toNat] at abs_check; exact abs_check) ]
            have is_U32_b : HWord.isU32 #v[b0, b1] := by apply Word.lt_cases_of_isU64 at is_U64_b; clear *- is_U64_b; apply HWord.isU32_of_cases <;> tauto
            have is_U32_c : HWord.isU32 #v[c0, c1] := by apply Word.lt_cases_of_isU64 at is_U64_c; clear *- is_U64_c; apply HWord.isU32_of_cases <;> tauto
            clear *- is_U32_b is_U32_c is_U32_q is_U32_r
                     u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 b_cry0 b_cry1 b_cry2 b_cry3
                     eq_msb_b eq_msb_c eq_msb_rem r_neg_b_neg r_pos_b_pos
                     nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
                     main_mul_low
            obtain ⟨ is_U64_ctql, ctq_low ⟩ := main_mul_low
            have eq_eb : (#v[b0, b1, 0, 0] : Word (Fin KB)) = HWord.extend #v[b0, b1] false := by simp [HWord.extend]
            have eq_er : (#v[r0, r1, 0, 0] : Word (Fin KB)) = HWord.extend #v[r0, r1] false := by simp [HWord.extend]
            suffices bv_ctqr:
              Word.toBitVec64 #v[b0, b1, 0, 0] =
                Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3] +
                Word.toBitVec64 #v[r0, r1, 0, 0]
            . have := HWord.toNat_lt_of_isU32 is_U32_b
              have := HWord.toNat_lt_of_isU32 is_U32_q
              have := HWord.toNat_lt_of_isU32 is_U32_c
              have := HWord.toNat_lt_of_isU32 is_U32_r
              trans (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat
              . rw [Word.low_toNat is_U32_b]
              . have : (Word.toBitVec64 #v[ctq0, ctq1, ctq2, ctq3]).toNat = HWord.toNat #v[q0, q1] * HWord.toNat #v[c0, c1] := by
                  simp only [ctq_low, execute_MUL_pure, ↓reduceIte, reduceCtorEq, or_self]
                  simp only [BitVec.extend, ↓reduceIte]
                  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
                  rw [Nat.shiftRight_zero, BitVec.toNat_mul]
                  simp [Word.low_toNat is_U32_q, Word.low_toNat is_U32_c]
                  nlinarith
                rw [bv_ctqr, BitVec.toNat_add, this, Word.low_toNat is_U32_r]
                simp; nlinarith
            . clear is_U32_c eq_msb_b eq_msb_c eq_msb_rem ctq_low eq_is_word r_neg_b_neg r_pos_b_pos eq_eb eq_er
              apply HWord.lt_cases_of_isU32 at is_U32_b
              apply HWord.lt_cases_of_isU32 at is_U32_r
              apply HWord.lt_cases_of_isU32 at is_U32_q
              apply Word.lt_cases_of_isU64 at is_U64_ctql
              simp at *
              rw [← add_sub_right_comm] at u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
              rw [div_mod_decomposition_w (by omega) (by omega)] at nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3
              trans Word.toBitVec64 #v[b0, b1, (ctq2 + cry1) % 65536, (ctq3 + cry2) % 65536]
              . rw [← nof_eq_ctqpr2.1, ← nof_eq_ctqpr3.1]
              . conv => lhs; simp [Word.toBitVec64, Word.toNat]
                        simp [nof_eq_ctqpr0.1, nof_eq_ctqpr1.1]
                        simp [nof_eq_ctqpr0.2, nof_eq_ctqpr1.2, nof_eq_ctqpr2.2, nof_eq_ctqpr3.2]
                simp [Fin.val_add]
                iterate 4 rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
                have joins : forall (i : Fin 4) (a b : ℕ), a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) = (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
                  clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
                have divs : forall (i : Fin 4) (a b : ℕ), (a + b / (65536 ^ i.val)) / 65536 = (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
                  clear *-; intro i a b; fin_cases i <;> norm_num <;> omega

                have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
                have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
                simp at *

                rw [j1, d1, j2, d2, j3]
                clear j1 j2 j3 d1 d2 d3 joins divs

                simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
                repeat rw [BitVec.toNat_add]
                iterate 2 rw [Word.toBitVec64_toNat (by apply Word.isU64_of_cases <;> simp <;> omega)]
                simp [Word.toNat]; ring_nf

set_option maxRecDepth 1000000 in
lemma spec.divuw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_divuw Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).1
  := by
  intro cstrs h_is_real h_is_divuw
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_divuw] at h_is_divuw

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_divuw]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divuw_remuw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop7 h_is_divuw
    simp [h_is_divuw, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_d_a0, eq_d_a1, eq_d_a2, eq_d_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega

set_option maxRecDepth 1000000 in
lemma spec.remuw :
  List.Forall SP1Constraint.toProp (constraints Main) →
    is_real Main → is_remuw Main →
      Word.toBitVec64 #v[Main[29], Main[30], Main[31], Main[32]] = (execute_DIV_REM_pure (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) (Word.toBitVec64 #v[Main[22], Main[23], Main[24], Main[25]]) .DRWU).2
  := by
  intro cstrs h_is_real h_is_remuw
  have ⟨ sop1, sop2, sop3, sop4, sop5, sop6, sop7, sop8 ⟩ := single_op Main cstrs
  have ⟨ is_U64_b, is_U64_c ⟩ := ops_U64_b_c Main cstrs h_is_real
  replace cstrs := (allHold_constraints_iff Main).mp cstrs; simp at h_is_real
  simp [is_remuw] at h_is_remuw

  set a0 := Main[29]
  set a1 := Main[30]
  set a2 := Main[31]
  set a3 := Main[32]

  set b0 := Main[15]
  set b1 := Main[16]
  set b2 := Main[17]
  set b3 := Main[18]

  set c0 := Main[22]
  set c1 := Main[23]
  set c2 := Main[24]
  set c3 := Main[25]

  set lb0 := Main[33]
  set lb1 := Main[34]
  set lb2 := Main[35]
  set lb3 := Main[36]

  set lc0 := Main[37]
  set lc1 := Main[38]
  set lc2 := Main[39]
  set lc3 := Main[40]

  set q0 := Main[41]
  set q1 := Main[42]
  set q2 := Main[43]
  set q3 := Main[44]

  set qbc0 := Main[45]
  set qbc1 := Main[46]
  set qbc2 := Main[47]
  set qbc3 := Main[48]

  set rbc0 := Main[49]
  set rbc1 := Main[50]
  set rbc2 := Main[51]
  set rbc3 := Main[52]

  set r0 := Main[53]
  set r1 := Main[54]
  set r2 := Main[55]
  set r3 := Main[56]

  set ar0 := Main[57]
  set ar1 := Main[58]
  set ar2 := Main[59]
  set ar3 := Main[60]

  set ac0 := Main[61]
  set ac1 := Main[62]
  set ac2 := Main[63]
  set ac3 := Main[64]

  set maco10 := Main[65]
  set maco11 := Main[66]
  set maco12 := Main[67]
  set maco13 := Main[68]

  set ctq0 := Main[69]
  set ctq1 := Main[70]
  set ctq2 := Main[71]
  set ctq3 := Main[72]
  set ctq4 := Main[73]
  set ctq5 := Main[74]
  set ctq6 := Main[75]
  set ctq7 := Main[76]

  set cnop0 := Main[167]
  set cnop1 := Main[168]
  set cnop2 := Main[169]
  set cnop3 := Main[170]

  set rnop0 := Main[171]
  set rnop1 := Main[172]
  set rnop2 := Main[173]
  set rnop3 := Main[174]

  set arlt := Main[175]

  set cry0 := Main[183]
  set cry1 := Main[184]
  set cry2 := Main[185]
  set cry3 := Main[186]
  set cry4 := Main[187]
  set cry5 := Main[188]
  set cry6 := Main[189]
  set cry7 := Main[190]

  set is_c_0 := Main[201]

  set is_div := Main[202]
  set is_divu := Main[203]
  set is_rem := Main[204]
  set is_remu := Main[205]
  set is_divw := Main[206]
  set is_remw := Main[207]
  set is_divuw := Main[208]
  set is_remuw := Main[209]

  set is_overflow := Main[210]
  set is_overflow_b := Main[221]
  set is_overflow_c := Main[232]

  set msb_b := Main[233]
  set msb_rem := Main[234]
  set msb_c := Main[235]
  set msb_quot := Main[236]
  set b_neg := Main[237]
  set b_neg_not_overflow := Main[238]
  set b_not_neg_not_overflow := Main[239]
  set is_real_not_word := Main[240]
  set rem_neg := Main[241]
  set c_neg := Main[242]
  set abs_c_alu_event := Main[243]
  set abs_rem_alu_event := Main[244]
  set is_real := Main[245]
  set remainder_check_multiplicity := Main[246]

  obtain ⟨ main_mul_low, main_mul_high,
           overflow_b, overflow_c, w_overflow_b, w_overflow_c,
           div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
           eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
           cpu, alu,
           eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
           eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
           eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
           eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
           eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
           of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
           nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
           nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
           u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
           rest2 ⟩ := cstrs
  obtain ⟨ eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
           r_neg_b_neg, r_pos_b_pos,
           c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
           cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
           u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
           u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
           eq_abs_c_alu_event, eq_abs_rem_alu_event,
           eq_maco10, eq_maco11, eq_maco12, eq_maco13,
           eq_rcm, eq_arlt,
           rest3 ⟩ := rest2
  obtain ⟨ u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
           b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
           u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7, rest4 ⟩ := rest3
  obtain ⟨
           b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
           b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
           b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops ⟩ := rest4
  clear cpu alu
  symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
  rw [eq_comm (a := b_neg * ↑(65535 : ℕ))] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
  rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
  rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
  rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
  rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
  rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
  rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
  rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
  rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
  simp_all [-h_is_remuw]

  apply MulOperation.spec.mul at main_mul_low
  apply MulOperation.spec.mulh.gen at main_mul_high
  apply IsEqualWordOperation.spec.gen at overflow_b
  apply IsEqualWordOperation.spec.gen at overflow_c
  apply IsEqualWordOperation.spec.gen at w_overflow_b
  apply IsEqualWordOperation.spec.gen at w_overflow_c
  apply IsZeroWordOperation.spec at div_zero
  apply U16MSBOperation.spec.gen at eq_msb_b
  apply U16MSBOperation.spec.gen at eq_msb_c
  apply U16MSBOperation.spec.gen at eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_b
  apply U16MSBOperation.spec.gen at w_eq_msb_c
  apply U16MSBOperation.spec.gen at w_eq_msb_rem
  apply U16MSBOperation.spec.gen at w_eq_msb_quot
  apply AddOperation.spec.gen at c_neg_sum_zero
  apply AddOperation.spec.gen at rem_neg_sum_zero
  apply LtOperationUnsigned.spec.nat.gen at abs_check

  simp [-Vector.eq_mk, -Vector.mk_eq, -Vector.mk.injEq]
    at main_mul_low main_mul_high overflow_b overflow_c w_overflow_b w_overflow_c div_zero eq_msb_b eq_msb_c
       eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot
       c_neg_sum_zero rem_neg_sum_zero abs_check

  set is_word := is_divw + is_remw + is_divuw + is_remuw
  have eq_is_word : is_word = is_divw + is_remw + is_divuw + is_remuw := by subst is_word; rfl

  have := divuw_remuw a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 lb0 lb1 lb2 lb3 lc0 lc1 lc2 lc3 q0 q1 q2 q3 qbc0 qbc1 qbc2 qbc3 rbc0 rbc1 rbc2 rbc3 r0 r1 r2 r3 ar0 ar1 ar2 ar3 ac0 ac1 ac2 ac3 maco10 maco11 maco12 maco13 ctq0 ctq1 ctq2 ctq3 ctq4 ctq5 ctq6 ctq7 cnop0 cnop1 cnop2 cnop3 rnop0 rnop1 rnop2 rnop3 arlt cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c msb_b msb_rem msb_c msb_quot b_neg b_neg_not_overflow b_not_neg_not_overflow is_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_U64_b is_U64_c sop1 sop2 sop3 sop4 sop5 sop6 sop7 sop8 eq_is_word eq_b_neg eq_rem_neg eq_c_neg
  simp only [eq_b_neg, eq_c_neg, eq_rem_neg] at *
  specialize this eq_lb0 eq_lc0 eq_lb1 eq_lc1 eq_lb2 eq_lc2 eq_lb3 eq_lc3 eq_qbc0 eq_qbc1 w_eq_qbc2_uw w_eq_qbc2_w w_eq_q2_w eq_qbc2 w_eq_qbc3_uw w_eq_qbc3_w w_eq_q3_w eq_qbc3 eq_rbc0 eq_rbc1 w_eq_rbc2_uw w_eq_rbc2_w w_eq_r2_w eq_rbc2 w_eq_rbc3_uw w_eq_rbc3_w w_eq_r3_w eq_rbc3 eq_is_overflow
  simp only [eq_is_overflow] at *
  specialize this eq_b_neg_not_overflow eq_not_b_neg_not_overflow of_eq_q0 of_eq_r0 of_eq_q1 of_eq_r1 of_eq_q2 of_eq_r2 of_eq_q3 of_eq_r3 nof_eq_ctqpr0 nof_eq_ctqpr1 nof_eq_ctqpr2 nof_eq_ctqpr3 nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7 u16_ctqpr0 u16_ctqpr1 u16_ctqpr2 u16_ctqpr3 u16_ctqpr4 u16_ctqpr5 u16_ctqpr6 u16_ctqpr7 eq_d_a0 eq_r_a0 eq_d_a1 eq_r_a1 eq_d_a2 eq_r_a2 eq_d_a3 eq_r_a3 r_neg_b_neg r_pos_b_pos c0_eq_q0 c0_eq_q1 c0_eq_q2 c0_eq_q3 c0_eq_r0 c0_eq_r1 c0_eq_r2 c0_eq_r3 cn_ac0 rn_ar0 cn_ac1 rn_ar1 cn_ac2 rn_ar2 cn_ac3 rn_ar3 u16_ac0 u16_ac1 u16_ac2 u16_ac3 eq_cnop0 eq_cnop1 eq_cnop2 eq_cnop3 u16_ar0 u16_ar1 u16_ar2 u16_ar3 eq_rnop0 eq_rnop1 eq_rnop2 eq_rnop3 eq_abs_c_alu_event eq_abs_rem_alu_event eq_maco10 eq_maco11 eq_maco12 eq_maco13
  have eq_arlt' : is_c_0 = 1 ∨ arlt = 1 := by clear *- eq_arlt div_zero; split_ifs at div_zero <;> simp_all
  have b_is_real_not_word' : is_word = 0 ∨ is_word = 1 := by clear *- b_is_real_not_word; rcases b_is_real_not_word <;> [ omega; simp_all ]
  specialize this eq_arlt' u16_q0 u16_q1 u16_q2 u16_q3 u16_r0 u16_r1 u16_r2 u16_r3 b_cry0 b_cry1 b_cry2 b_cry3 b_cry4 b_cry5 b_cry6 b_cry7 u16_ctq0 u16_ctq1 u16_ctq2 u16_ctq3 u16_ctq4 u16_ctq5 u16_ctq6 u16_ctq7 b_is_div b_is_divu b_is_rem b_is_remu b_is_divw b_is_remw b_is_divuw b_is_remuw b_is_overflow b_is_real_not_word' b_b_neg
  simp only [eq_b_neg_not_overflow, eq_not_b_neg_not_overflow] at *
  specialize this b_b_neg_not_overflow b_b_not_neg_not_overflow b_rem_neg b_c_neg b_one_of_ops w_overflow_b w_overflow_c
  simp only [eq_is_word] at *
  specialize this div_zero c_neg_sum_zero rem_neg_sum_zero main_mul_low main_mul_high overflow_b overflow_c eq_msb_b eq_msb_c eq_msb_rem w_eq_msb_b w_eq_msb_c w_eq_msb_rem w_eq_msb_quot abs_check

  all_goals
    obtain ⟨ z0, z1, z2, z3, z4, z5, z6 ⟩ := sop8 h_is_remuw
    simp [h_is_remuw, z0, z1, z2, z3, z4, z5, z6] at *

  . rw [← this, eq_r_a0, eq_r_a1, eq_r_a2, eq_r_a3]
  . apply Word.isU64_of_cases <;> simp <;> omega
  . split_ifs at div_zero <;> simp [div_zero] <;> apply Word.isU64_of_cases <;> simp <;> assumption
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . rw [Fin.lt_def]; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . rw [Fin.lt_def]; omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; simp at is_U64_c; omega
  . apply Word.lt_cases_of_isU64 at is_U64_b; simp at is_U64_b; omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega
  . apply Word.isU64_of_cases <;> simp <;> omega
  . apply Word.lt_cases_of_isU64 at is_U64_c; apply Word.isU64_of_cases <;> simp at is_U64_c ⊢ <;> omega

end divuw_remuw

end DivRem
