import SP1Operations.Operation.MulOperation
import SP1Operations.Operation.AddOperation
import SP1Operations.Compare.IsEqualWordOperation
import SP1Operations.Compare.IsZeroWordOperation
import SP1Operations.Compare.LtOperationUnsigned
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader

namespace DivRem

set_option maxHeartbeats 100000000

variable (Main : Vector (Fin BB) 251)

section constraints

-- Generated Lean code for chip DivRemChip
def constraints : SP1ConstraintList :=
  let E0 : Fin BB := Main[209] + Main[210]
  let E1 : Fin BB := E0 + Main[211]
  let E2 : Fin BB := E1 + Main[212]
  let E3 : Fin BB := Main[206] + Main[208]
  let E4 : Fin BB := E3 + Main[205]
  let E5 : Fin BB := E4 + Main[207]
  let E6 : Fin BB := Main[209] + Main[210]
  let E7 : Fin BB := Main[211] + Main[212]
  let E8 : Fin BB := Main[205] + Main[207]
  let E9 : Fin BB := E8 + Main[209]
  let E10 : Fin BB := E9 + Main[210]
  let E11 : Fin BB := 1 - E2
  let E12 : Fin BB := Main[249] * E11
  let E13 : Fin BB := Main[244] - E12
  let E14 : Fin BB := Main[237] * E10
  let E15 : Fin BB := E14 - Main[241]
  let E16 : Fin BB := Main[238] * E10
  let E17 : Fin BB := E16 - Main[245]
  let E18 : Fin BB := Main[239] * E10
  let E19 : Fin BB := E18 - Main[246]
  let E20 : Fin BB := Main[15] - Main[36]
  let E21 : Fin BB := Main[25] - Main[40]
  let E22 : Fin BB := Main[16] - Main[37]
  let E23 : Fin BB := Main[26] - Main[41]
  let E24 : Fin BB := 1 - E2
  let E25 : Fin BB := Main[17] * E24
  let E26 : Fin BB := Main[241] * E2
  let E27 : Fin BB := E26 * 65535
  let E28 : Fin BB := E25 + E27
  let E29 : Fin BB := Main[38] - E28
  let E30 : Fin BB := 1 - E2
  let E31 : Fin BB := Main[27] * E30
  let E32 : Fin BB := Main[246] * E2
  let E33 : Fin BB := E32 * 65535
  let E34 : Fin BB := E31 + E33
  let E35 : Fin BB := Main[42] - E34
  let E36 : Fin BB := 1 - E2
  let E37 : Fin BB := Main[18] * E36
  let E38 : Fin BB := Main[241] * E2
  let E39 : Fin BB := E38 * 65535
  let E40 : Fin BB := E37 + E39
  let E41 : Fin BB := Main[39] - E40
  let E42 : Fin BB := 1 - E2
  let E43 : Fin BB := Main[28] * E42
  let E44 : Fin BB := Main[246] * E2
  let E45 : Fin BB := E44 * 65535
  let E46 : Fin BB := E43 + E45
  let E47 : Fin BB := Main[43] - E46
  let E48 : Fin BB := Main[48] - Main[44]
  let E49 : Fin BB := Main[49] - Main[45]
  let E50 : Fin BB := Main[50] - 0
  let E51 : Fin BB := E7 * E50
  let E52 : Fin BB := Main[240] * 65535
  let E53 : Fin BB := Main[50] - E52
  let E54 : Fin BB := E6 * E53
  let E55 : Fin BB := Main[240] * 65535
  let E56 : Fin BB := Main[46] - E55
  let E57 : Fin BB := E2 * E56
  let E58 : Fin BB := Main[50] - Main[46]
  let E59 : Fin BB := E5 * E58
  let E60 : Fin BB := Main[51] - 0
  let E61 : Fin BB := E7 * E60
  let E62 : Fin BB := Main[240] * 65535
  let E63 : Fin BB := Main[51] - E62
  let E64 : Fin BB := E6 * E63
  let E65 : Fin BB := Main[240] * 65535
  let E66 : Fin BB := Main[47] - E65
  let E67 : Fin BB := E2 * E66
  let E68 : Fin BB := Main[51] - Main[47]
  let E69 : Fin BB := E5 * E68
  let E70 : Fin BB := Main[52] - Main[56]
  let E71 : Fin BB := Main[53] - Main[57]
  let E72 : Fin BB := Main[54] - 0
  let E73 : Fin BB := E7 * E72
  let E74 : Fin BB := Main[238] * 65535
  let E75 : Fin BB := Main[54] - E74
  let E76 : Fin BB := E6 * E75
  let E77 : Fin BB := Main[238] * 65535
  let E78 : Fin BB := Main[58] - E77
  let E79 : Fin BB := E2 * E78
  let E80 : Fin BB := Main[54] - Main[58]
  let E81 : Fin BB := E5 * E80
  let E82 : Fin BB := Main[55] - 0
  let E83 : Fin BB := E7 * E82
  let E84 : Fin BB := Main[238] * 65535
  let E85 : Fin BB := Main[55] - E84
  let E86 : Fin BB := E6 * E85
  let E87 : Fin BB := Main[238] * 65535
  let E88 : Fin BB := Main[59] - E87
  let E89 : Fin BB := E2 * E88
  let E90 : Fin BB := Main[55] - Main[59]
  let E91 : Fin BB := E5 * E90
  let CS0 : SP1ConstraintList := MulOperation.constraints #v[Main[72], Main[73], Main[74], Main[75]] #v[Main[48], Main[49], Main[50], Main[51]] #v[Main[40], Main[41], Main[42], Main[43]] { carry := #v[Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91], Main[92], Main[93], Main[94], Main[95]], product := #v[Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107], Main[108], Main[109], Main[110], Main[111]], b_lower_byte := { low_bytes := #v[Main[112], Main[113], Main[114], Main[115]] }, c_lower_byte := { low_bytes := #v[Main[116], Main[117], Main[118], Main[119]] }, b_msb := Main[120], c_msb := Main[121], product_msb := { msb := Main[122] }, b_sign_extend := Main[123], c_sign_extend := Main[124] } Main[249] Main[249] 0 0 0 0
  let E92 : Fin BB := Main[205] + Main[207]
  let E93 : Fin BB := Main[206] + Main[208]
  let CS1 : SP1ConstraintList := MulOperation.constraints #v[Main[76], Main[77], Main[78], Main[79]] #v[Main[48], Main[49], Main[50], Main[51]] #v[Main[40], Main[41], Main[42], Main[43]] { carry := #v[Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136], Main[137], Main[138], Main[139], Main[140]], product := #v[Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152], Main[153], Main[154], Main[155], Main[156]], b_lower_byte := { low_bytes := #v[Main[157], Main[158], Main[159], Main[160]] }, c_lower_byte := { low_bytes := #v[Main[161], Main[162], Main[163], Main[164]] }, b_msb := Main[165], c_msb := Main[166], product_msb := { msb := Main[167] }, b_sign_extend := Main[168], c_sign_extend := Main[169] } Main[244] 0 E92 0 E93 0
  let CS2 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[0, 0, 0, 32768] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }, { inverse := Main[219], result := Main[220] }, { inverse := Main[221], result := Main[222] }], is_zero_first_half := Main[223], is_zero_second_half := Main[224], result := Main[225] } } Main[244]
  let CS3 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[25], Main[26], Main[27], Main[28]] #v[65535, 65535, 65535, 65535] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }, { inverse := Main[230], result := Main[231] }, { inverse := Main[232], result := Main[233] }], is_zero_first_half := Main[234], is_zero_second_half := Main[235], result := Main[236] } } Main[244]
  let CS4 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[15], Main[16], 0, 0] #v[0, 32768, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }, { inverse := Main[219], result := Main[220] }, { inverse := Main[221], result := Main[222] }], is_zero_first_half := Main[223], is_zero_second_half := Main[224], result := Main[225] } } E2
  let CS5 : SP1ConstraintList := IsEqualWordOperation.constraints #v[Main[25], Main[26], 0, 0] #v[65535, 65535, 0, 0] { is_diff_zero := { is_zero_limb := #v[{ inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }, { inverse := Main[230], result := Main[231] }, { inverse := Main[232], result := Main[233] }], is_zero_first_half := Main[234], is_zero_second_half := Main[235], result := Main[236] } } E2
  let E94 : Fin BB := Main[225] * Main[236]
  let E95 : Fin BB := E94 * E10
  let E96 : Fin BB := Main[214] - E95
  let E97 : Fin BB := 1 - Main[214]
  let E98 : Fin BB := Main[241] * E97
  let E99 : Fin BB := Main[242] - E98
  let E100 : Fin BB := 1 - Main[241]
  let E101 : Fin BB := 1 - Main[214]
  let E102 : Fin BB := E100 * E101
  let E103 : Fin BB := Main[243] - E102
  let E104 : Fin BB := Main[44] - Main[36]
  let E105 : Fin BB := Main[214] * E104
  let E106 : Fin BB := Main[56] - 0
  let E107 : Fin BB := Main[214] * E106
  let E108 : Fin BB := Main[45] - Main[37]
  let E109 : Fin BB := Main[214] * E108
  let E110 : Fin BB := Main[57] - 0
  let E111 : Fin BB := Main[214] * E110
  let E112 : Fin BB := Main[46] - Main[38]
  let E113 : Fin BB := Main[214] * E112
  let E114 : Fin BB := Main[58] - 0
  let E115 : Fin BB := Main[214] * E114
  let E116 : Fin BB := Main[47] - Main[39]
  let E117 : Fin BB := Main[214] * E116
  let E118 : Fin BB := Main[59] - 0
  let E119 : Fin BB := Main[214] * E118
  let E120 : Fin BB := Main[245] * 65535
  let E121 : Fin BB := Main[72] + Main[52]
  let E122 : Fin BB := Main[186] * 65536
  let E123 : Fin BB := E121 - E122
  let E124 : Fin BB := Main[73] + Main[53]
  let E125 : Fin BB := Main[187] * 65536
  let E126 : Fin BB := E124 - E125
  let E127 : Fin BB := E126 + Main[186]
  let E128 : Fin BB := Main[74] + Main[54]
  let E129 : Fin BB := Main[188] * 65536
  let E130 : Fin BB := E128 - E129
  let E131 : Fin BB := E130 + Main[187]
  let E132 : Fin BB := Main[75] + Main[55]
  let E133 : Fin BB := Main[189] * 65536
  let E134 : Fin BB := E132 - E133
  let E135 : Fin BB := E134 + Main[188]
  let E136 : Fin BB := Main[76] + E120
  let E137 : Fin BB := Main[190] * 65536
  let E138 : Fin BB := E136 - E137
  let E139 : Fin BB := E138 + Main[189]
  let E140 : Fin BB := Main[77] + E120
  let E141 : Fin BB := Main[191] * 65536
  let E142 : Fin BB := E140 - E141
  let E143 : Fin BB := E142 + Main[190]
  let E144 : Fin BB := Main[78] + E120
  let E145 : Fin BB := Main[192] * 65536
  let E146 : Fin BB := E144 - E145
  let E147 : Fin BB := E146 + Main[191]
  let E148 : Fin BB := Main[79] + E120
  let E149 : Fin BB := Main[193] * 65536
  let E150 : Fin BB := E148 - E149
  let E151 : Fin BB := E150 + Main[192]
  let E152 : Fin BB := Main[214] - 1
  let E153 : Fin BB := Main[36] - E123
  let E154 : Fin BB := E152 * E153
  let E155 : Fin BB := Main[214] - 1
  let E156 : Fin BB := Main[37] - E127
  let E157 : Fin BB := E155 * E156
  let E158 : Fin BB := Main[214] - 1
  let E159 : Fin BB := Main[38] - E131
  let E160 : Fin BB := E158 * E159
  let E161 : Fin BB := Main[214] - 1
  let E162 : Fin BB := Main[39] - E135
  let E163 : Fin BB := E161 * E162
  let E164 : Fin BB := Main[214] - 1
  let E165 : Fin BB := Main[241] * 65535
  let E166 : Fin BB := E165 - E139
  let E167 : Fin BB := E164 * E166
  let E168 : Fin BB := Main[214] - 1
  let E169 : Fin BB := Main[241] * 65535
  let E170 : Fin BB := E169 - E143
  let E171 : Fin BB := E168 * E170
  let E172 : Fin BB := Main[214] - 1
  let E173 : Fin BB := Main[241] * 65535
  let E174 : Fin BB := E173 - E147
  let E175 : Fin BB := E172 * E174
  let E176 : Fin BB := Main[214] - 1
  let E177 : Fin BB := Main[241] * 65535
  let E178 : Fin BB := E177 - E151
  let E179 : Fin BB := E176 * E178
  let E180 : Fin BB := Main[206] + Main[205]
  let E181 : Fin BB := E180 + Main[209]
  let E182 : Fin BB := E181 + Main[211]
  let E183 : Fin BB := Main[44] - Main[32]
  let E184 : Fin BB := E182 * E183
  let E185 : Fin BB := Main[208] + Main[207]
  let E186 : Fin BB := E185 + Main[210]
  let E187 : Fin BB := E186 + Main[212]
  let E188 : Fin BB := Main[56] - Main[32]
  let E189 : Fin BB := E187 * E188
  let E190 : Fin BB := Main[206] + Main[205]
  let E191 : Fin BB := E190 + Main[209]
  let E192 : Fin BB := E191 + Main[211]
  let E193 : Fin BB := Main[45] - Main[33]
  let E194 : Fin BB := E192 * E193
  let E195 : Fin BB := Main[208] + Main[207]
  let E196 : Fin BB := E195 + Main[210]
  let E197 : Fin BB := E196 + Main[212]
  let E198 : Fin BB := Main[57] - Main[33]
  let E199 : Fin BB := E197 * E198
  let E200 : Fin BB := Main[206] + Main[205]
  let E201 : Fin BB := E200 + Main[209]
  let E202 : Fin BB := E201 + Main[211]
  let E203 : Fin BB := Main[46] - Main[34]
  let E204 : Fin BB := E202 * E203
  let E205 : Fin BB := Main[208] + Main[207]
  let E206 : Fin BB := E205 + Main[210]
  let E207 : Fin BB := E206 + Main[212]
  let E208 : Fin BB := Main[58] - Main[34]
  let E209 : Fin BB := E207 * E208
  let E210 : Fin BB := Main[206] + Main[205]
  let E211 : Fin BB := E210 + Main[209]
  let E212 : Fin BB := E211 + Main[211]
  let E213 : Fin BB := Main[47] - Main[35]
  let E214 : Fin BB := E212 * E213
  let E215 : Fin BB := Main[208] + Main[207]
  let E216 : Fin BB := E215 + Main[210]
  let E217 : Fin BB := E216 + Main[212]
  let E218 : Fin BB := Main[59] - Main[35]
  let E219 : Fin BB := E217 * E218
  let E220 : Fin BB := 0 + Main[56]
  let E221 : Fin BB := E220 + Main[57]
  let E222 : Fin BB := E221 + Main[58]
  let E223 : Fin BB := E222 + Main[59]
  let E224 : Fin BB := Main[241] - 1
  let E225 : Fin BB := Main[245] * E224
  let E226 : Fin BB := 1 - Main[245]
  let E227 : Fin BB := E226 * Main[241]
  let E228 : Fin BB := E223 * E227
  let CS6 : SP1ConstraintList := IsZeroWordOperation.constraints #v[Main[40], Main[41], Main[42], Main[43]] { is_zero_limb := #v[{ inverse := Main[194], result := Main[195] }, { inverse := Main[196], result := Main[197] }, { inverse := Main[198], result := Main[199] }, { inverse := Main[200], result := Main[201] }], is_zero_first_half := Main[202], is_zero_second_half := Main[203], result := Main[204] } Main[249]
  let E229 : Fin BB := Main[44] - 65535
  let E230 : Fin BB := Main[204] * E229
  let E231 : Fin BB := Main[45] - 65535
  let E232 : Fin BB := Main[204] * E231
  let E233 : Fin BB := Main[46] - 65535
  let E234 : Fin BB := Main[204] * E233
  let E235 : Fin BB := Main[47] - 65535
  let E236 : Fin BB := Main[204] * E235
  let E237 : Fin BB := Main[52] - Main[36]
  let E238 : Fin BB := Main[204] * E237
  let E239 : Fin BB := Main[53] - Main[37]
  let E240 : Fin BB := Main[204] * E239
  let E241 : Fin BB := Main[54] - Main[38]
  let E242 : Fin BB := Main[204] * E241
  let E243 : Fin BB := Main[55] - Main[39]
  let E244 : Fin BB := Main[204] * E243
  let E245 : Fin BB := Main[246] - 1
  let E246 : Fin BB := Main[40] - Main[64]
  let E247 : Fin BB := E245 * E246
  let E248 : Fin BB := Main[245] - 1
  let E249 : Fin BB := Main[52] - Main[60]
  let E250 : Fin BB := E248 * E249
  let E251 : Fin BB := Main[246] - 1
  let E252 : Fin BB := Main[41] - Main[65]
  let E253 : Fin BB := E251 * E252
  let E254 : Fin BB := Main[245] - 1
  let E255 : Fin BB := Main[53] - Main[61]
  let E256 : Fin BB := E254 * E255
  let E257 : Fin BB := Main[246] - 1
  let E258 : Fin BB := Main[42] - Main[66]
  let E259 : Fin BB := E257 * E258
  let E260 : Fin BB := Main[245] - 1
  let E261 : Fin BB := Main[54] - Main[62]
  let E262 : Fin BB := E260 * E261
  let E263 : Fin BB := Main[246] - 1
  let E264 : Fin BB := Main[43] - Main[67]
  let E265 : Fin BB := E263 * E264
  let E266 : Fin BB := Main[245] - 1
  let E267 : Fin BB := Main[55] - Main[63]
  let E268 : Fin BB := E266 * E267
  let CS7 : SP1ConstraintList := AddOperation.constraints #v[Main[40], Main[41], Main[42], Main[43]] #v[Main[64], Main[65], Main[66], Main[67]] { value := #v[Main[170], Main[171], Main[172], Main[173]] } Main[247]
  let E269 : Fin BB := 0 - Main[170]
  let E270 : Fin BB := Main[247] * E269
  let E271 : Fin BB := 0 - Main[171]
  let E272 : Fin BB := Main[247] * E271
  let E273 : Fin BB := 0 - Main[172]
  let E274 : Fin BB := Main[247] * E273
  let E275 : Fin BB := 0 - Main[173]
  let E276 : Fin BB := Main[247] * E275
  let CS8 : SP1ConstraintList := AddOperation.constraints #v[Main[52], Main[53], Main[54], Main[55]] #v[Main[60], Main[61], Main[62], Main[63]] { value := #v[Main[174], Main[175], Main[176], Main[177]] } Main[248]
  let E277 : Fin BB := 0 - Main[174]
  let E278 : Fin BB := Main[248] * E277
  let E279 : Fin BB := 0 - Main[175]
  let E280 : Fin BB := Main[248] * E279
  let E281 : Fin BB := 0 - Main[176]
  let E282 : Fin BB := Main[248] * E281
  let E283 : Fin BB := 0 - Main[177]
  let E284 : Fin BB := Main[248] * E283
  let E285 : Fin BB := Main[246] * Main[249]
  let E286 : Fin BB := Main[247] - E285
  let E287 : Fin BB := Main[245] * Main[249]
  let E288 : Fin BB := Main[248] - E287
  let E289 : Fin BB := Main[204] * 1
  let E290 : Fin BB := 1 - Main[204]
  let E291 : Fin BB := E290 * Main[64]
  let E292 : Fin BB := E289 + E291
  let E293 : Fin BB := 1 - Main[204]
  let E294 : Fin BB := E293 * Main[65]
  let E295 : Fin BB := 1 - Main[204]
  let E296 : Fin BB := E295 * Main[66]
  let E297 : Fin BB := 1 - Main[204]
  let E298 : Fin BB := E297 * Main[67]
  let E299 : Fin BB := Main[68] - E292
  let E300 : Fin BB := Main[69] - E294
  let E301 : Fin BB := Main[70] - E296
  let E302 : Fin BB := Main[71] - E298
  let E303 : Fin BB := 1 - Main[204]
  let E304 : Fin BB := E303 * Main[249]
  let E305 : Fin BB := E304 - Main[250]
  let CS9 : SP1ConstraintList := LtOperationUnsigned.constraints #v[Main[60], Main[61], Main[62], Main[63]] #v[Main[68], Main[69], Main[70], Main[71]] { u16_compare_operation := { bit := Main[178] }, u16_flags := #v[Main[179], Main[180], Main[181], Main[182]], not_eq_inv := Main[183], comparison_limbs := #v[Main[184], Main[185]] } Main[250]
  let E306 : Fin BB := 1 - Main[178]
  let E307 : Fin BB := Main[250] * E306
  let CS10 : SP1ConstraintList := U16MSBOperation.constraints Main[18] { msb := Main[237] } Main[244]
  let CS11 : SP1ConstraintList := U16MSBOperation.constraints Main[28] { msb := Main[239] } Main[244]
  let CS12 : SP1ConstraintList := U16MSBOperation.constraints Main[59] { msb := Main[238] } Main[244]
  let CS13 : SP1ConstraintList := U16MSBOperation.constraints Main[16] { msb := Main[237] } E2
  let CS14 : SP1ConstraintList := U16MSBOperation.constraints Main[26] { msb := Main[239] } E2
  let CS15 : SP1ConstraintList := U16MSBOperation.constraints Main[57] { msb := Main[238] } E2
  let CS16 : SP1ConstraintList := U16MSBOperation.constraints Main[45] { msb := Main[240] } E2
  let E308 : Fin BB := Main[186] - 1
  let E309 : Fin BB := Main[186] * E308
  let E310 : Fin BB := Main[187] - 1
  let E311 : Fin BB := Main[187] * E310
  let E312 : Fin BB := Main[188] - 1
  let E313 : Fin BB := Main[188] * E312
  let E314 : Fin BB := Main[189] - 1
  let E315 : Fin BB := Main[189] * E314
  let E316 : Fin BB := Main[190] - 1
  let E317 : Fin BB := Main[190] * E316
  let E318 : Fin BB := Main[191] - 1
  let E319 : Fin BB := Main[191] * E318
  let E320 : Fin BB := Main[192] - 1
  let E321 : Fin BB := Main[192] * E320
  let E322 : Fin BB := Main[193] - 1
  let E323 : Fin BB := Main[193] * E322
  let E324 : Fin BB := Main[205] - 1
  let E325 : Fin BB := Main[205] * E324
  let E326 : Fin BB := Main[206] - 1
  let E327 : Fin BB := Main[206] * E326
  let E328 : Fin BB := Main[207] - 1
  let E329 : Fin BB := Main[207] * E328
  let E330 : Fin BB := Main[208] - 1
  let E331 : Fin BB := Main[208] * E330
  let E332 : Fin BB := Main[209] - 1
  let E333 : Fin BB := Main[209] * E332
  let E334 : Fin BB := Main[210] - 1
  let E335 : Fin BB := Main[210] * E334
  let E336 : Fin BB := Main[211] - 1
  let E337 : Fin BB := Main[211] * E336
  let E338 : Fin BB := Main[212] - 1
  let E339 : Fin BB := Main[212] * E338
  let E340 : Fin BB := Main[214] - 1
  let E341 : Fin BB := Main[214] * E340
  let E342 : Fin BB := Main[244] - 1
  let E343 : Fin BB := Main[244] * E342
  let E344 : Fin BB := Main[241] - 1
  let E345 : Fin BB := Main[241] * E344
  let E346 : Fin BB := Main[242] - 1
  let E347 : Fin BB := Main[242] * E346
  let E348 : Fin BB := Main[243] - 1
  let E349 : Fin BB := Main[243] * E348
  let E350 : Fin BB := Main[245] - 1
  let E351 : Fin BB := Main[245] * E350
  let E352 : Fin BB := Main[246] - 1
  let E353 : Fin BB := Main[246] * E352
  let E354 : Fin BB := Main[249] - 1
  let E355 : Fin BB := Main[249] * E354
  let E356 : Fin BB := Main[247] - 1
  let E357 : Fin BB := Main[247] * E356
  let E358 : Fin BB := Main[248] - 1
  let E359 : Fin BB := Main[248] * E358
  let E360 : Fin BB := Main[206] + Main[208]
  let E361 : Fin BB := E360 + Main[205]
  let E362 : Fin BB := E361 + Main[207]
  let E363 : Fin BB := E362 + Main[209]
  let E364 : Fin BB := E363 + Main[210]
  let E365 : Fin BB := E364 + Main[211]
  let E366 : Fin BB := E365 + Main[212]
  let E367 : Fin BB := 1 - E366
  let E368 : Fin BB := Main[206] * 16
  let E369 : Fin BB := Main[208] * 18
  let E370 : Fin BB := E368 + E369
  let E371 : Fin BB := Main[205] * 15
  let E372 : Fin BB := E370 + E371
  let E373 : Fin BB := Main[207] * 17
  let E374 : Fin BB := E372 + E373
  let E375 : Fin BB := Main[209] * 48
  let E376 : Fin BB := E374 + E375
  let E377 : Fin BB := Main[210] * 50
  let E378 : Fin BB := E376 + E377
  let E379 : Fin BB := Main[211] * 49
  let E380 : Fin BB := E378 + E379
  let E381 : Fin BB := Main[212] * 51
  let E382 : Fin BB := E380 + E381
  let E383 : Fin BB := Main[206] * 5
  let E384 : Fin BB := Main[208] * 7
  let E385 : Fin BB := E383 + E384
  let E386 : Fin BB := Main[205] * 4
  let E387 : Fin BB := E385 + E386
  let E388 : Fin BB := Main[207] * 6
  let E389 : Fin BB := E387 + E388
  let E390 : Fin BB := Main[209] * 4
  let E391 : Fin BB := E389 + E390
  let E392 : Fin BB := Main[210] * 6
  let E393 : Fin BB := E391 + E392
  let E394 : Fin BB := Main[211] * 5
  let E395 : Fin BB := E393 + E394
  let E396 : Fin BB := Main[212] * 7
  let E397 : Fin BB := E395 + E396
  let E398 : Fin BB := Main[206] * 1
  let E399 : Fin BB := Main[208] * 1
  let E400 : Fin BB := E398 + E399
  let E401 : Fin BB := Main[205] * 1
  let E402 : Fin BB := E400 + E401
  let E403 : Fin BB := Main[207] * 1
  let E404 : Fin BB := E402 + E403
  let E405 : Fin BB := Main[209] * 1
  let E406 : Fin BB := E404 + E405
  let E407 : Fin BB := Main[210] * 1
  let E408 : Fin BB := E406 + E407
  let E409 : Fin BB := Main[211] * 1
  let E410 : Fin BB := E408 + E409
  let E411 : Fin BB := Main[212] * 1
  let E412 : Fin BB := E410 + E411
  let E413 : Fin BB := Main[209] * 27
  let E414 : Fin BB := Main[210] * 27
  let E415 : Fin BB := E413 + E414
  let E416 : Fin BB := Main[211] * 27
  let E417 : Fin BB := E415 + E416
  let E418 : Fin BB := Main[212] * 27
  let E419 : Fin BB := E417 + E418
  let E420 : Fin BB := Main[206] * 51
  let E421 : Fin BB := Main[208] * 51
  let E422 : Fin BB := E420 + E421
  let E423 : Fin BB := Main[205] * 51
  let E424 : Fin BB := E422 + E423
  let E425 : Fin BB := Main[207] * 51
  let E426 : Fin BB := E424 + E425
  let E427 : Fin BB := Main[209] * 59
  let E428 : Fin BB := E426 + E427
  let E429 : Fin BB := Main[210] * 59
  let E430 : Fin BB := E428 + E429
  let E431 : Fin BB := Main[211] * 59
  let E432 : Fin BB := E430 + E431
  let E433 : Fin BB := Main[212] * 59
  let E434 : Fin BB := E432 + E433
  let E435 : Fin BB := Main[31] * E419
  let E436 : Fin BB := 1 - Main[31]
  let E437 : Fin BB := E436 * E434
  let E438 : Fin BB := E435 + E437
  let E439 : Fin BB := Main[213] - E438
  let E440 : Fin BB := Main[249] * E439
  let E441 : Fin BB := Main[3] + 4
  let CS17 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E441, Main[4], Main[5]] 8 Main[249]
  let E442 : Fin BB := Main[1] * 65536
  let E443 : Fin BB := Main[2] + E442
  let CS18 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E443 #v[Main[3], Main[4], Main[5]] E382 #v[Main[213], E397, E412] #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } Main[249]
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
    (.send (.byte (ByteOpcode.ofNat 6) E123 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E127 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E131 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E135 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E139 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E143 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E147 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) E151 16 0) Main[249]),
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[64] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[65] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[66] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[67] 16 0) Main[249]),
    (.assertZero E270),
    (.assertZero E272),
    (.assertZero E274),
    (.assertZero E276),
    (.send (.byte (ByteOpcode.ofNat 6) Main[60] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[61] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[62] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[63] 16 0) Main[249]),
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
    (.send (.byte (ByteOpcode.ofNat 6) Main[44] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[45] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[46] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[47] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[56] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[57] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[58] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[59] 16 0) Main[249]),
    (.assertZero E309),
    (.assertZero E311),
    (.assertZero E313),
    (.assertZero E315),
    (.assertZero E317),
    (.assertZero E319),
    (.assertZero E321),
    (.assertZero E323),
    (.send (.byte (ByteOpcode.ofNat 6) Main[72] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[73] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[74] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[75] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[76] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[77] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[78] 16 0) Main[249]),
    (.send (.byte (ByteOpcode.ofNat 6) Main[79] 16 0) Main[249]),
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
    (.assertZero E440),
  ]

set_option maxRecDepth 1000000 in
lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints Main) ↔
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[72], Main[73], Main[74], Main[75]]
      #v[Main[48], Main[49], Main[50], Main[51]]
      #v[Main[40], Main[41], Main[42], Main[43]]
      {
        carry := #v[Main[80], Main[81], Main[82], Main[83], Main[84], Main[85], Main[86], Main[87], Main[88], Main[89], Main[90], Main[91], Main[92], Main[93], Main[94], Main[95]],
        product := #v[Main[96], Main[97], Main[98], Main[99], Main[100], Main[101], Main[102], Main[103], Main[104], Main[105], Main[106], Main[107], Main[108], Main[109], Main[110], Main[111]],
        b_lower_byte := { low_bytes := #v[Main[112], Main[113], Main[114], Main[115]] },
        c_lower_byte := { low_bytes := #v[Main[116], Main[117], Main[118], Main[119]] },
        b_msb := Main[120],
        c_msb := Main[121],
        product_msb := { msb := Main[122] },
        b_sign_extend := Main[123],
        c_sign_extend := Main[124]
      }
      Main[249] Main[249] 0 0 0 0) ∧
    List.Forall SP1Constraint.toProp
    (MulOperation.constraints
      #v[Main[76], Main[77], Main[78], Main[79]]
      #v[Main[48], Main[49], Main[50], Main[51]]
      #v[Main[40], Main[41], Main[42], Main[43]]
      {
        carry := #v[Main[125], Main[126], Main[127], Main[128], Main[129], Main[130], Main[131], Main[132], Main[133], Main[134], Main[135], Main[136], Main[137], Main[138], Main[139], Main[140]],
        product := #v[Main[141], Main[142], Main[143], Main[144], Main[145], Main[146], Main[147], Main[148], Main[149], Main[150], Main[151], Main[152], Main[153], Main[154], Main[155], Main[156]],
        b_lower_byte := { low_bytes := #v[Main[157], Main[158], Main[159], Main[160]] },
        c_lower_byte := { low_bytes := #v[Main[161], Main[162], Main[163], Main[164]] },
        b_msb := Main[165],
        c_msb := Main[166],
        product_msb := { msb := Main[167] },
        b_sign_extend := Main[168],
        c_sign_extend := Main[169]
      }
      Main[244] 0 (Main[205] + Main[207]) 0 (Main[206] + Main[208]) 0) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[0, 0, 0, 32768]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }, { inverse := Main[219], result := Main[220] }, { inverse := Main[221], result := Main[222] }],
          is_zero_first_half := Main[223],
          is_zero_second_half := Main[224],
          result := Main[225]
        }
      }
      Main[244]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[25], Main[26], Main[27], Main[28]]
      #v[65535, 65535, 65535, 65535]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }, { inverse := Main[230], result := Main[231] }, { inverse := Main[232], result := Main[233] }],
          is_zero_first_half := Main[234],
          is_zero_second_half := Main[235],
          result := Main[236]
        }
      }
      Main[244]) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[15], Main[16], 0, 0]
      #v[0, 32768, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[215], result := Main[216] }, { inverse := Main[217], result := Main[218] }, { inverse := Main[219], result := Main[220] }, { inverse := Main[221], result := Main[222] }],
          is_zero_first_half := Main[223],
          is_zero_second_half := Main[224],
          result := Main[225] }
      }
      (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp
    (IsEqualWordOperation.constraints
      #v[Main[25], Main[26], 0, 0]
      #v[65535, 65535, 0, 0]
      {
        is_diff_zero := {
          is_zero_limb := #v[{ inverse := Main[226], result := Main[227] }, { inverse := Main[228], result := Main[229] }, { inverse := Main[230], result := Main[231] }, { inverse := Main[232], result := Main[233] }],
          is_zero_first_half := Main[234],
          is_zero_second_half := Main[235],
          result := Main[236] }
      }
      (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp
    (IsZeroWordOperation.constraints
      #v[Main[40], Main[41], Main[42], Main[43]]
      {
        is_zero_limb := #v[{ inverse := Main[194], result := Main[195] }, { inverse := Main[196], result := Main[197] }, { inverse := Main[198], result := Main[199] }, { inverse := Main[200], result := Main[201] }],
        is_zero_first_half := Main[202],
        is_zero_second_half := Main[203],
        result := Main[204]
      }
      Main[249]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[40], Main[41], Main[42], Main[43]]
      #v[Main[64], Main[65], Main[66], Main[67]]
      { value := #v[Main[170], Main[171], Main[172], Main[173]] }
      Main[247]) ∧
    List.Forall SP1Constraint.toProp
    (AddOperation.constraints
      #v[Main[52], Main[53], Main[54], Main[55]]
      #v[Main[60], Main[61], Main[62], Main[63]]
      { value := #v[Main[174], Main[175], Main[176], Main[177]] }
      Main[248]) ∧
    List.Forall SP1Constraint.toProp
    (LtOperationUnsigned.constraints
      #v[Main[60], Main[61], Main[62], Main[63]]
      #v[Main[68], Main[69], Main[70], Main[71]]
      {
          u16_compare_operation := { bit := Main[178] },
          u16_flags := #v[Main[179], Main[180], Main[181], Main[182]]
          not_eq_inv := Main[183],
          comparison_limbs := #v[Main[184], Main[185]]
      }
      Main[250]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[18] { msb := Main[237] } Main[244]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[28] { msb := Main[239] } Main[244]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[59] { msb := Main[238] } Main[244]) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[16] { msb := Main[237] } (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[26] { msb := Main[239] } (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[57] { msb := Main[238] } (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp (U16MSBOperation.constraints Main[45] { msb := Main[240] } (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    List.Forall SP1Constraint.toProp (CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[Main[3] + 4, Main[4], Main[5]] 8 Main[249]) ∧
    List.Forall SP1Constraint.toProp
    (ALUTypeReader.constraints
      Main[0]
      (Main[2] + Main[1] * 65536)
      #v[Main[3], Main[4], Main[5]]
      (Main[206] * (16 : Fin BB) + Main[208] * (18 : Fin BB) + Main[205] * (15 : Fin BB) + Main[207] * (17 : Fin BB) +
       Main[209] * (48 : Fin BB) + Main[210] * (50 : Fin BB) + Main[211] * (49 : Fin BB) + Main[212] * (51 : Fin BB))
      #v[Main[213], Main[206] * (5 : Fin BB) + Main[208] * (7 : Fin BB) + Main[205] * (4 : Fin BB) + Main[207] * (6 : Fin BB) + Main[209] * (4 : Fin BB) + Main[210] * (6 : Fin BB) + Main[211] * (5 : Fin BB) + Main[212] * (7 : Fin BB), Main[206] + Main[208] + Main[205] + Main[207] + Main[209] + Main[210] + Main[211] + Main[212]]
      #v[Main[32], Main[33], Main[34], Main[35]]
      {
        op_a := Main[6],
        op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
        op_a_0 := Main[13],
        op_b := Main[14],
        op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
        op_c := #v[Main[21], Main[22], Main[23], Main[24]],
        op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } },
        imm_c := Main[31]
      }
      Main[249]) ∧
    Main[244] = Main[249] * ((1 : Fin BB) - (Main[209] + Main[210] + Main[211] + Main[212])) ∧
    Main[241] = Main[237] * (Main[205] + Main[207] + Main[209] + Main[210]) ∧
    Main[245] = Main[238] * (Main[205] + Main[207] + Main[209] + Main[210]) ∧
    Main[246] = Main[239] * (Main[205] + Main[207] + Main[209] + Main[210]) ∧
    Main[15] = Main[36] ∧
    Main[25] = Main[40] ∧
    Main[16] = Main[37] ∧
    Main[26] = Main[41] ∧
    Main[38] = Main[17] * ((1 : Fin BB) - (Main[209] + Main[210] + Main[211] + Main[212])) + Main[241] * (Main[209] + Main[210] + Main[211] + Main[212]) * (65535 : Fin BB) ∧
    Main[42] = Main[27] * ((1 : Fin BB) - (Main[209] + Main[210] + Main[211] + Main[212])) + Main[246] * (Main[209] + Main[210] + Main[211] + Main[212]) * (65535 : Fin BB) ∧
    Main[39] = Main[18] * ((1 : Fin BB) - (Main[209] + Main[210] + Main[211] + Main[212])) + Main[241] * (Main[209] + Main[210] + Main[211] + Main[212]) * (65535 : Fin BB) ∧
    Main[43] = Main[28] * ((1 : Fin BB) - (Main[209] + Main[210] + Main[211] + Main[212])) + Main[246] * (Main[209] + Main[210] + Main[211] + Main[212]) * (65535 : Fin BB) ∧
    Main[48] = Main[44] ∧
    Main[49] = Main[45] ∧
    (Main[211] + Main[212] = 0 ∨ Main[50] = 0) ∧
    (Main[209] + Main[210] = 0 ∨ Main[50] = Main[240] * 65535) ∧
    (Main[209] + Main[210] + Main[211] + Main[212] = 0 ∨ Main[46] = Main[240] * 65535) ∧
    (Main[206] + Main[208] + Main[205] + Main[207] = 0 ∨ Main[50] = Main[46]) ∧
    (Main[211] + Main[212] = 0 ∨ Main[51] = 0) ∧
    (Main[209] + Main[210] = 0 ∨ Main[51] = Main[240] * 65535) ∧
    (Main[209] + Main[210] + Main[211] + Main[212] = 0 ∨ Main[47] = Main[240] * 65535) ∧
    (Main[206] + Main[208] + Main[205] + Main[207] = 0 ∨ Main[51] = Main[47]) ∧
    Main[52] = Main[56] ∧
    Main[53] = Main[57] ∧
    (Main[211] + Main[212] = 0 ∨ Main[54] = 0) ∧
    (Main[209] + Main[210] = 0 ∨ Main[54] = Main[238] * (65535 : Fin BB)) ∧
    (Main[209] + Main[210] + Main[211] + Main[212] = 0 ∨ Main[58] = Main[238] * (65535 : Fin BB)) ∧
    (Main[206] + Main[208] + Main[205] + Main[207] = 0 ∨ Main[54] = Main[58]) ∧
    (Main[211] + Main[212] = 0 ∨ Main[55] = 0) ∧
    (Main[209] + Main[210] = 0 ∨ Main[55] = Main[238] * (65535 : Fin BB)) ∧
    (Main[209] + Main[210] + Main[211] + Main[212] = 0 ∨ Main[59] = Main[238] * (65535 : Fin BB)) ∧
    (Main[206] + Main[208] + Main[205] + Main[207] = 0 ∨ Main[55] = Main[59]) ∧
    Main[214] = Main[225] * Main[236] * (Main[205] + Main[207] + Main[209] + Main[210]) ∧
    Main[242] = Main[241] * ((1 : Fin BB) - Main[214]) ∧
    Main[243] = ((1 : Fin BB) - Main[241]) * ((1 : Fin BB) - Main[214]) ∧
    (Main[214] = 0 ∨ Main[44] = Main[36]) ∧
    (Main[214] = 0 ∨ Main[56] = 0) ∧
    (Main[214] = 0 ∨ Main[45] = Main[37]) ∧
    (Main[214] = 0 ∨ Main[57] = 0) ∧
    (Main[214] = 0 ∨ Main[46] = Main[38]) ∧
    (Main[214] = 0 ∨ Main[58] = 0) ∧
    (Main[214] = 0 ∨ Main[47] = Main[39]) ∧
    (Main[214] = 0 ∨ Main[59] = 0) ∧
    (Main[214] = 1 ∨ Main[36] = Main[72] + Main[52] - Main[186] * (65536 : Fin BB)) ∧
    (Main[214] = 1 ∨ Main[37] = Main[73] + Main[53] - Main[187] * (65536 : Fin BB) + Main[186]) ∧
    (Main[214] = 1 ∨ Main[38] = Main[74] + Main[54] - Main[188] * (65536 : Fin BB) + Main[187]) ∧
    (Main[214] = 1 ∨ Main[39] = Main[75] + Main[55] - Main[189] * (65536 : Fin BB) + Main[188]) ∧
    (Main[214] = 1 ∨ Main[241] * (65535 : Fin BB) = Main[76] + Main[245] * (65535 : Fin BB) - Main[190] * (65536 : Fin BB) + Main[189]) ∧
    (Main[214] = 1 ∨ Main[241] * (65535 : Fin BB) = Main[77] + Main[245] * (65535 : Fin BB) - Main[191] * (65536 : Fin BB) + Main[190]) ∧
    (Main[214] = 1 ∨ Main[241] * (65535 : Fin BB) = Main[78] + Main[245] * (65535 : Fin BB) - Main[192] * (65536 : Fin BB) + Main[191]) ∧
    (Main[214] = 1 ∨ Main[241] * (65535 : Fin BB) = Main[79] + Main[245] * (65535 : Fin BB) - Main[193] * (65536 : Fin BB) + Main[192]) ∧
    (¬Main[249] = 0 → (Main[72] + Main[52] - Main[186] * 65536).val < 65536) ∧
    (¬Main[249] = 0 → (Main[73] + Main[53] - Main[187] * 65536 + Main[186]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[74] + Main[54] - Main[188] * 65536 + Main[187]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[75] + Main[55] - Main[189] * 65536 + Main[188]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[76] + Main[245] * 65535 - Main[190] * 65536 + Main[189]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[77] + Main[245] * 65535 - Main[191] * 65536 + Main[190]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[78] + Main[245] * 65535 - Main[192] * 65536 + Main[191]).val < 65536) ∧
    (¬Main[249] = 0 → (Main[79] + Main[245] * 65535 - Main[193] * 65536 + Main[192]).val < 65536) ∧
    (Main[206] + Main[205] + Main[209] + Main[211] = 0 ∨ Main[44] = Main[32]) ∧
    (Main[208] + Main[207] + Main[210] + Main[212] = 0 ∨ Main[56] = Main[32]) ∧
    (Main[206] + Main[205] + Main[209] + Main[211] = 0 ∨ Main[45] = Main[33]) ∧
    (Main[208] + Main[207] + Main[210] + Main[212] = 0 ∨ Main[57] = Main[33]) ∧
    (Main[206] + Main[205] + Main[209] + Main[211] = 0 ∨ Main[46] = Main[34]) ∧
    (Main[208] + Main[207] + Main[210] + Main[212] = 0 ∨ Main[58] = Main[34]) ∧
    (Main[206] + Main[205] + Main[209] + Main[211] = 0 ∨ Main[47] = Main[35]) ∧
    (Main[208] + Main[207] + Main[210] + Main[212] = 0 ∨ Main[59] = Main[35]) ∧
    (Main[245] = 0 ∨ Main[241] = 1) ∧
    (Main[56] + Main[57] + Main[58] + Main[59] = 0 ∨ Main[245] = 1 ∨ Main[241] = 0) ∧
    (Main[204] = 0 ∨ Main[44] = 65535) ∧
    (Main[204] = 0 ∨ Main[45] = 65535) ∧
    (Main[204] = 0 ∨ Main[46] = 65535) ∧
    (Main[204] = 0 ∨ Main[47] = 65535) ∧
    (Main[204] = 0 ∨ Main[52] = Main[36]) ∧
    (Main[204] = 0 ∨ Main[53] = Main[37]) ∧
    (Main[204] = 0 ∨ Main[54] = Main[38]) ∧
    (Main[204] = 0 ∨ Main[55] = Main[39]) ∧
    (Main[246] = 1 ∨ Main[40] = Main[64]) ∧
    (Main[245] = 1 ∨ Main[52] = Main[60]) ∧
    (Main[246] = 1 ∨ Main[41] = Main[65]) ∧
    (Main[245] = 1 ∨ Main[53] = Main[61]) ∧
    (Main[246] = 1 ∨ Main[42] = Main[66]) ∧
    (Main[245] = 1 ∨ Main[54] = Main[62]) ∧
    (Main[246] = 1 ∨ Main[43] = Main[67]) ∧
    (Main[245] = 1 ∨ Main[55] = Main[63]) ∧
    (¬Main[249] = 0 → Main[64].val < 65536) ∧
    (¬Main[249] = 0 → Main[65].val < 65536) ∧
    (¬Main[249] = 0 → Main[66].val < 65536) ∧
    (¬Main[249] = 0 → Main[67].val < 65536) ∧
    (Main[247] = 0 ∨ Main[170] = 0) ∧
    (Main[247] = 0 ∨ Main[171] = 0) ∧
    (Main[247] = 0 ∨ Main[172] = 0) ∧
    (Main[247] = 0 ∨ Main[173] = 0) ∧
    (¬Main[249] = 0 → Main[60].val < 65536) ∧
    (¬Main[249] = 0 → Main[61].val < 65536) ∧
    (¬Main[249] = 0 → Main[62].val < 65536) ∧
    (¬Main[249] = 0 → Main[63].val < 65536) ∧
    (Main[248] = 0 ∨ Main[174] = 0) ∧
    (Main[248] = 0 ∨ Main[175] = 0) ∧
    (Main[248] = 0 ∨ Main[176] = 0) ∧
    (Main[248] = 0 ∨ Main[177] = 0) ∧
    Main[247] = Main[246] * Main[249] ∧
    Main[248] = Main[245] * Main[249] ∧
    Main[68] = Main[204] + ((1 : Fin BB) - Main[204]) * Main[64] ∧
    Main[69] = ((1 : Fin BB) - Main[204]) * Main[65] ∧
    Main[70] = ((1 : Fin BB) - Main[204]) * Main[66] ∧
    Main[71] = ((1 : Fin BB) - Main[204]) * Main[67] ∧
    Main[250] = ((1 : Fin BB) - Main[204]) * Main[249] ∧
    (Main[250] = 0 ∨ Main[178] = 1) ∧
    (¬Main[249] = 0 → Main[44].val < 65536) ∧
    (¬Main[249] = 0 → Main[45].val < 65536) ∧
    (¬Main[249] = 0 → Main[46].val < 65536) ∧
    (¬Main[249] = 0 → Main[47].val < 65536) ∧
    (¬Main[249] = 0 → Main[56].val < 65536) ∧
    (¬Main[249] = 0 → Main[57].val < 65536) ∧
    (¬Main[249] = 0 → Main[58].val < 65536) ∧
    (¬Main[249] = 0 → Main[59].val < 65536) ∧
    (Main[186] = 0 ∨ Main[186] = 1) ∧
    (Main[187] = 0 ∨ Main[187] = 1) ∧
    (Main[188] = 0 ∨ Main[188] = 1) ∧
    (Main[189] = 0 ∨ Main[189] = 1) ∧
    (Main[190] = 0 ∨ Main[190] = 1) ∧
    (Main[191] = 0 ∨ Main[191] = 1) ∧
    (Main[192] = 0 ∨ Main[192] = 1) ∧
    (Main[193] = 0 ∨ Main[193] = 1) ∧
    (¬Main[249] = 0 → Main[72].val < 65536) ∧
    (¬Main[249] = 0 → Main[73].val < 65536) ∧
    (¬Main[249] = 0 → Main[74].val < 65536) ∧
    (¬Main[249] = 0 → Main[75].val < 65536) ∧
    (¬Main[249] = 0 → Main[76].val < 65536) ∧
    (¬Main[249] = 0 → Main[77].val < 65536) ∧
    (¬Main[249] = 0 → Main[78].val < 65536) ∧
    (¬Main[249] = 0 → Main[79].val < 65536) ∧
    (Main[205] = 0 ∨ Main[205] = 1) ∧
    (Main[206] = 0 ∨ Main[206] = 1) ∧
    (Main[207] = 0 ∨ Main[207] = 1) ∧
    (Main[208] = 0 ∨ Main[208] = 1) ∧
    (Main[209] = 0 ∨ Main[209] = 1) ∧
    (Main[210] = 0 ∨ Main[210] = 1) ∧
    (Main[211] = 0 ∨ Main[211] = 1) ∧
    (Main[212] = 0 ∨ Main[212] = 1) ∧
    (Main[214] = 0 ∨ Main[214] = 1) ∧
    (Main[244] = 0 ∨ Main[244] = 1) ∧
    (Main[241] = 0 ∨ Main[241] = 1) ∧
    (Main[242] = 0 ∨ Main[242] = 1) ∧
    (Main[243] = 0 ∨ Main[243] = 1) ∧
    (Main[245] = 0 ∨ Main[245] = 1) ∧
    (Main[246] = 0 ∨ Main[246] = 1) ∧
    (Main[249] = 0 ∨ Main[249] = 1) ∧
    (Main[247] = 0 ∨ Main[247] = 1) ∧
    (Main[248] = 0 ∨ Main[248] = 1) ∧
    Main[206] + Main[208] + Main[205] + Main[207] + Main[209] + Main[210] + Main[211] + Main[212] = 1 ∧
    (Main[249] = 0 ∨ Main[213] = Main[31] * (Main[209] * (27 : Fin BB) + Main[210] * (27 : Fin BB) + Main[211] * (27 : Fin BB) + Main[212] * (27 : Fin BB)) + ((1 : Fin BB) - Main[31]) * (Main[206] * (51 : Fin BB) + Main[208] * (51 : Fin BB) + Main[205] * (51 : Fin BB) + Main[207] * (51 : Fin BB) + Main[209] * (59 : Fin BB) + Main[210] * (59 : Fin BB) + Main[211] * (59 : Fin BB) + Main[212] * (59 : Fin BB)))
  := by
    simp [constraints, sub_eq_zero]
    iterate 3 rw [eq_comm (a := _ * (Main[205] + Main[207] + Main[209] + Main[210]))]
    iterate 3 rw [eq_comm (a := (1 : Fin BB))]
    rw [eq_comm (a := _ * _) (b := Main[250])]
    simp

end constraints

-- section rem

-- set_option maxRecDepth 1000000 in
-- lemma allHold_constraints_iff_rem :
--   Main[249] = 1 →
--   Main[205] = 0 → Main[206] = 0 → Main[207] = 1 → Main[208] = 0 →
--   Main[209] = 0 → Main[210] = 0 → Main[211] = 0 → Main[212] = 0 →
--   List.Forall SP1Constraint.toProp (constraints Main) →
--     False
--   := by
--   intro h_is_real h_div h_divu h_rem h_remu h_divw h_divuw h_remw h_remuw
--   rw [allHold_constraints_iff]

--   intro cstrs

--   set a0 := Main[32]
--   set a1 := Main[33]
--   set a2 := Main[34]
--   set a3 := Main[35]

--   set b0 := Main[15]
--   set b1 := Main[16]
--   set b2 := Main[17]
--   set b3 := Main[18]

--   set c0 := Main[25]
--   set c1 := Main[26]
--   set c2 := Main[27]
--   set c3 := Main[28]

--   set lb0 := Main[36]
--   set lb1 := Main[37]
--   set lb2 := Main[38]
--   set lb3 := Main[39]

--   set lc0 := Main[40]
--   set lc1 := Main[41]
--   set lc2 := Main[42]
--   set lc3 := Main[43]

--   set q0 := Main[44]
--   set q1 := Main[45]
--   set q2 := Main[46]
--   set q3 := Main[47]

--   set qbc0 := Main[48]
--   set qbc1 := Main[49]
--   set qbc2 := Main[50]
--   set qbc3 := Main[51]

--   set rbc0 := Main[52]
--   set rbc1 := Main[53]
--   set rbc2 := Main[54]
--   set rbc3 := Main[55]

--   set r0 := Main[56]
--   set r1 := Main[57]
--   set r2 := Main[58]
--   set r3 := Main[59]

--   set ar0 := Main[60]
--   set ar1 := Main[61]
--   set ar2 := Main[62]
--   set ar3 := Main[63]

--   set ac0 := Main[64]
--   set ac1 := Main[65]
--   set ac2 := Main[66]
--   set ac3 := Main[67]

--   set maco10 := Main[68]
--   set maco11 := Main[69]
--   set maco12 := Main[70]
--   set maco13 := Main[71]

--   set ctq0 := Main[72]
--   set ctq1 := Main[73]
--   set ctq2 := Main[74]
--   set ctq3 := Main[75]
--   set ctq4 := Main[76]
--   set ctq5 := Main[77]
--   set ctq6 := Main[78]
--   set ctq7 := Main[79]

--   set cnop0 := Main[170]
--   set cnop1 := Main[171]
--   set cnop2 := Main[172]
--   set cnop3 := Main[173]

--   set rnop0 := Main[174]
--   set rnop1 := Main[175]
--   set rnop2 := Main[176]
--   set rnop3 := Main[177]

--   set arlt := Main[178]

--   set cry0 := Main[186]
--   set cry1 := Main[187]
--   set cry2 := Main[188]
--   set cry3 := Main[189]
--   set cry4 := Main[190]
--   set cry5 := Main[191]
--   set cry6 := Main[192]
--   set cry7 := Main[193]

--   set is_c_0 := Main[204]

--   set is_div := Main[205]
--   set is_divu := Main[206]
--   set is_rem := Main[207]
--   set is_remu := Main[208]
--   set is_divw := Main[209]
--   set is_remw := Main[210]
--   set is_divuw := Main[211]
--   set is_remuw := Main[212]

--   set is_overflow := Main[214]
--   set is_overflow_b := Main[225]
--   set is_overflow_c := Main[236]

--   set msb_b := Main[237]
--   set msb_rem := Main[238]
--   set msb_c := Main[239]
--   set msb_quot := Main[240]
--   set b_neg := Main[241]
--   set b_neg_not_overflow := Main[242]
--   set b_not_neg_not_overflow := Main[243]
--   set is_real_not_word := Main[244]
--   set rem_neg := Main[245]
--   set c_neg := Main[246]
--   set abs_c_alu_event := Main[247]
--   set abs_rem_alu_event := Main[248]
--   set is_real := Main[249]
--   set remainder_check_multiplicity := Main[250]

--   obtain ⟨ main_mul_low, main_mul_high,
--            overflow_b, overflow_c, w_overflow_b, w_overflow_c,
--            div_zero, c_neg_sum_zero, rem_neg_sum_zero, abs_check,
--            eq_msb_b, eq_msb_c, eq_msb_rem, w_eq_msb_b, w_eq_msb_c, w_eq_msb_rem, w_eq_msb_quot,
--            cpu, alu,
--            eq_is_real_not_word, eq_b_neg, eq_rem_neg, eq_c_neg,
--            eq_lb0, eq_lc0, eq_lb1, eq_lc1, eq_lb2, eq_lc2, eq_lb3, eq_lc3,
--            eq_qbc0, eq_qbc1, w_eq_qbc2_uw, w_eq_qbc2_w, w_eq_q2_w, eq_qbc2, w_eq_qbc3_uw, w_eq_qbc3_w, w_eq_q3_w, eq_qbc3,
--            eq_rbc0, eq_rbc1, w_eq_rbc2_uw, w_eq_rbc2_w, w_eq_r2_w, eq_rbc2, w_eq_rbc3_uw, w_eq_rbc3_w, w_eq_r3_w, eq_rbc3,
--            eq_is_overflow, eq_b_neg_not_overflow, eq_not_b_neg_not_overflow,
--            of_eq_q0, of_eq_r0, of_eq_q1, of_eq_r1, of_eq_q2, of_eq_r2, of_eq_q3, of_eq_r3,
--            nof_eq_ctqpr0, nof_eq_ctqpr1, nof_eq_ctqpr2, nof_eq_ctqpr3,
--            nof_eq_ctqpr4, nof_eq_ctqpr5, nof_eq_ctqpr6, nof_eq_ctqpr7,
--            u16_ctqpr0, u16_ctqpr1, u16_ctqpr2, u16_ctqpr3, u16_ctqpr4, u16_ctqpr5, u16_ctqpr6, u16_ctqpr7,
--            eq_d_a0, eq_r_a0, eq_d_a1, eq_r_a1, eq_d_a2, eq_r_a2, eq_d_a3, eq_r_a3,
--            r_neg_b_neg, r_pos_b_pos,
--            c0_eq_q0, c0_eq_q1, c0_eq_q2, c0_eq_q3, c0_eq_r0, c0_eq_r1, c0_eq_r2, c0_eq_r3,
--            cn_ac0, rn_ar0, cn_ac1, rn_ar1, cn_ac2, rn_ar2, cn_ac3, rn_ar3,
--            u16_ac0, u16_ac1, u16_ac2, u16_ac3, eq_cnop0, eq_cnop1, eq_cnop2, eq_cnop3,
--            u16_ar0, u16_ar1, u16_ar2, u16_ar3, eq_rnop0, eq_rnop1, eq_rnop2, eq_rnop3,
--            eq_abs_c_alu_event, eq_abs_rem_alu_event,
--            eq_maco10, eq_maco11, eq_maco12, eq_maco13,
--            eq_rcm, eq_arlt,
--            u16_q0, u16_q1, u16_q2, u16_q3, u16_r0, u16_r1, u16_r2, u16_r3,
--            b_cry0, b_cry1, b_cry2, b_cry3, b_cry4, b_cry5, b_cry6, b_cry7,
--            u16_ctq0, u16_ctq1, u16_ctq2, u16_ctq3, u16_ctq4, u16_ctq5, u16_ctq6, u16_ctq7,
--            b_is_div, b_is_divu, b_is_rem, b_is_remu, b_is_divw, b_is_remw, b_is_divuw, b_is_remuw,
--            b_is_overflow, b_is_real_not_word, b_b_neg, b_b_neg_not_overflow, b_b_not_neg_not_overflow,
--            b_rem_neg, b_c_neg, b_is_real, b_abs_c_alu_event, b_abs_rem_alu_event, b_one_of_ops,
--            correct_opcode ⟩ := cstrs
--   symm at eq_lb0 eq_lc0 eq_lb1 eq_lc1
--   rw [eq_comm (a := b_neg * 65535)] at nof_eq_ctqpr4 nof_eq_ctqpr5 nof_eq_ctqpr6 nof_eq_ctqpr7
--   rw [eq_comm (b := a0)] at eq_d_a0 eq_r_a0
--   rw [eq_comm (b := a1)] at eq_d_a1 eq_r_a1
--   rw [eq_comm (b := a2)] at eq_d_a2 eq_r_a2
--   rw [eq_comm (b := a3)] at eq_d_a3 eq_r_a3
--   rw [eq_comm (b := ac0)] at cn_ac0; rw [eq_comm (b := ar0)] at rn_ar0
--   rw [eq_comm (b := ac1)] at cn_ac1; rw [eq_comm (b := ar1)] at rn_ar1
--   rw [eq_comm (b := ac2)] at cn_ac2; rw [eq_comm (b := ar2)] at rn_ar2
--   rw [eq_comm (b := ac3)] at cn_ac3; rw [eq_comm (b := ar3)] at rn_ar3
--   clear correct_opcode

--   sorry

-- end rem

end DivRem
