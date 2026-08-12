import SP1Clean.Math.Word
import SP1Clean.Extracted.ExtractionDSL
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # AUTO-GENERATED Core public-values AIR oracle — do not edit by hand.

Generated from the pinned `ExecutionRecord::eval_public_values` through the list-only constraint compiler mode. This is the complete machine-level assertion and interaction block; it is not attached to a table row and takes the exact 160-element public-values vector directly. -/

set_option linter.all false  -- auto-generated: skip linters

namespace SP1Clean.Extracted
open SP1Clean

-- Generated Lean code for the machine-level public-values constraints

namespace PublicValuesOracle

@[irreducible] def assertsPart0 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E0 : F := publicValues[113] * 256
  let E1 : F := publicValues[114] + E0
  let E2 : F := publicValues[115] * 65536
  let E3 : F := publicValues[116] + E2
  let E4 : F := publicValues[117] * 256
  let E5 : F := publicValues[118] + E4
  let E6 : F := publicValues[119] * 65536
  let E7 : F := publicValues[120] + E6
  let E12 : F := publicValues[88] - 1
  let E13 : F := publicValues[88] * E12
  let E14 : F := publicValues[88] - 1
  let E15 : F := E3 - E7
  let E16 : F := E14 * E15
  let E17 : F := publicValues[88] - 1
  let E18 : F := E1 - E5
  let E19 : F := E17 * E18
  let E20 : F := publicValues[88] - 1
  let E21 : F := publicValues[80] - publicValues[83]
  let E22 : F := E20 * E21
  let E23 : F := publicValues[81] - publicValues[84]
  let E24 : F := E20 * E23
  let E25 : F := publicValues[82] - publicValues[85]
  let E26 : F := E20 * E25
  let E27 : F := publicValues[121] - 1
  let E28 : F := publicValues[121] * E27
  let E29 : F := E5 - E1
  let E30 : F := E29 * publicValues[122]
  let E31 : F := 1 - publicValues[121]
  let E32 : F := E30 - E31
  let E33 : F := E5 - E1
  let E34 : F := E33 * publicValues[121]
  let E35 : F := publicValues[123] - 1
  let E36 : F := publicValues[123] * E35
  let E37 : F := E7 - E3
  let E38 : F := E37 * publicValues[124]
  let E39 : F := 1 - publicValues[123]
  let E40 : F := E38 - E39
  let E41 : F := E7 - E3
  let E42 : F := E41 * publicValues[123]
  let E43 : F := 1 - publicValues[88]
  let E44 : F := publicValues[121] * publicValues[123]
  let E45 : F := E43 - E44
  let E46 : F := E5 + E7
  let E47 : F := E46 - 1
  let E48 : F := E47 * publicValues[149]
  let E49 : F := E48 - 1
  let E50 : F := publicValues[88] * E49
  let E51 : F := publicValues[150] - 1
  let E52 : F := publicValues[150] * E51
  let E53 : F := publicValues[113] - 0
  let E54 : F := publicValues[150] * E53
  let E55 : F := publicValues[114] - 0
  let E56 : F := publicValues[150] * E55
  let E57 : F := publicValues[115] - 0
  let E58 : F := publicValues[150] * E57
  let E59 : F := publicValues[116] - 1
  let E60 : F := publicValues[150] * E59
  let E61 : F := publicValues[88] - 1
  let E62 : F := publicValues[150] * E61
  let E63 : F := publicValues[150] * publicValues[0]
  let E64 : F := publicValues[150] * publicValues[1]
  let E65 : F := publicValues[150] * publicValues[2]
  let E66 : F := publicValues[150] * publicValues[3]
  let E67 : F := publicValues[150] * publicValues[4]
  let E68 : F := publicValues[150] * publicValues[5]
  let E69 : F := publicValues[150] * publicValues[6]
  let E70 : F := publicValues[150] * publicValues[7]
  let E71 : F := publicValues[150] * publicValues[8]
  let E72 : F := publicValues[150] * publicValues[9]
  let E73 : F := publicValues[150] * publicValues[10]
  let E74 : F := publicValues[150] * publicValues[11]
  let E75 : F := publicValues[150] * publicValues[12]
  let E76 : F := publicValues[150] * publicValues[13]
  let E77 : F := publicValues[150] * publicValues[14]
  let E78 : F := publicValues[150] * publicValues[15]
  let E79 : F := publicValues[150] * publicValues[16]
  let E80 : F := publicValues[150] * publicValues[17]
  let E81 : F := publicValues[150] * publicValues[18]
  let E82 : F := publicValues[150] * publicValues[19]
  let E83 : F := publicValues[150] * publicValues[20]
  let E84 : F := publicValues[150] * publicValues[21]
  let E85 : F := publicValues[150] * publicValues[22]
  let E86 : F := publicValues[150] * publicValues[23]
  let E87 : F := publicValues[150] * publicValues[24]
  let E88 : F := publicValues[150] * publicValues[25]
  let E89 : F := publicValues[150] * publicValues[26]
  let E90 : F := publicValues[150] * publicValues[27]
  let E91 : F := publicValues[150] * publicValues[28]
  let E92 : F := publicValues[150] * publicValues[29]
  let E93 : F := publicValues[150] * publicValues[30]
  let E94 : F := publicValues[150] * publicValues[31]
  let E95 : F := publicValues[150] * publicValues[64]
  let E96 : F := publicValues[150] * publicValues[65]
  let E97 : F := publicValues[150] * publicValues[66]
  let E98 : F := publicValues[150] * publicValues[67]
  let E99 : F := publicValues[150] * publicValues[68]
  let E100 : F := publicValues[150] * publicValues[69]
  let E101 : F := publicValues[150] * publicValues[70]
  let E102 : F := publicValues[150] * publicValues[71]
  [
    publicValues[156],
    publicValues[157],
    publicValues[158],
    publicValues[159],
    E13,
    E16,
    E19,
    E22,
    E24,
    E26,
    E28,
    E32,
    E34,
    E36,
    E40,
    E42,
    E45,
    E50,
    E52,
    E54,
    E56,
    E58,
    E60,
    E62,
    E63,
    E64,
    E65,
    E66,
    E67,
    E68,
    E69,
    E70,
    E71,
    E72,
    E73,
    E74,
    E75,
    E76,
    E77,
    E78,
    E79,
    E80,
    E81,
    E82,
    E83,
    E84,
    E85,
    E86,
    E87,
    E88,
    E89,
    E90,
    E91,
    E92,
    E93,
    E94,
    E95,
    E96,
    E97,
    E98,
    E99,
    E100,
    E101,
    E102,
  ]

@[irreducible] def assertsPart1 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E103 : F := publicValues[150] * publicValues[86]
  let E104 : F := publicValues[150] * publicValues[89]
  let E105 : F := publicValues[150] * publicValues[90]
  let E106 : F := publicValues[150] * publicValues[91]
  let E107 : F := publicValues[150] * publicValues[95]
  let E108 : F := publicValues[150] * publicValues[96]
  let E109 : F := publicValues[150] * publicValues[97]
  let E110 : F := publicValues[150] * publicValues[101]
  let E111 : F := publicValues[150] * publicValues[102]
  let E112 : F := publicValues[150] * publicValues[103]
  let E113 : F := publicValues[150] * publicValues[107]
  let E114 : F := publicValues[150] * publicValues[108]
  let E115 : F := publicValues[150] * publicValues[109]
  let E116 : F := publicValues[150] * publicValues[144]
  let E117 : F := publicValues[150] * publicValues[146]
  let E118 : F := publicValues[87] - publicValues[86]
  let E119 : F := publicValues[86] * E118
  let E120 : F := publicValues[88] - 1
  let E121 : F := publicValues[86] - publicValues[87]
  let E122 : F := E120 * E121
  let E123 : F := publicValues[144] - 1
  let E124 : F := publicValues[144] * E123
  let E125 : F := publicValues[145] - 1
  let E126 : F := publicValues[145] * E125
  let E127 : F := publicValues[145] - 1
  let E128 : F := publicValues[144] * E127
  let E129 : F := publicValues[88] - 1
  let E130 : F := publicValues[144] - publicValues[145]
  let E131 : F := E129 * E130
  let E132 : F := publicValues[88] - 1
  let E133 : F := publicValues[0] - publicValues[32]
  let E134 : F := E132 * E133
  let E135 : F := publicValues[1] - publicValues[33]
  let E136 : F := E132 * E135
  let E137 : F := publicValues[2] - publicValues[34]
  let E138 : F := E132 * E137
  let E139 : F := publicValues[3] - publicValues[35]
  let E140 : F := E132 * E139
  let E141 : F := publicValues[88] - 1
  let E142 : F := publicValues[4] - publicValues[36]
  let E143 : F := E141 * E142
  let E144 : F := publicValues[5] - publicValues[37]
  let E145 : F := E141 * E144
  let E146 : F := publicValues[6] - publicValues[38]
  let E147 : F := E141 * E146
  let E148 : F := publicValues[7] - publicValues[39]
  let E149 : F := E141 * E148
  let E150 : F := publicValues[88] - 1
  let E151 : F := publicValues[8] - publicValues[40]
  let E152 : F := E150 * E151
  let E153 : F := publicValues[9] - publicValues[41]
  let E154 : F := E150 * E153
  let E155 : F := publicValues[10] - publicValues[42]
  let E156 : F := E150 * E155
  let E157 : F := publicValues[11] - publicValues[43]
  let E158 : F := E150 * E157
  let E159 : F := publicValues[88] - 1
  let E160 : F := publicValues[12] - publicValues[44]
  let E161 : F := E159 * E160
  let E162 : F := publicValues[13] - publicValues[45]
  let E163 : F := E159 * E162
  let E164 : F := publicValues[14] - publicValues[46]
  let E165 : F := E159 * E164
  let E166 : F := publicValues[15] - publicValues[47]
  let E167 : F := E159 * E166
  let E168 : F := publicValues[88] - 1
  let E169 : F := publicValues[16] - publicValues[48]
  let E170 : F := E168 * E169
  let E171 : F := publicValues[17] - publicValues[49]
  let E172 : F := E168 * E171
  let E173 : F := publicValues[18] - publicValues[50]
  let E174 : F := E168 * E173
  let E175 : F := publicValues[19] - publicValues[51]
  let E176 : F := E168 * E175
  let E177 : F := publicValues[88] - 1
  let E178 : F := publicValues[20] - publicValues[52]
  let E179 : F := E177 * E178
  let E180 : F := publicValues[21] - publicValues[53]
  let E181 : F := E177 * E180
  let E182 : F := publicValues[22] - publicValues[54]
  let E183 : F := E177 * E182
  let E184 : F := publicValues[23] - publicValues[55]
  let E185 : F := E177 * E184
  let E186 : F := publicValues[88] - 1
  let E187 : F := publicValues[24] - publicValues[56]
  let E188 : F := E186 * E187
  let E189 : F := publicValues[25] - publicValues[57]
  let E190 : F := E186 * E189
  let E191 : F := publicValues[26] - publicValues[58]
  let E192 : F := E186 * E191
  let E193 : F := publicValues[27] - publicValues[59]
  let E194 : F := E186 * E193
  let E195 : F := publicValues[88] - 1
  let E196 : F := publicValues[28] - publicValues[60]
  let E197 : F := E195 * E196
  let E198 : F := publicValues[29] - publicValues[61]
  let E199 : F := E195 * E198
  let E200 : F := publicValues[30] - publicValues[62]
  let E201 : F := E195 * E200
  let E202 : F := publicValues[31] - publicValues[63]
  let E203 : F := E195 * E202
  let E204 : F := publicValues[0] - publicValues[32]
  let E205 : F := publicValues[0] * E204
  let E206 : F := publicValues[1] - publicValues[33]
  let E207 : F := publicValues[0] * E206
  let E208 : F := publicValues[2] - publicValues[34]
  let E209 : F := publicValues[0] * E208
  let E210 : F := publicValues[3] - publicValues[35]
  let E211 : F := publicValues[0] * E210
  let E212 : F := publicValues[4] - publicValues[36]
  let E213 : F := publicValues[0] * E212
  let E214 : F := publicValues[5] - publicValues[37]
  let E215 : F := publicValues[0] * E214
  let E216 : F := publicValues[6] - publicValues[38]
  let E217 : F := publicValues[0] * E216
  let E218 : F := publicValues[7] - publicValues[39]
  let E219 : F := publicValues[0] * E218
  let E220 : F := publicValues[8] - publicValues[40]
  let E221 : F := publicValues[0] * E220
  let E222 : F := publicValues[9] - publicValues[41]
  let E223 : F := publicValues[0] * E222
  let E224 : F := publicValues[10] - publicValues[42]
  let E225 : F := publicValues[0] * E224
  [
    E103,
    E104,
    E105,
    E106,
    E107,
    E108,
    E109,
    E110,
    E111,
    E112,
    E113,
    E114,
    E115,
    E116,
    E117,
    E119,
    E122,
    E124,
    E126,
    E128,
    E131,
    E134,
    E136,
    E138,
    E140,
    E143,
    E145,
    E147,
    E149,
    E152,
    E154,
    E156,
    E158,
    E161,
    E163,
    E165,
    E167,
    E170,
    E172,
    E174,
    E176,
    E179,
    E181,
    E183,
    E185,
    E188,
    E190,
    E192,
    E194,
    E197,
    E199,
    E201,
    E203,
    E205,
    E207,
    E209,
    E211,
    E213,
    E215,
    E217,
    E219,
    E221,
    E223,
    E225,
  ]

@[irreducible] def assertsPart2 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E226 : F := publicValues[11] - publicValues[43]
  let E227 : F := publicValues[0] * E226
  let E228 : F := publicValues[12] - publicValues[44]
  let E229 : F := publicValues[0] * E228
  let E230 : F := publicValues[13] - publicValues[45]
  let E231 : F := publicValues[0] * E230
  let E232 : F := publicValues[14] - publicValues[46]
  let E233 : F := publicValues[0] * E232
  let E234 : F := publicValues[15] - publicValues[47]
  let E235 : F := publicValues[0] * E234
  let E236 : F := publicValues[16] - publicValues[48]
  let E237 : F := publicValues[0] * E236
  let E238 : F := publicValues[17] - publicValues[49]
  let E239 : F := publicValues[0] * E238
  let E240 : F := publicValues[18] - publicValues[50]
  let E241 : F := publicValues[0] * E240
  let E242 : F := publicValues[19] - publicValues[51]
  let E243 : F := publicValues[0] * E242
  let E244 : F := publicValues[20] - publicValues[52]
  let E245 : F := publicValues[0] * E244
  let E246 : F := publicValues[21] - publicValues[53]
  let E247 : F := publicValues[0] * E246
  let E248 : F := publicValues[22] - publicValues[54]
  let E249 : F := publicValues[0] * E248
  let E250 : F := publicValues[23] - publicValues[55]
  let E251 : F := publicValues[0] * E250
  let E252 : F := publicValues[24] - publicValues[56]
  let E253 : F := publicValues[0] * E252
  let E254 : F := publicValues[25] - publicValues[57]
  let E255 : F := publicValues[0] * E254
  let E256 : F := publicValues[26] - publicValues[58]
  let E257 : F := publicValues[0] * E256
  let E258 : F := publicValues[27] - publicValues[59]
  let E259 : F := publicValues[0] * E258
  let E260 : F := publicValues[28] - publicValues[60]
  let E261 : F := publicValues[0] * E260
  let E262 : F := publicValues[29] - publicValues[61]
  let E263 : F := publicValues[0] * E262
  let E264 : F := publicValues[30] - publicValues[62]
  let E265 : F := publicValues[0] * E264
  let E266 : F := publicValues[31] - publicValues[63]
  let E267 : F := publicValues[0] * E266
  let E268 : F := publicValues[0] - publicValues[32]
  let E269 : F := publicValues[1] * E268
  let E270 : F := publicValues[1] - publicValues[33]
  let E271 : F := publicValues[1] * E270
  let E272 : F := publicValues[2] - publicValues[34]
  let E273 : F := publicValues[1] * E272
  let E274 : F := publicValues[3] - publicValues[35]
  let E275 : F := publicValues[1] * E274
  let E276 : F := publicValues[4] - publicValues[36]
  let E277 : F := publicValues[1] * E276
  let E278 : F := publicValues[5] - publicValues[37]
  let E279 : F := publicValues[1] * E278
  let E280 : F := publicValues[6] - publicValues[38]
  let E281 : F := publicValues[1] * E280
  let E282 : F := publicValues[7] - publicValues[39]
  let E283 : F := publicValues[1] * E282
  let E284 : F := publicValues[8] - publicValues[40]
  let E285 : F := publicValues[1] * E284
  let E286 : F := publicValues[9] - publicValues[41]
  let E287 : F := publicValues[1] * E286
  let E288 : F := publicValues[10] - publicValues[42]
  let E289 : F := publicValues[1] * E288
  let E290 : F := publicValues[11] - publicValues[43]
  let E291 : F := publicValues[1] * E290
  let E292 : F := publicValues[12] - publicValues[44]
  let E293 : F := publicValues[1] * E292
  let E294 : F := publicValues[13] - publicValues[45]
  let E295 : F := publicValues[1] * E294
  let E296 : F := publicValues[14] - publicValues[46]
  let E297 : F := publicValues[1] * E296
  let E298 : F := publicValues[15] - publicValues[47]
  let E299 : F := publicValues[1] * E298
  let E300 : F := publicValues[16] - publicValues[48]
  let E301 : F := publicValues[1] * E300
  let E302 : F := publicValues[17] - publicValues[49]
  let E303 : F := publicValues[1] * E302
  let E304 : F := publicValues[18] - publicValues[50]
  let E305 : F := publicValues[1] * E304
  let E306 : F := publicValues[19] - publicValues[51]
  let E307 : F := publicValues[1] * E306
  let E308 : F := publicValues[20] - publicValues[52]
  let E309 : F := publicValues[1] * E308
  let E310 : F := publicValues[21] - publicValues[53]
  let E311 : F := publicValues[1] * E310
  let E312 : F := publicValues[22] - publicValues[54]
  let E313 : F := publicValues[1] * E312
  let E314 : F := publicValues[23] - publicValues[55]
  let E315 : F := publicValues[1] * E314
  let E316 : F := publicValues[24] - publicValues[56]
  let E317 : F := publicValues[1] * E316
  let E318 : F := publicValues[25] - publicValues[57]
  let E319 : F := publicValues[1] * E318
  let E320 : F := publicValues[26] - publicValues[58]
  let E321 : F := publicValues[1] * E320
  let E322 : F := publicValues[27] - publicValues[59]
  let E323 : F := publicValues[1] * E322
  let E324 : F := publicValues[28] - publicValues[60]
  let E325 : F := publicValues[1] * E324
  let E326 : F := publicValues[29] - publicValues[61]
  let E327 : F := publicValues[1] * E326
  let E328 : F := publicValues[30] - publicValues[62]
  let E329 : F := publicValues[1] * E328
  let E330 : F := publicValues[31] - publicValues[63]
  let E331 : F := publicValues[1] * E330
  let E332 : F := publicValues[0] - publicValues[32]
  let E333 : F := publicValues[2] * E332
  let E334 : F := publicValues[1] - publicValues[33]
  let E335 : F := publicValues[2] * E334
  let E336 : F := publicValues[2] - publicValues[34]
  let E337 : F := publicValues[2] * E336
  let E338 : F := publicValues[3] - publicValues[35]
  let E339 : F := publicValues[2] * E338
  let E340 : F := publicValues[4] - publicValues[36]
  let E341 : F := publicValues[2] * E340
  let E342 : F := publicValues[5] - publicValues[37]
  let E343 : F := publicValues[2] * E342
  let E344 : F := publicValues[6] - publicValues[38]
  let E345 : F := publicValues[2] * E344
  let E346 : F := publicValues[7] - publicValues[39]
  let E347 : F := publicValues[2] * E346
  let E348 : F := publicValues[8] - publicValues[40]
  let E349 : F := publicValues[2] * E348
  let E350 : F := publicValues[9] - publicValues[41]
  let E351 : F := publicValues[2] * E350
  let E352 : F := publicValues[10] - publicValues[42]
  let E353 : F := publicValues[2] * E352
  [
    E227,
    E229,
    E231,
    E233,
    E235,
    E237,
    E239,
    E241,
    E243,
    E245,
    E247,
    E249,
    E251,
    E253,
    E255,
    E257,
    E259,
    E261,
    E263,
    E265,
    E267,
    E269,
    E271,
    E273,
    E275,
    E277,
    E279,
    E281,
    E283,
    E285,
    E287,
    E289,
    E291,
    E293,
    E295,
    E297,
    E299,
    E301,
    E303,
    E305,
    E307,
    E309,
    E311,
    E313,
    E315,
    E317,
    E319,
    E321,
    E323,
    E325,
    E327,
    E329,
    E331,
    E333,
    E335,
    E337,
    E339,
    E341,
    E343,
    E345,
    E347,
    E349,
    E351,
    E353,
  ]

@[irreducible] def assertsPart3 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E354 : F := publicValues[11] - publicValues[43]
  let E355 : F := publicValues[2] * E354
  let E356 : F := publicValues[12] - publicValues[44]
  let E357 : F := publicValues[2] * E356
  let E358 : F := publicValues[13] - publicValues[45]
  let E359 : F := publicValues[2] * E358
  let E360 : F := publicValues[14] - publicValues[46]
  let E361 : F := publicValues[2] * E360
  let E362 : F := publicValues[15] - publicValues[47]
  let E363 : F := publicValues[2] * E362
  let E364 : F := publicValues[16] - publicValues[48]
  let E365 : F := publicValues[2] * E364
  let E366 : F := publicValues[17] - publicValues[49]
  let E367 : F := publicValues[2] * E366
  let E368 : F := publicValues[18] - publicValues[50]
  let E369 : F := publicValues[2] * E368
  let E370 : F := publicValues[19] - publicValues[51]
  let E371 : F := publicValues[2] * E370
  let E372 : F := publicValues[20] - publicValues[52]
  let E373 : F := publicValues[2] * E372
  let E374 : F := publicValues[21] - publicValues[53]
  let E375 : F := publicValues[2] * E374
  let E376 : F := publicValues[22] - publicValues[54]
  let E377 : F := publicValues[2] * E376
  let E378 : F := publicValues[23] - publicValues[55]
  let E379 : F := publicValues[2] * E378
  let E380 : F := publicValues[24] - publicValues[56]
  let E381 : F := publicValues[2] * E380
  let E382 : F := publicValues[25] - publicValues[57]
  let E383 : F := publicValues[2] * E382
  let E384 : F := publicValues[26] - publicValues[58]
  let E385 : F := publicValues[2] * E384
  let E386 : F := publicValues[27] - publicValues[59]
  let E387 : F := publicValues[2] * E386
  let E388 : F := publicValues[28] - publicValues[60]
  let E389 : F := publicValues[2] * E388
  let E390 : F := publicValues[29] - publicValues[61]
  let E391 : F := publicValues[2] * E390
  let E392 : F := publicValues[30] - publicValues[62]
  let E393 : F := publicValues[2] * E392
  let E394 : F := publicValues[31] - publicValues[63]
  let E395 : F := publicValues[2] * E394
  let E396 : F := publicValues[0] - publicValues[32]
  let E397 : F := publicValues[3] * E396
  let E398 : F := publicValues[1] - publicValues[33]
  let E399 : F := publicValues[3] * E398
  let E400 : F := publicValues[2] - publicValues[34]
  let E401 : F := publicValues[3] * E400
  let E402 : F := publicValues[3] - publicValues[35]
  let E403 : F := publicValues[3] * E402
  let E404 : F := publicValues[4] - publicValues[36]
  let E405 : F := publicValues[3] * E404
  let E406 : F := publicValues[5] - publicValues[37]
  let E407 : F := publicValues[3] * E406
  let E408 : F := publicValues[6] - publicValues[38]
  let E409 : F := publicValues[3] * E408
  let E410 : F := publicValues[7] - publicValues[39]
  let E411 : F := publicValues[3] * E410
  let E412 : F := publicValues[8] - publicValues[40]
  let E413 : F := publicValues[3] * E412
  let E414 : F := publicValues[9] - publicValues[41]
  let E415 : F := publicValues[3] * E414
  let E416 : F := publicValues[10] - publicValues[42]
  let E417 : F := publicValues[3] * E416
  let E418 : F := publicValues[11] - publicValues[43]
  let E419 : F := publicValues[3] * E418
  let E420 : F := publicValues[12] - publicValues[44]
  let E421 : F := publicValues[3] * E420
  let E422 : F := publicValues[13] - publicValues[45]
  let E423 : F := publicValues[3] * E422
  let E424 : F := publicValues[14] - publicValues[46]
  let E425 : F := publicValues[3] * E424
  let E426 : F := publicValues[15] - publicValues[47]
  let E427 : F := publicValues[3] * E426
  let E428 : F := publicValues[16] - publicValues[48]
  let E429 : F := publicValues[3] * E428
  let E430 : F := publicValues[17] - publicValues[49]
  let E431 : F := publicValues[3] * E430
  let E432 : F := publicValues[18] - publicValues[50]
  let E433 : F := publicValues[3] * E432
  let E434 : F := publicValues[19] - publicValues[51]
  let E435 : F := publicValues[3] * E434
  let E436 : F := publicValues[20] - publicValues[52]
  let E437 : F := publicValues[3] * E436
  let E438 : F := publicValues[21] - publicValues[53]
  let E439 : F := publicValues[3] * E438
  let E440 : F := publicValues[22] - publicValues[54]
  let E441 : F := publicValues[3] * E440
  let E442 : F := publicValues[23] - publicValues[55]
  let E443 : F := publicValues[3] * E442
  let E444 : F := publicValues[24] - publicValues[56]
  let E445 : F := publicValues[3] * E444
  let E446 : F := publicValues[25] - publicValues[57]
  let E447 : F := publicValues[3] * E446
  let E448 : F := publicValues[26] - publicValues[58]
  let E449 : F := publicValues[3] * E448
  let E450 : F := publicValues[27] - publicValues[59]
  let E451 : F := publicValues[3] * E450
  let E452 : F := publicValues[28] - publicValues[60]
  let E453 : F := publicValues[3] * E452
  let E454 : F := publicValues[29] - publicValues[61]
  let E455 : F := publicValues[3] * E454
  let E456 : F := publicValues[30] - publicValues[62]
  let E457 : F := publicValues[3] * E456
  let E458 : F := publicValues[31] - publicValues[63]
  let E459 : F := publicValues[3] * E458
  let E460 : F := publicValues[0] - publicValues[32]
  let E461 : F := publicValues[4] * E460
  let E462 : F := publicValues[1] - publicValues[33]
  let E463 : F := publicValues[4] * E462
  let E464 : F := publicValues[2] - publicValues[34]
  let E465 : F := publicValues[4] * E464
  let E466 : F := publicValues[3] - publicValues[35]
  let E467 : F := publicValues[4] * E466
  let E468 : F := publicValues[4] - publicValues[36]
  let E469 : F := publicValues[4] * E468
  let E470 : F := publicValues[5] - publicValues[37]
  let E471 : F := publicValues[4] * E470
  let E472 : F := publicValues[6] - publicValues[38]
  let E473 : F := publicValues[4] * E472
  let E474 : F := publicValues[7] - publicValues[39]
  let E475 : F := publicValues[4] * E474
  let E476 : F := publicValues[8] - publicValues[40]
  let E477 : F := publicValues[4] * E476
  let E478 : F := publicValues[9] - publicValues[41]
  let E479 : F := publicValues[4] * E478
  let E480 : F := publicValues[10] - publicValues[42]
  let E481 : F := publicValues[4] * E480
  [
    E355,
    E357,
    E359,
    E361,
    E363,
    E365,
    E367,
    E369,
    E371,
    E373,
    E375,
    E377,
    E379,
    E381,
    E383,
    E385,
    E387,
    E389,
    E391,
    E393,
    E395,
    E397,
    E399,
    E401,
    E403,
    E405,
    E407,
    E409,
    E411,
    E413,
    E415,
    E417,
    E419,
    E421,
    E423,
    E425,
    E427,
    E429,
    E431,
    E433,
    E435,
    E437,
    E439,
    E441,
    E443,
    E445,
    E447,
    E449,
    E451,
    E453,
    E455,
    E457,
    E459,
    E461,
    E463,
    E465,
    E467,
    E469,
    E471,
    E473,
    E475,
    E477,
    E479,
    E481,
  ]

@[irreducible] def assertsPart4 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E482 : F := publicValues[11] - publicValues[43]
  let E483 : F := publicValues[4] * E482
  let E484 : F := publicValues[12] - publicValues[44]
  let E485 : F := publicValues[4] * E484
  let E486 : F := publicValues[13] - publicValues[45]
  let E487 : F := publicValues[4] * E486
  let E488 : F := publicValues[14] - publicValues[46]
  let E489 : F := publicValues[4] * E488
  let E490 : F := publicValues[15] - publicValues[47]
  let E491 : F := publicValues[4] * E490
  let E492 : F := publicValues[16] - publicValues[48]
  let E493 : F := publicValues[4] * E492
  let E494 : F := publicValues[17] - publicValues[49]
  let E495 : F := publicValues[4] * E494
  let E496 : F := publicValues[18] - publicValues[50]
  let E497 : F := publicValues[4] * E496
  let E498 : F := publicValues[19] - publicValues[51]
  let E499 : F := publicValues[4] * E498
  let E500 : F := publicValues[20] - publicValues[52]
  let E501 : F := publicValues[4] * E500
  let E502 : F := publicValues[21] - publicValues[53]
  let E503 : F := publicValues[4] * E502
  let E504 : F := publicValues[22] - publicValues[54]
  let E505 : F := publicValues[4] * E504
  let E506 : F := publicValues[23] - publicValues[55]
  let E507 : F := publicValues[4] * E506
  let E508 : F := publicValues[24] - publicValues[56]
  let E509 : F := publicValues[4] * E508
  let E510 : F := publicValues[25] - publicValues[57]
  let E511 : F := publicValues[4] * E510
  let E512 : F := publicValues[26] - publicValues[58]
  let E513 : F := publicValues[4] * E512
  let E514 : F := publicValues[27] - publicValues[59]
  let E515 : F := publicValues[4] * E514
  let E516 : F := publicValues[28] - publicValues[60]
  let E517 : F := publicValues[4] * E516
  let E518 : F := publicValues[29] - publicValues[61]
  let E519 : F := publicValues[4] * E518
  let E520 : F := publicValues[30] - publicValues[62]
  let E521 : F := publicValues[4] * E520
  let E522 : F := publicValues[31] - publicValues[63]
  let E523 : F := publicValues[4] * E522
  let E524 : F := publicValues[0] - publicValues[32]
  let E525 : F := publicValues[5] * E524
  let E526 : F := publicValues[1] - publicValues[33]
  let E527 : F := publicValues[5] * E526
  let E528 : F := publicValues[2] - publicValues[34]
  let E529 : F := publicValues[5] * E528
  let E530 : F := publicValues[3] - publicValues[35]
  let E531 : F := publicValues[5] * E530
  let E532 : F := publicValues[4] - publicValues[36]
  let E533 : F := publicValues[5] * E532
  let E534 : F := publicValues[5] - publicValues[37]
  let E535 : F := publicValues[5] * E534
  let E536 : F := publicValues[6] - publicValues[38]
  let E537 : F := publicValues[5] * E536
  let E538 : F := publicValues[7] - publicValues[39]
  let E539 : F := publicValues[5] * E538
  let E540 : F := publicValues[8] - publicValues[40]
  let E541 : F := publicValues[5] * E540
  let E542 : F := publicValues[9] - publicValues[41]
  let E543 : F := publicValues[5] * E542
  let E544 : F := publicValues[10] - publicValues[42]
  let E545 : F := publicValues[5] * E544
  let E546 : F := publicValues[11] - publicValues[43]
  let E547 : F := publicValues[5] * E546
  let E548 : F := publicValues[12] - publicValues[44]
  let E549 : F := publicValues[5] * E548
  let E550 : F := publicValues[13] - publicValues[45]
  let E551 : F := publicValues[5] * E550
  let E552 : F := publicValues[14] - publicValues[46]
  let E553 : F := publicValues[5] * E552
  let E554 : F := publicValues[15] - publicValues[47]
  let E555 : F := publicValues[5] * E554
  let E556 : F := publicValues[16] - publicValues[48]
  let E557 : F := publicValues[5] * E556
  let E558 : F := publicValues[17] - publicValues[49]
  let E559 : F := publicValues[5] * E558
  let E560 : F := publicValues[18] - publicValues[50]
  let E561 : F := publicValues[5] * E560
  let E562 : F := publicValues[19] - publicValues[51]
  let E563 : F := publicValues[5] * E562
  let E564 : F := publicValues[20] - publicValues[52]
  let E565 : F := publicValues[5] * E564
  let E566 : F := publicValues[21] - publicValues[53]
  let E567 : F := publicValues[5] * E566
  let E568 : F := publicValues[22] - publicValues[54]
  let E569 : F := publicValues[5] * E568
  let E570 : F := publicValues[23] - publicValues[55]
  let E571 : F := publicValues[5] * E570
  let E572 : F := publicValues[24] - publicValues[56]
  let E573 : F := publicValues[5] * E572
  let E574 : F := publicValues[25] - publicValues[57]
  let E575 : F := publicValues[5] * E574
  let E576 : F := publicValues[26] - publicValues[58]
  let E577 : F := publicValues[5] * E576
  let E578 : F := publicValues[27] - publicValues[59]
  let E579 : F := publicValues[5] * E578
  let E580 : F := publicValues[28] - publicValues[60]
  let E581 : F := publicValues[5] * E580
  let E582 : F := publicValues[29] - publicValues[61]
  let E583 : F := publicValues[5] * E582
  let E584 : F := publicValues[30] - publicValues[62]
  let E585 : F := publicValues[5] * E584
  let E586 : F := publicValues[31] - publicValues[63]
  let E587 : F := publicValues[5] * E586
  let E588 : F := publicValues[0] - publicValues[32]
  let E589 : F := publicValues[6] * E588
  let E590 : F := publicValues[1] - publicValues[33]
  let E591 : F := publicValues[6] * E590
  let E592 : F := publicValues[2] - publicValues[34]
  let E593 : F := publicValues[6] * E592
  let E594 : F := publicValues[3] - publicValues[35]
  let E595 : F := publicValues[6] * E594
  let E596 : F := publicValues[4] - publicValues[36]
  let E597 : F := publicValues[6] * E596
  let E598 : F := publicValues[5] - publicValues[37]
  let E599 : F := publicValues[6] * E598
  let E600 : F := publicValues[6] - publicValues[38]
  let E601 : F := publicValues[6] * E600
  let E602 : F := publicValues[7] - publicValues[39]
  let E603 : F := publicValues[6] * E602
  let E604 : F := publicValues[8] - publicValues[40]
  let E605 : F := publicValues[6] * E604
  let E606 : F := publicValues[9] - publicValues[41]
  let E607 : F := publicValues[6] * E606
  let E608 : F := publicValues[10] - publicValues[42]
  let E609 : F := publicValues[6] * E608
  [
    E483,
    E485,
    E487,
    E489,
    E491,
    E493,
    E495,
    E497,
    E499,
    E501,
    E503,
    E505,
    E507,
    E509,
    E511,
    E513,
    E515,
    E517,
    E519,
    E521,
    E523,
    E525,
    E527,
    E529,
    E531,
    E533,
    E535,
    E537,
    E539,
    E541,
    E543,
    E545,
    E547,
    E549,
    E551,
    E553,
    E555,
    E557,
    E559,
    E561,
    E563,
    E565,
    E567,
    E569,
    E571,
    E573,
    E575,
    E577,
    E579,
    E581,
    E583,
    E585,
    E587,
    E589,
    E591,
    E593,
    E595,
    E597,
    E599,
    E601,
    E603,
    E605,
    E607,
    E609,
  ]

@[irreducible] def assertsPart5 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E610 : F := publicValues[11] - publicValues[43]
  let E611 : F := publicValues[6] * E610
  let E612 : F := publicValues[12] - publicValues[44]
  let E613 : F := publicValues[6] * E612
  let E614 : F := publicValues[13] - publicValues[45]
  let E615 : F := publicValues[6] * E614
  let E616 : F := publicValues[14] - publicValues[46]
  let E617 : F := publicValues[6] * E616
  let E618 : F := publicValues[15] - publicValues[47]
  let E619 : F := publicValues[6] * E618
  let E620 : F := publicValues[16] - publicValues[48]
  let E621 : F := publicValues[6] * E620
  let E622 : F := publicValues[17] - publicValues[49]
  let E623 : F := publicValues[6] * E622
  let E624 : F := publicValues[18] - publicValues[50]
  let E625 : F := publicValues[6] * E624
  let E626 : F := publicValues[19] - publicValues[51]
  let E627 : F := publicValues[6] * E626
  let E628 : F := publicValues[20] - publicValues[52]
  let E629 : F := publicValues[6] * E628
  let E630 : F := publicValues[21] - publicValues[53]
  let E631 : F := publicValues[6] * E630
  let E632 : F := publicValues[22] - publicValues[54]
  let E633 : F := publicValues[6] * E632
  let E634 : F := publicValues[23] - publicValues[55]
  let E635 : F := publicValues[6] * E634
  let E636 : F := publicValues[24] - publicValues[56]
  let E637 : F := publicValues[6] * E636
  let E638 : F := publicValues[25] - publicValues[57]
  let E639 : F := publicValues[6] * E638
  let E640 : F := publicValues[26] - publicValues[58]
  let E641 : F := publicValues[6] * E640
  let E642 : F := publicValues[27] - publicValues[59]
  let E643 : F := publicValues[6] * E642
  let E644 : F := publicValues[28] - publicValues[60]
  let E645 : F := publicValues[6] * E644
  let E646 : F := publicValues[29] - publicValues[61]
  let E647 : F := publicValues[6] * E646
  let E648 : F := publicValues[30] - publicValues[62]
  let E649 : F := publicValues[6] * E648
  let E650 : F := publicValues[31] - publicValues[63]
  let E651 : F := publicValues[6] * E650
  let E652 : F := publicValues[0] - publicValues[32]
  let E653 : F := publicValues[7] * E652
  let E654 : F := publicValues[1] - publicValues[33]
  let E655 : F := publicValues[7] * E654
  let E656 : F := publicValues[2] - publicValues[34]
  let E657 : F := publicValues[7] * E656
  let E658 : F := publicValues[3] - publicValues[35]
  let E659 : F := publicValues[7] * E658
  let E660 : F := publicValues[4] - publicValues[36]
  let E661 : F := publicValues[7] * E660
  let E662 : F := publicValues[5] - publicValues[37]
  let E663 : F := publicValues[7] * E662
  let E664 : F := publicValues[6] - publicValues[38]
  let E665 : F := publicValues[7] * E664
  let E666 : F := publicValues[7] - publicValues[39]
  let E667 : F := publicValues[7] * E666
  let E668 : F := publicValues[8] - publicValues[40]
  let E669 : F := publicValues[7] * E668
  let E670 : F := publicValues[9] - publicValues[41]
  let E671 : F := publicValues[7] * E670
  let E672 : F := publicValues[10] - publicValues[42]
  let E673 : F := publicValues[7] * E672
  let E674 : F := publicValues[11] - publicValues[43]
  let E675 : F := publicValues[7] * E674
  let E676 : F := publicValues[12] - publicValues[44]
  let E677 : F := publicValues[7] * E676
  let E678 : F := publicValues[13] - publicValues[45]
  let E679 : F := publicValues[7] * E678
  let E680 : F := publicValues[14] - publicValues[46]
  let E681 : F := publicValues[7] * E680
  let E682 : F := publicValues[15] - publicValues[47]
  let E683 : F := publicValues[7] * E682
  let E684 : F := publicValues[16] - publicValues[48]
  let E685 : F := publicValues[7] * E684
  let E686 : F := publicValues[17] - publicValues[49]
  let E687 : F := publicValues[7] * E686
  let E688 : F := publicValues[18] - publicValues[50]
  let E689 : F := publicValues[7] * E688
  let E690 : F := publicValues[19] - publicValues[51]
  let E691 : F := publicValues[7] * E690
  let E692 : F := publicValues[20] - publicValues[52]
  let E693 : F := publicValues[7] * E692
  let E694 : F := publicValues[21] - publicValues[53]
  let E695 : F := publicValues[7] * E694
  let E696 : F := publicValues[22] - publicValues[54]
  let E697 : F := publicValues[7] * E696
  let E698 : F := publicValues[23] - publicValues[55]
  let E699 : F := publicValues[7] * E698
  let E700 : F := publicValues[24] - publicValues[56]
  let E701 : F := publicValues[7] * E700
  let E702 : F := publicValues[25] - publicValues[57]
  let E703 : F := publicValues[7] * E702
  let E704 : F := publicValues[26] - publicValues[58]
  let E705 : F := publicValues[7] * E704
  let E706 : F := publicValues[27] - publicValues[59]
  let E707 : F := publicValues[7] * E706
  let E708 : F := publicValues[28] - publicValues[60]
  let E709 : F := publicValues[7] * E708
  let E710 : F := publicValues[29] - publicValues[61]
  let E711 : F := publicValues[7] * E710
  let E712 : F := publicValues[30] - publicValues[62]
  let E713 : F := publicValues[7] * E712
  let E714 : F := publicValues[31] - publicValues[63]
  let E715 : F := publicValues[7] * E714
  let E716 : F := publicValues[0] - publicValues[32]
  let E717 : F := publicValues[8] * E716
  let E718 : F := publicValues[1] - publicValues[33]
  let E719 : F := publicValues[8] * E718
  let E720 : F := publicValues[2] - publicValues[34]
  let E721 : F := publicValues[8] * E720
  let E722 : F := publicValues[3] - publicValues[35]
  let E723 : F := publicValues[8] * E722
  let E724 : F := publicValues[4] - publicValues[36]
  let E725 : F := publicValues[8] * E724
  let E726 : F := publicValues[5] - publicValues[37]
  let E727 : F := publicValues[8] * E726
  let E728 : F := publicValues[6] - publicValues[38]
  let E729 : F := publicValues[8] * E728
  let E730 : F := publicValues[7] - publicValues[39]
  let E731 : F := publicValues[8] * E730
  let E732 : F := publicValues[8] - publicValues[40]
  let E733 : F := publicValues[8] * E732
  let E734 : F := publicValues[9] - publicValues[41]
  let E735 : F := publicValues[8] * E734
  let E736 : F := publicValues[10] - publicValues[42]
  let E737 : F := publicValues[8] * E736
  [
    E611,
    E613,
    E615,
    E617,
    E619,
    E621,
    E623,
    E625,
    E627,
    E629,
    E631,
    E633,
    E635,
    E637,
    E639,
    E641,
    E643,
    E645,
    E647,
    E649,
    E651,
    E653,
    E655,
    E657,
    E659,
    E661,
    E663,
    E665,
    E667,
    E669,
    E671,
    E673,
    E675,
    E677,
    E679,
    E681,
    E683,
    E685,
    E687,
    E689,
    E691,
    E693,
    E695,
    E697,
    E699,
    E701,
    E703,
    E705,
    E707,
    E709,
    E711,
    E713,
    E715,
    E717,
    E719,
    E721,
    E723,
    E725,
    E727,
    E729,
    E731,
    E733,
    E735,
    E737,
  ]

@[irreducible] def assertsPart6 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E738 : F := publicValues[11] - publicValues[43]
  let E739 : F := publicValues[8] * E738
  let E740 : F := publicValues[12] - publicValues[44]
  let E741 : F := publicValues[8] * E740
  let E742 : F := publicValues[13] - publicValues[45]
  let E743 : F := publicValues[8] * E742
  let E744 : F := publicValues[14] - publicValues[46]
  let E745 : F := publicValues[8] * E744
  let E746 : F := publicValues[15] - publicValues[47]
  let E747 : F := publicValues[8] * E746
  let E748 : F := publicValues[16] - publicValues[48]
  let E749 : F := publicValues[8] * E748
  let E750 : F := publicValues[17] - publicValues[49]
  let E751 : F := publicValues[8] * E750
  let E752 : F := publicValues[18] - publicValues[50]
  let E753 : F := publicValues[8] * E752
  let E754 : F := publicValues[19] - publicValues[51]
  let E755 : F := publicValues[8] * E754
  let E756 : F := publicValues[20] - publicValues[52]
  let E757 : F := publicValues[8] * E756
  let E758 : F := publicValues[21] - publicValues[53]
  let E759 : F := publicValues[8] * E758
  let E760 : F := publicValues[22] - publicValues[54]
  let E761 : F := publicValues[8] * E760
  let E762 : F := publicValues[23] - publicValues[55]
  let E763 : F := publicValues[8] * E762
  let E764 : F := publicValues[24] - publicValues[56]
  let E765 : F := publicValues[8] * E764
  let E766 : F := publicValues[25] - publicValues[57]
  let E767 : F := publicValues[8] * E766
  let E768 : F := publicValues[26] - publicValues[58]
  let E769 : F := publicValues[8] * E768
  let E770 : F := publicValues[27] - publicValues[59]
  let E771 : F := publicValues[8] * E770
  let E772 : F := publicValues[28] - publicValues[60]
  let E773 : F := publicValues[8] * E772
  let E774 : F := publicValues[29] - publicValues[61]
  let E775 : F := publicValues[8] * E774
  let E776 : F := publicValues[30] - publicValues[62]
  let E777 : F := publicValues[8] * E776
  let E778 : F := publicValues[31] - publicValues[63]
  let E779 : F := publicValues[8] * E778
  let E780 : F := publicValues[0] - publicValues[32]
  let E781 : F := publicValues[9] * E780
  let E782 : F := publicValues[1] - publicValues[33]
  let E783 : F := publicValues[9] * E782
  let E784 : F := publicValues[2] - publicValues[34]
  let E785 : F := publicValues[9] * E784
  let E786 : F := publicValues[3] - publicValues[35]
  let E787 : F := publicValues[9] * E786
  let E788 : F := publicValues[4] - publicValues[36]
  let E789 : F := publicValues[9] * E788
  let E790 : F := publicValues[5] - publicValues[37]
  let E791 : F := publicValues[9] * E790
  let E792 : F := publicValues[6] - publicValues[38]
  let E793 : F := publicValues[9] * E792
  let E794 : F := publicValues[7] - publicValues[39]
  let E795 : F := publicValues[9] * E794
  let E796 : F := publicValues[8] - publicValues[40]
  let E797 : F := publicValues[9] * E796
  let E798 : F := publicValues[9] - publicValues[41]
  let E799 : F := publicValues[9] * E798
  let E800 : F := publicValues[10] - publicValues[42]
  let E801 : F := publicValues[9] * E800
  let E802 : F := publicValues[11] - publicValues[43]
  let E803 : F := publicValues[9] * E802
  let E804 : F := publicValues[12] - publicValues[44]
  let E805 : F := publicValues[9] * E804
  let E806 : F := publicValues[13] - publicValues[45]
  let E807 : F := publicValues[9] * E806
  let E808 : F := publicValues[14] - publicValues[46]
  let E809 : F := publicValues[9] * E808
  let E810 : F := publicValues[15] - publicValues[47]
  let E811 : F := publicValues[9] * E810
  let E812 : F := publicValues[16] - publicValues[48]
  let E813 : F := publicValues[9] * E812
  let E814 : F := publicValues[17] - publicValues[49]
  let E815 : F := publicValues[9] * E814
  let E816 : F := publicValues[18] - publicValues[50]
  let E817 : F := publicValues[9] * E816
  let E818 : F := publicValues[19] - publicValues[51]
  let E819 : F := publicValues[9] * E818
  let E820 : F := publicValues[20] - publicValues[52]
  let E821 : F := publicValues[9] * E820
  let E822 : F := publicValues[21] - publicValues[53]
  let E823 : F := publicValues[9] * E822
  let E824 : F := publicValues[22] - publicValues[54]
  let E825 : F := publicValues[9] * E824
  let E826 : F := publicValues[23] - publicValues[55]
  let E827 : F := publicValues[9] * E826
  let E828 : F := publicValues[24] - publicValues[56]
  let E829 : F := publicValues[9] * E828
  let E830 : F := publicValues[25] - publicValues[57]
  let E831 : F := publicValues[9] * E830
  let E832 : F := publicValues[26] - publicValues[58]
  let E833 : F := publicValues[9] * E832
  let E834 : F := publicValues[27] - publicValues[59]
  let E835 : F := publicValues[9] * E834
  let E836 : F := publicValues[28] - publicValues[60]
  let E837 : F := publicValues[9] * E836
  let E838 : F := publicValues[29] - publicValues[61]
  let E839 : F := publicValues[9] * E838
  let E840 : F := publicValues[30] - publicValues[62]
  let E841 : F := publicValues[9] * E840
  let E842 : F := publicValues[31] - publicValues[63]
  let E843 : F := publicValues[9] * E842
  let E844 : F := publicValues[0] - publicValues[32]
  let E845 : F := publicValues[10] * E844
  let E846 : F := publicValues[1] - publicValues[33]
  let E847 : F := publicValues[10] * E846
  let E848 : F := publicValues[2] - publicValues[34]
  let E849 : F := publicValues[10] * E848
  let E850 : F := publicValues[3] - publicValues[35]
  let E851 : F := publicValues[10] * E850
  let E852 : F := publicValues[4] - publicValues[36]
  let E853 : F := publicValues[10] * E852
  let E854 : F := publicValues[5] - publicValues[37]
  let E855 : F := publicValues[10] * E854
  let E856 : F := publicValues[6] - publicValues[38]
  let E857 : F := publicValues[10] * E856
  let E858 : F := publicValues[7] - publicValues[39]
  let E859 : F := publicValues[10] * E858
  let E860 : F := publicValues[8] - publicValues[40]
  let E861 : F := publicValues[10] * E860
  let E862 : F := publicValues[9] - publicValues[41]
  let E863 : F := publicValues[10] * E862
  let E864 : F := publicValues[10] - publicValues[42]
  let E865 : F := publicValues[10] * E864
  [
    E739,
    E741,
    E743,
    E745,
    E747,
    E749,
    E751,
    E753,
    E755,
    E757,
    E759,
    E761,
    E763,
    E765,
    E767,
    E769,
    E771,
    E773,
    E775,
    E777,
    E779,
    E781,
    E783,
    E785,
    E787,
    E789,
    E791,
    E793,
    E795,
    E797,
    E799,
    E801,
    E803,
    E805,
    E807,
    E809,
    E811,
    E813,
    E815,
    E817,
    E819,
    E821,
    E823,
    E825,
    E827,
    E829,
    E831,
    E833,
    E835,
    E837,
    E839,
    E841,
    E843,
    E845,
    E847,
    E849,
    E851,
    E853,
    E855,
    E857,
    E859,
    E861,
    E863,
    E865,
  ]

@[irreducible] def assertsPart7 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E866 : F := publicValues[11] - publicValues[43]
  let E867 : F := publicValues[10] * E866
  let E868 : F := publicValues[12] - publicValues[44]
  let E869 : F := publicValues[10] * E868
  let E870 : F := publicValues[13] - publicValues[45]
  let E871 : F := publicValues[10] * E870
  let E872 : F := publicValues[14] - publicValues[46]
  let E873 : F := publicValues[10] * E872
  let E874 : F := publicValues[15] - publicValues[47]
  let E875 : F := publicValues[10] * E874
  let E876 : F := publicValues[16] - publicValues[48]
  let E877 : F := publicValues[10] * E876
  let E878 : F := publicValues[17] - publicValues[49]
  let E879 : F := publicValues[10] * E878
  let E880 : F := publicValues[18] - publicValues[50]
  let E881 : F := publicValues[10] * E880
  let E882 : F := publicValues[19] - publicValues[51]
  let E883 : F := publicValues[10] * E882
  let E884 : F := publicValues[20] - publicValues[52]
  let E885 : F := publicValues[10] * E884
  let E886 : F := publicValues[21] - publicValues[53]
  let E887 : F := publicValues[10] * E886
  let E888 : F := publicValues[22] - publicValues[54]
  let E889 : F := publicValues[10] * E888
  let E890 : F := publicValues[23] - publicValues[55]
  let E891 : F := publicValues[10] * E890
  let E892 : F := publicValues[24] - publicValues[56]
  let E893 : F := publicValues[10] * E892
  let E894 : F := publicValues[25] - publicValues[57]
  let E895 : F := publicValues[10] * E894
  let E896 : F := publicValues[26] - publicValues[58]
  let E897 : F := publicValues[10] * E896
  let E898 : F := publicValues[27] - publicValues[59]
  let E899 : F := publicValues[10] * E898
  let E900 : F := publicValues[28] - publicValues[60]
  let E901 : F := publicValues[10] * E900
  let E902 : F := publicValues[29] - publicValues[61]
  let E903 : F := publicValues[10] * E902
  let E904 : F := publicValues[30] - publicValues[62]
  let E905 : F := publicValues[10] * E904
  let E906 : F := publicValues[31] - publicValues[63]
  let E907 : F := publicValues[10] * E906
  let E908 : F := publicValues[0] - publicValues[32]
  let E909 : F := publicValues[11] * E908
  let E910 : F := publicValues[1] - publicValues[33]
  let E911 : F := publicValues[11] * E910
  let E912 : F := publicValues[2] - publicValues[34]
  let E913 : F := publicValues[11] * E912
  let E914 : F := publicValues[3] - publicValues[35]
  let E915 : F := publicValues[11] * E914
  let E916 : F := publicValues[4] - publicValues[36]
  let E917 : F := publicValues[11] * E916
  let E918 : F := publicValues[5] - publicValues[37]
  let E919 : F := publicValues[11] * E918
  let E920 : F := publicValues[6] - publicValues[38]
  let E921 : F := publicValues[11] * E920
  let E922 : F := publicValues[7] - publicValues[39]
  let E923 : F := publicValues[11] * E922
  let E924 : F := publicValues[8] - publicValues[40]
  let E925 : F := publicValues[11] * E924
  let E926 : F := publicValues[9] - publicValues[41]
  let E927 : F := publicValues[11] * E926
  let E928 : F := publicValues[10] - publicValues[42]
  let E929 : F := publicValues[11] * E928
  let E930 : F := publicValues[11] - publicValues[43]
  let E931 : F := publicValues[11] * E930
  let E932 : F := publicValues[12] - publicValues[44]
  let E933 : F := publicValues[11] * E932
  let E934 : F := publicValues[13] - publicValues[45]
  let E935 : F := publicValues[11] * E934
  let E936 : F := publicValues[14] - publicValues[46]
  let E937 : F := publicValues[11] * E936
  let E938 : F := publicValues[15] - publicValues[47]
  let E939 : F := publicValues[11] * E938
  let E940 : F := publicValues[16] - publicValues[48]
  let E941 : F := publicValues[11] * E940
  let E942 : F := publicValues[17] - publicValues[49]
  let E943 : F := publicValues[11] * E942
  let E944 : F := publicValues[18] - publicValues[50]
  let E945 : F := publicValues[11] * E944
  let E946 : F := publicValues[19] - publicValues[51]
  let E947 : F := publicValues[11] * E946
  let E948 : F := publicValues[20] - publicValues[52]
  let E949 : F := publicValues[11] * E948
  let E950 : F := publicValues[21] - publicValues[53]
  let E951 : F := publicValues[11] * E950
  let E952 : F := publicValues[22] - publicValues[54]
  let E953 : F := publicValues[11] * E952
  let E954 : F := publicValues[23] - publicValues[55]
  let E955 : F := publicValues[11] * E954
  let E956 : F := publicValues[24] - publicValues[56]
  let E957 : F := publicValues[11] * E956
  let E958 : F := publicValues[25] - publicValues[57]
  let E959 : F := publicValues[11] * E958
  let E960 : F := publicValues[26] - publicValues[58]
  let E961 : F := publicValues[11] * E960
  let E962 : F := publicValues[27] - publicValues[59]
  let E963 : F := publicValues[11] * E962
  let E964 : F := publicValues[28] - publicValues[60]
  let E965 : F := publicValues[11] * E964
  let E966 : F := publicValues[29] - publicValues[61]
  let E967 : F := publicValues[11] * E966
  let E968 : F := publicValues[30] - publicValues[62]
  let E969 : F := publicValues[11] * E968
  let E970 : F := publicValues[31] - publicValues[63]
  let E971 : F := publicValues[11] * E970
  let E972 : F := publicValues[0] - publicValues[32]
  let E973 : F := publicValues[12] * E972
  let E974 : F := publicValues[1] - publicValues[33]
  let E975 : F := publicValues[12] * E974
  let E976 : F := publicValues[2] - publicValues[34]
  let E977 : F := publicValues[12] * E976
  let E978 : F := publicValues[3] - publicValues[35]
  let E979 : F := publicValues[12] * E978
  let E980 : F := publicValues[4] - publicValues[36]
  let E981 : F := publicValues[12] * E980
  let E982 : F := publicValues[5] - publicValues[37]
  let E983 : F := publicValues[12] * E982
  let E984 : F := publicValues[6] - publicValues[38]
  let E985 : F := publicValues[12] * E984
  let E986 : F := publicValues[7] - publicValues[39]
  let E987 : F := publicValues[12] * E986
  let E988 : F := publicValues[8] - publicValues[40]
  let E989 : F := publicValues[12] * E988
  let E990 : F := publicValues[9] - publicValues[41]
  let E991 : F := publicValues[12] * E990
  let E992 : F := publicValues[10] - publicValues[42]
  let E993 : F := publicValues[12] * E992
  [
    E867,
    E869,
    E871,
    E873,
    E875,
    E877,
    E879,
    E881,
    E883,
    E885,
    E887,
    E889,
    E891,
    E893,
    E895,
    E897,
    E899,
    E901,
    E903,
    E905,
    E907,
    E909,
    E911,
    E913,
    E915,
    E917,
    E919,
    E921,
    E923,
    E925,
    E927,
    E929,
    E931,
    E933,
    E935,
    E937,
    E939,
    E941,
    E943,
    E945,
    E947,
    E949,
    E951,
    E953,
    E955,
    E957,
    E959,
    E961,
    E963,
    E965,
    E967,
    E969,
    E971,
    E973,
    E975,
    E977,
    E979,
    E981,
    E983,
    E985,
    E987,
    E989,
    E991,
    E993,
  ]

@[irreducible] def assertsPart8 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E994 : F := publicValues[11] - publicValues[43]
  let E995 : F := publicValues[12] * E994
  let E996 : F := publicValues[12] - publicValues[44]
  let E997 : F := publicValues[12] * E996
  let E998 : F := publicValues[13] - publicValues[45]
  let E999 : F := publicValues[12] * E998
  let E1000 : F := publicValues[14] - publicValues[46]
  let E1001 : F := publicValues[12] * E1000
  let E1002 : F := publicValues[15] - publicValues[47]
  let E1003 : F := publicValues[12] * E1002
  let E1004 : F := publicValues[16] - publicValues[48]
  let E1005 : F := publicValues[12] * E1004
  let E1006 : F := publicValues[17] - publicValues[49]
  let E1007 : F := publicValues[12] * E1006
  let E1008 : F := publicValues[18] - publicValues[50]
  let E1009 : F := publicValues[12] * E1008
  let E1010 : F := publicValues[19] - publicValues[51]
  let E1011 : F := publicValues[12] * E1010
  let E1012 : F := publicValues[20] - publicValues[52]
  let E1013 : F := publicValues[12] * E1012
  let E1014 : F := publicValues[21] - publicValues[53]
  let E1015 : F := publicValues[12] * E1014
  let E1016 : F := publicValues[22] - publicValues[54]
  let E1017 : F := publicValues[12] * E1016
  let E1018 : F := publicValues[23] - publicValues[55]
  let E1019 : F := publicValues[12] * E1018
  let E1020 : F := publicValues[24] - publicValues[56]
  let E1021 : F := publicValues[12] * E1020
  let E1022 : F := publicValues[25] - publicValues[57]
  let E1023 : F := publicValues[12] * E1022
  let E1024 : F := publicValues[26] - publicValues[58]
  let E1025 : F := publicValues[12] * E1024
  let E1026 : F := publicValues[27] - publicValues[59]
  let E1027 : F := publicValues[12] * E1026
  let E1028 : F := publicValues[28] - publicValues[60]
  let E1029 : F := publicValues[12] * E1028
  let E1030 : F := publicValues[29] - publicValues[61]
  let E1031 : F := publicValues[12] * E1030
  let E1032 : F := publicValues[30] - publicValues[62]
  let E1033 : F := publicValues[12] * E1032
  let E1034 : F := publicValues[31] - publicValues[63]
  let E1035 : F := publicValues[12] * E1034
  let E1036 : F := publicValues[0] - publicValues[32]
  let E1037 : F := publicValues[13] * E1036
  let E1038 : F := publicValues[1] - publicValues[33]
  let E1039 : F := publicValues[13] * E1038
  let E1040 : F := publicValues[2] - publicValues[34]
  let E1041 : F := publicValues[13] * E1040
  let E1042 : F := publicValues[3] - publicValues[35]
  let E1043 : F := publicValues[13] * E1042
  let E1044 : F := publicValues[4] - publicValues[36]
  let E1045 : F := publicValues[13] * E1044
  let E1046 : F := publicValues[5] - publicValues[37]
  let E1047 : F := publicValues[13] * E1046
  let E1048 : F := publicValues[6] - publicValues[38]
  let E1049 : F := publicValues[13] * E1048
  let E1050 : F := publicValues[7] - publicValues[39]
  let E1051 : F := publicValues[13] * E1050
  let E1052 : F := publicValues[8] - publicValues[40]
  let E1053 : F := publicValues[13] * E1052
  let E1054 : F := publicValues[9] - publicValues[41]
  let E1055 : F := publicValues[13] * E1054
  let E1056 : F := publicValues[10] - publicValues[42]
  let E1057 : F := publicValues[13] * E1056
  let E1058 : F := publicValues[11] - publicValues[43]
  let E1059 : F := publicValues[13] * E1058
  let E1060 : F := publicValues[12] - publicValues[44]
  let E1061 : F := publicValues[13] * E1060
  let E1062 : F := publicValues[13] - publicValues[45]
  let E1063 : F := publicValues[13] * E1062
  let E1064 : F := publicValues[14] - publicValues[46]
  let E1065 : F := publicValues[13] * E1064
  let E1066 : F := publicValues[15] - publicValues[47]
  let E1067 : F := publicValues[13] * E1066
  let E1068 : F := publicValues[16] - publicValues[48]
  let E1069 : F := publicValues[13] * E1068
  let E1070 : F := publicValues[17] - publicValues[49]
  let E1071 : F := publicValues[13] * E1070
  let E1072 : F := publicValues[18] - publicValues[50]
  let E1073 : F := publicValues[13] * E1072
  let E1074 : F := publicValues[19] - publicValues[51]
  let E1075 : F := publicValues[13] * E1074
  let E1076 : F := publicValues[20] - publicValues[52]
  let E1077 : F := publicValues[13] * E1076
  let E1078 : F := publicValues[21] - publicValues[53]
  let E1079 : F := publicValues[13] * E1078
  let E1080 : F := publicValues[22] - publicValues[54]
  let E1081 : F := publicValues[13] * E1080
  let E1082 : F := publicValues[23] - publicValues[55]
  let E1083 : F := publicValues[13] * E1082
  let E1084 : F := publicValues[24] - publicValues[56]
  let E1085 : F := publicValues[13] * E1084
  let E1086 : F := publicValues[25] - publicValues[57]
  let E1087 : F := publicValues[13] * E1086
  let E1088 : F := publicValues[26] - publicValues[58]
  let E1089 : F := publicValues[13] * E1088
  let E1090 : F := publicValues[27] - publicValues[59]
  let E1091 : F := publicValues[13] * E1090
  let E1092 : F := publicValues[28] - publicValues[60]
  let E1093 : F := publicValues[13] * E1092
  let E1094 : F := publicValues[29] - publicValues[61]
  let E1095 : F := publicValues[13] * E1094
  let E1096 : F := publicValues[30] - publicValues[62]
  let E1097 : F := publicValues[13] * E1096
  let E1098 : F := publicValues[31] - publicValues[63]
  let E1099 : F := publicValues[13] * E1098
  let E1100 : F := publicValues[0] - publicValues[32]
  let E1101 : F := publicValues[14] * E1100
  let E1102 : F := publicValues[1] - publicValues[33]
  let E1103 : F := publicValues[14] * E1102
  let E1104 : F := publicValues[2] - publicValues[34]
  let E1105 : F := publicValues[14] * E1104
  let E1106 : F := publicValues[3] - publicValues[35]
  let E1107 : F := publicValues[14] * E1106
  let E1108 : F := publicValues[4] - publicValues[36]
  let E1109 : F := publicValues[14] * E1108
  let E1110 : F := publicValues[5] - publicValues[37]
  let E1111 : F := publicValues[14] * E1110
  let E1112 : F := publicValues[6] - publicValues[38]
  let E1113 : F := publicValues[14] * E1112
  let E1114 : F := publicValues[7] - publicValues[39]
  let E1115 : F := publicValues[14] * E1114
  let E1116 : F := publicValues[8] - publicValues[40]
  let E1117 : F := publicValues[14] * E1116
  let E1118 : F := publicValues[9] - publicValues[41]
  let E1119 : F := publicValues[14] * E1118
  let E1120 : F := publicValues[10] - publicValues[42]
  let E1121 : F := publicValues[14] * E1120
  [
    E995,
    E997,
    E999,
    E1001,
    E1003,
    E1005,
    E1007,
    E1009,
    E1011,
    E1013,
    E1015,
    E1017,
    E1019,
    E1021,
    E1023,
    E1025,
    E1027,
    E1029,
    E1031,
    E1033,
    E1035,
    E1037,
    E1039,
    E1041,
    E1043,
    E1045,
    E1047,
    E1049,
    E1051,
    E1053,
    E1055,
    E1057,
    E1059,
    E1061,
    E1063,
    E1065,
    E1067,
    E1069,
    E1071,
    E1073,
    E1075,
    E1077,
    E1079,
    E1081,
    E1083,
    E1085,
    E1087,
    E1089,
    E1091,
    E1093,
    E1095,
    E1097,
    E1099,
    E1101,
    E1103,
    E1105,
    E1107,
    E1109,
    E1111,
    E1113,
    E1115,
    E1117,
    E1119,
    E1121,
  ]

@[irreducible] def assertsPart9 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1122 : F := publicValues[11] - publicValues[43]
  let E1123 : F := publicValues[14] * E1122
  let E1124 : F := publicValues[12] - publicValues[44]
  let E1125 : F := publicValues[14] * E1124
  let E1126 : F := publicValues[13] - publicValues[45]
  let E1127 : F := publicValues[14] * E1126
  let E1128 : F := publicValues[14] - publicValues[46]
  let E1129 : F := publicValues[14] * E1128
  let E1130 : F := publicValues[15] - publicValues[47]
  let E1131 : F := publicValues[14] * E1130
  let E1132 : F := publicValues[16] - publicValues[48]
  let E1133 : F := publicValues[14] * E1132
  let E1134 : F := publicValues[17] - publicValues[49]
  let E1135 : F := publicValues[14] * E1134
  let E1136 : F := publicValues[18] - publicValues[50]
  let E1137 : F := publicValues[14] * E1136
  let E1138 : F := publicValues[19] - publicValues[51]
  let E1139 : F := publicValues[14] * E1138
  let E1140 : F := publicValues[20] - publicValues[52]
  let E1141 : F := publicValues[14] * E1140
  let E1142 : F := publicValues[21] - publicValues[53]
  let E1143 : F := publicValues[14] * E1142
  let E1144 : F := publicValues[22] - publicValues[54]
  let E1145 : F := publicValues[14] * E1144
  let E1146 : F := publicValues[23] - publicValues[55]
  let E1147 : F := publicValues[14] * E1146
  let E1148 : F := publicValues[24] - publicValues[56]
  let E1149 : F := publicValues[14] * E1148
  let E1150 : F := publicValues[25] - publicValues[57]
  let E1151 : F := publicValues[14] * E1150
  let E1152 : F := publicValues[26] - publicValues[58]
  let E1153 : F := publicValues[14] * E1152
  let E1154 : F := publicValues[27] - publicValues[59]
  let E1155 : F := publicValues[14] * E1154
  let E1156 : F := publicValues[28] - publicValues[60]
  let E1157 : F := publicValues[14] * E1156
  let E1158 : F := publicValues[29] - publicValues[61]
  let E1159 : F := publicValues[14] * E1158
  let E1160 : F := publicValues[30] - publicValues[62]
  let E1161 : F := publicValues[14] * E1160
  let E1162 : F := publicValues[31] - publicValues[63]
  let E1163 : F := publicValues[14] * E1162
  let E1164 : F := publicValues[0] - publicValues[32]
  let E1165 : F := publicValues[15] * E1164
  let E1166 : F := publicValues[1] - publicValues[33]
  let E1167 : F := publicValues[15] * E1166
  let E1168 : F := publicValues[2] - publicValues[34]
  let E1169 : F := publicValues[15] * E1168
  let E1170 : F := publicValues[3] - publicValues[35]
  let E1171 : F := publicValues[15] * E1170
  let E1172 : F := publicValues[4] - publicValues[36]
  let E1173 : F := publicValues[15] * E1172
  let E1174 : F := publicValues[5] - publicValues[37]
  let E1175 : F := publicValues[15] * E1174
  let E1176 : F := publicValues[6] - publicValues[38]
  let E1177 : F := publicValues[15] * E1176
  let E1178 : F := publicValues[7] - publicValues[39]
  let E1179 : F := publicValues[15] * E1178
  let E1180 : F := publicValues[8] - publicValues[40]
  let E1181 : F := publicValues[15] * E1180
  let E1182 : F := publicValues[9] - publicValues[41]
  let E1183 : F := publicValues[15] * E1182
  let E1184 : F := publicValues[10] - publicValues[42]
  let E1185 : F := publicValues[15] * E1184
  let E1186 : F := publicValues[11] - publicValues[43]
  let E1187 : F := publicValues[15] * E1186
  let E1188 : F := publicValues[12] - publicValues[44]
  let E1189 : F := publicValues[15] * E1188
  let E1190 : F := publicValues[13] - publicValues[45]
  let E1191 : F := publicValues[15] * E1190
  let E1192 : F := publicValues[14] - publicValues[46]
  let E1193 : F := publicValues[15] * E1192
  let E1194 : F := publicValues[15] - publicValues[47]
  let E1195 : F := publicValues[15] * E1194
  let E1196 : F := publicValues[16] - publicValues[48]
  let E1197 : F := publicValues[15] * E1196
  let E1198 : F := publicValues[17] - publicValues[49]
  let E1199 : F := publicValues[15] * E1198
  let E1200 : F := publicValues[18] - publicValues[50]
  let E1201 : F := publicValues[15] * E1200
  let E1202 : F := publicValues[19] - publicValues[51]
  let E1203 : F := publicValues[15] * E1202
  let E1204 : F := publicValues[20] - publicValues[52]
  let E1205 : F := publicValues[15] * E1204
  let E1206 : F := publicValues[21] - publicValues[53]
  let E1207 : F := publicValues[15] * E1206
  let E1208 : F := publicValues[22] - publicValues[54]
  let E1209 : F := publicValues[15] * E1208
  let E1210 : F := publicValues[23] - publicValues[55]
  let E1211 : F := publicValues[15] * E1210
  let E1212 : F := publicValues[24] - publicValues[56]
  let E1213 : F := publicValues[15] * E1212
  let E1214 : F := publicValues[25] - publicValues[57]
  let E1215 : F := publicValues[15] * E1214
  let E1216 : F := publicValues[26] - publicValues[58]
  let E1217 : F := publicValues[15] * E1216
  let E1218 : F := publicValues[27] - publicValues[59]
  let E1219 : F := publicValues[15] * E1218
  let E1220 : F := publicValues[28] - publicValues[60]
  let E1221 : F := publicValues[15] * E1220
  let E1222 : F := publicValues[29] - publicValues[61]
  let E1223 : F := publicValues[15] * E1222
  let E1224 : F := publicValues[30] - publicValues[62]
  let E1225 : F := publicValues[15] * E1224
  let E1226 : F := publicValues[31] - publicValues[63]
  let E1227 : F := publicValues[15] * E1226
  let E1228 : F := publicValues[0] - publicValues[32]
  let E1229 : F := publicValues[16] * E1228
  let E1230 : F := publicValues[1] - publicValues[33]
  let E1231 : F := publicValues[16] * E1230
  let E1232 : F := publicValues[2] - publicValues[34]
  let E1233 : F := publicValues[16] * E1232
  let E1234 : F := publicValues[3] - publicValues[35]
  let E1235 : F := publicValues[16] * E1234
  let E1236 : F := publicValues[4] - publicValues[36]
  let E1237 : F := publicValues[16] * E1236
  let E1238 : F := publicValues[5] - publicValues[37]
  let E1239 : F := publicValues[16] * E1238
  let E1240 : F := publicValues[6] - publicValues[38]
  let E1241 : F := publicValues[16] * E1240
  let E1242 : F := publicValues[7] - publicValues[39]
  let E1243 : F := publicValues[16] * E1242
  let E1244 : F := publicValues[8] - publicValues[40]
  let E1245 : F := publicValues[16] * E1244
  let E1246 : F := publicValues[9] - publicValues[41]
  let E1247 : F := publicValues[16] * E1246
  let E1248 : F := publicValues[10] - publicValues[42]
  let E1249 : F := publicValues[16] * E1248
  [
    E1123,
    E1125,
    E1127,
    E1129,
    E1131,
    E1133,
    E1135,
    E1137,
    E1139,
    E1141,
    E1143,
    E1145,
    E1147,
    E1149,
    E1151,
    E1153,
    E1155,
    E1157,
    E1159,
    E1161,
    E1163,
    E1165,
    E1167,
    E1169,
    E1171,
    E1173,
    E1175,
    E1177,
    E1179,
    E1181,
    E1183,
    E1185,
    E1187,
    E1189,
    E1191,
    E1193,
    E1195,
    E1197,
    E1199,
    E1201,
    E1203,
    E1205,
    E1207,
    E1209,
    E1211,
    E1213,
    E1215,
    E1217,
    E1219,
    E1221,
    E1223,
    E1225,
    E1227,
    E1229,
    E1231,
    E1233,
    E1235,
    E1237,
    E1239,
    E1241,
    E1243,
    E1245,
    E1247,
    E1249,
  ]

@[irreducible] def assertsPart10 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1250 : F := publicValues[11] - publicValues[43]
  let E1251 : F := publicValues[16] * E1250
  let E1252 : F := publicValues[12] - publicValues[44]
  let E1253 : F := publicValues[16] * E1252
  let E1254 : F := publicValues[13] - publicValues[45]
  let E1255 : F := publicValues[16] * E1254
  let E1256 : F := publicValues[14] - publicValues[46]
  let E1257 : F := publicValues[16] * E1256
  let E1258 : F := publicValues[15] - publicValues[47]
  let E1259 : F := publicValues[16] * E1258
  let E1260 : F := publicValues[16] - publicValues[48]
  let E1261 : F := publicValues[16] * E1260
  let E1262 : F := publicValues[17] - publicValues[49]
  let E1263 : F := publicValues[16] * E1262
  let E1264 : F := publicValues[18] - publicValues[50]
  let E1265 : F := publicValues[16] * E1264
  let E1266 : F := publicValues[19] - publicValues[51]
  let E1267 : F := publicValues[16] * E1266
  let E1268 : F := publicValues[20] - publicValues[52]
  let E1269 : F := publicValues[16] * E1268
  let E1270 : F := publicValues[21] - publicValues[53]
  let E1271 : F := publicValues[16] * E1270
  let E1272 : F := publicValues[22] - publicValues[54]
  let E1273 : F := publicValues[16] * E1272
  let E1274 : F := publicValues[23] - publicValues[55]
  let E1275 : F := publicValues[16] * E1274
  let E1276 : F := publicValues[24] - publicValues[56]
  let E1277 : F := publicValues[16] * E1276
  let E1278 : F := publicValues[25] - publicValues[57]
  let E1279 : F := publicValues[16] * E1278
  let E1280 : F := publicValues[26] - publicValues[58]
  let E1281 : F := publicValues[16] * E1280
  let E1282 : F := publicValues[27] - publicValues[59]
  let E1283 : F := publicValues[16] * E1282
  let E1284 : F := publicValues[28] - publicValues[60]
  let E1285 : F := publicValues[16] * E1284
  let E1286 : F := publicValues[29] - publicValues[61]
  let E1287 : F := publicValues[16] * E1286
  let E1288 : F := publicValues[30] - publicValues[62]
  let E1289 : F := publicValues[16] * E1288
  let E1290 : F := publicValues[31] - publicValues[63]
  let E1291 : F := publicValues[16] * E1290
  let E1292 : F := publicValues[0] - publicValues[32]
  let E1293 : F := publicValues[17] * E1292
  let E1294 : F := publicValues[1] - publicValues[33]
  let E1295 : F := publicValues[17] * E1294
  let E1296 : F := publicValues[2] - publicValues[34]
  let E1297 : F := publicValues[17] * E1296
  let E1298 : F := publicValues[3] - publicValues[35]
  let E1299 : F := publicValues[17] * E1298
  let E1300 : F := publicValues[4] - publicValues[36]
  let E1301 : F := publicValues[17] * E1300
  let E1302 : F := publicValues[5] - publicValues[37]
  let E1303 : F := publicValues[17] * E1302
  let E1304 : F := publicValues[6] - publicValues[38]
  let E1305 : F := publicValues[17] * E1304
  let E1306 : F := publicValues[7] - publicValues[39]
  let E1307 : F := publicValues[17] * E1306
  let E1308 : F := publicValues[8] - publicValues[40]
  let E1309 : F := publicValues[17] * E1308
  let E1310 : F := publicValues[9] - publicValues[41]
  let E1311 : F := publicValues[17] * E1310
  let E1312 : F := publicValues[10] - publicValues[42]
  let E1313 : F := publicValues[17] * E1312
  let E1314 : F := publicValues[11] - publicValues[43]
  let E1315 : F := publicValues[17] * E1314
  let E1316 : F := publicValues[12] - publicValues[44]
  let E1317 : F := publicValues[17] * E1316
  let E1318 : F := publicValues[13] - publicValues[45]
  let E1319 : F := publicValues[17] * E1318
  let E1320 : F := publicValues[14] - publicValues[46]
  let E1321 : F := publicValues[17] * E1320
  let E1322 : F := publicValues[15] - publicValues[47]
  let E1323 : F := publicValues[17] * E1322
  let E1324 : F := publicValues[16] - publicValues[48]
  let E1325 : F := publicValues[17] * E1324
  let E1326 : F := publicValues[17] - publicValues[49]
  let E1327 : F := publicValues[17] * E1326
  let E1328 : F := publicValues[18] - publicValues[50]
  let E1329 : F := publicValues[17] * E1328
  let E1330 : F := publicValues[19] - publicValues[51]
  let E1331 : F := publicValues[17] * E1330
  let E1332 : F := publicValues[20] - publicValues[52]
  let E1333 : F := publicValues[17] * E1332
  let E1334 : F := publicValues[21] - publicValues[53]
  let E1335 : F := publicValues[17] * E1334
  let E1336 : F := publicValues[22] - publicValues[54]
  let E1337 : F := publicValues[17] * E1336
  let E1338 : F := publicValues[23] - publicValues[55]
  let E1339 : F := publicValues[17] * E1338
  let E1340 : F := publicValues[24] - publicValues[56]
  let E1341 : F := publicValues[17] * E1340
  let E1342 : F := publicValues[25] - publicValues[57]
  let E1343 : F := publicValues[17] * E1342
  let E1344 : F := publicValues[26] - publicValues[58]
  let E1345 : F := publicValues[17] * E1344
  let E1346 : F := publicValues[27] - publicValues[59]
  let E1347 : F := publicValues[17] * E1346
  let E1348 : F := publicValues[28] - publicValues[60]
  let E1349 : F := publicValues[17] * E1348
  let E1350 : F := publicValues[29] - publicValues[61]
  let E1351 : F := publicValues[17] * E1350
  let E1352 : F := publicValues[30] - publicValues[62]
  let E1353 : F := publicValues[17] * E1352
  let E1354 : F := publicValues[31] - publicValues[63]
  let E1355 : F := publicValues[17] * E1354
  let E1356 : F := publicValues[0] - publicValues[32]
  let E1357 : F := publicValues[18] * E1356
  let E1358 : F := publicValues[1] - publicValues[33]
  let E1359 : F := publicValues[18] * E1358
  let E1360 : F := publicValues[2] - publicValues[34]
  let E1361 : F := publicValues[18] * E1360
  let E1362 : F := publicValues[3] - publicValues[35]
  let E1363 : F := publicValues[18] * E1362
  let E1364 : F := publicValues[4] - publicValues[36]
  let E1365 : F := publicValues[18] * E1364
  let E1366 : F := publicValues[5] - publicValues[37]
  let E1367 : F := publicValues[18] * E1366
  let E1368 : F := publicValues[6] - publicValues[38]
  let E1369 : F := publicValues[18] * E1368
  let E1370 : F := publicValues[7] - publicValues[39]
  let E1371 : F := publicValues[18] * E1370
  let E1372 : F := publicValues[8] - publicValues[40]
  let E1373 : F := publicValues[18] * E1372
  let E1374 : F := publicValues[9] - publicValues[41]
  let E1375 : F := publicValues[18] * E1374
  let E1376 : F := publicValues[10] - publicValues[42]
  let E1377 : F := publicValues[18] * E1376
  [
    E1251,
    E1253,
    E1255,
    E1257,
    E1259,
    E1261,
    E1263,
    E1265,
    E1267,
    E1269,
    E1271,
    E1273,
    E1275,
    E1277,
    E1279,
    E1281,
    E1283,
    E1285,
    E1287,
    E1289,
    E1291,
    E1293,
    E1295,
    E1297,
    E1299,
    E1301,
    E1303,
    E1305,
    E1307,
    E1309,
    E1311,
    E1313,
    E1315,
    E1317,
    E1319,
    E1321,
    E1323,
    E1325,
    E1327,
    E1329,
    E1331,
    E1333,
    E1335,
    E1337,
    E1339,
    E1341,
    E1343,
    E1345,
    E1347,
    E1349,
    E1351,
    E1353,
    E1355,
    E1357,
    E1359,
    E1361,
    E1363,
    E1365,
    E1367,
    E1369,
    E1371,
    E1373,
    E1375,
    E1377,
  ]

@[irreducible] def assertsPart11 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1378 : F := publicValues[11] - publicValues[43]
  let E1379 : F := publicValues[18] * E1378
  let E1380 : F := publicValues[12] - publicValues[44]
  let E1381 : F := publicValues[18] * E1380
  let E1382 : F := publicValues[13] - publicValues[45]
  let E1383 : F := publicValues[18] * E1382
  let E1384 : F := publicValues[14] - publicValues[46]
  let E1385 : F := publicValues[18] * E1384
  let E1386 : F := publicValues[15] - publicValues[47]
  let E1387 : F := publicValues[18] * E1386
  let E1388 : F := publicValues[16] - publicValues[48]
  let E1389 : F := publicValues[18] * E1388
  let E1390 : F := publicValues[17] - publicValues[49]
  let E1391 : F := publicValues[18] * E1390
  let E1392 : F := publicValues[18] - publicValues[50]
  let E1393 : F := publicValues[18] * E1392
  let E1394 : F := publicValues[19] - publicValues[51]
  let E1395 : F := publicValues[18] * E1394
  let E1396 : F := publicValues[20] - publicValues[52]
  let E1397 : F := publicValues[18] * E1396
  let E1398 : F := publicValues[21] - publicValues[53]
  let E1399 : F := publicValues[18] * E1398
  let E1400 : F := publicValues[22] - publicValues[54]
  let E1401 : F := publicValues[18] * E1400
  let E1402 : F := publicValues[23] - publicValues[55]
  let E1403 : F := publicValues[18] * E1402
  let E1404 : F := publicValues[24] - publicValues[56]
  let E1405 : F := publicValues[18] * E1404
  let E1406 : F := publicValues[25] - publicValues[57]
  let E1407 : F := publicValues[18] * E1406
  let E1408 : F := publicValues[26] - publicValues[58]
  let E1409 : F := publicValues[18] * E1408
  let E1410 : F := publicValues[27] - publicValues[59]
  let E1411 : F := publicValues[18] * E1410
  let E1412 : F := publicValues[28] - publicValues[60]
  let E1413 : F := publicValues[18] * E1412
  let E1414 : F := publicValues[29] - publicValues[61]
  let E1415 : F := publicValues[18] * E1414
  let E1416 : F := publicValues[30] - publicValues[62]
  let E1417 : F := publicValues[18] * E1416
  let E1418 : F := publicValues[31] - publicValues[63]
  let E1419 : F := publicValues[18] * E1418
  let E1420 : F := publicValues[0] - publicValues[32]
  let E1421 : F := publicValues[19] * E1420
  let E1422 : F := publicValues[1] - publicValues[33]
  let E1423 : F := publicValues[19] * E1422
  let E1424 : F := publicValues[2] - publicValues[34]
  let E1425 : F := publicValues[19] * E1424
  let E1426 : F := publicValues[3] - publicValues[35]
  let E1427 : F := publicValues[19] * E1426
  let E1428 : F := publicValues[4] - publicValues[36]
  let E1429 : F := publicValues[19] * E1428
  let E1430 : F := publicValues[5] - publicValues[37]
  let E1431 : F := publicValues[19] * E1430
  let E1432 : F := publicValues[6] - publicValues[38]
  let E1433 : F := publicValues[19] * E1432
  let E1434 : F := publicValues[7] - publicValues[39]
  let E1435 : F := publicValues[19] * E1434
  let E1436 : F := publicValues[8] - publicValues[40]
  let E1437 : F := publicValues[19] * E1436
  let E1438 : F := publicValues[9] - publicValues[41]
  let E1439 : F := publicValues[19] * E1438
  let E1440 : F := publicValues[10] - publicValues[42]
  let E1441 : F := publicValues[19] * E1440
  let E1442 : F := publicValues[11] - publicValues[43]
  let E1443 : F := publicValues[19] * E1442
  let E1444 : F := publicValues[12] - publicValues[44]
  let E1445 : F := publicValues[19] * E1444
  let E1446 : F := publicValues[13] - publicValues[45]
  let E1447 : F := publicValues[19] * E1446
  let E1448 : F := publicValues[14] - publicValues[46]
  let E1449 : F := publicValues[19] * E1448
  let E1450 : F := publicValues[15] - publicValues[47]
  let E1451 : F := publicValues[19] * E1450
  let E1452 : F := publicValues[16] - publicValues[48]
  let E1453 : F := publicValues[19] * E1452
  let E1454 : F := publicValues[17] - publicValues[49]
  let E1455 : F := publicValues[19] * E1454
  let E1456 : F := publicValues[18] - publicValues[50]
  let E1457 : F := publicValues[19] * E1456
  let E1458 : F := publicValues[19] - publicValues[51]
  let E1459 : F := publicValues[19] * E1458
  let E1460 : F := publicValues[20] - publicValues[52]
  let E1461 : F := publicValues[19] * E1460
  let E1462 : F := publicValues[21] - publicValues[53]
  let E1463 : F := publicValues[19] * E1462
  let E1464 : F := publicValues[22] - publicValues[54]
  let E1465 : F := publicValues[19] * E1464
  let E1466 : F := publicValues[23] - publicValues[55]
  let E1467 : F := publicValues[19] * E1466
  let E1468 : F := publicValues[24] - publicValues[56]
  let E1469 : F := publicValues[19] * E1468
  let E1470 : F := publicValues[25] - publicValues[57]
  let E1471 : F := publicValues[19] * E1470
  let E1472 : F := publicValues[26] - publicValues[58]
  let E1473 : F := publicValues[19] * E1472
  let E1474 : F := publicValues[27] - publicValues[59]
  let E1475 : F := publicValues[19] * E1474
  let E1476 : F := publicValues[28] - publicValues[60]
  let E1477 : F := publicValues[19] * E1476
  let E1478 : F := publicValues[29] - publicValues[61]
  let E1479 : F := publicValues[19] * E1478
  let E1480 : F := publicValues[30] - publicValues[62]
  let E1481 : F := publicValues[19] * E1480
  let E1482 : F := publicValues[31] - publicValues[63]
  let E1483 : F := publicValues[19] * E1482
  let E1484 : F := publicValues[0] - publicValues[32]
  let E1485 : F := publicValues[20] * E1484
  let E1486 : F := publicValues[1] - publicValues[33]
  let E1487 : F := publicValues[20] * E1486
  let E1488 : F := publicValues[2] - publicValues[34]
  let E1489 : F := publicValues[20] * E1488
  let E1490 : F := publicValues[3] - publicValues[35]
  let E1491 : F := publicValues[20] * E1490
  let E1492 : F := publicValues[4] - publicValues[36]
  let E1493 : F := publicValues[20] * E1492
  let E1494 : F := publicValues[5] - publicValues[37]
  let E1495 : F := publicValues[20] * E1494
  let E1496 : F := publicValues[6] - publicValues[38]
  let E1497 : F := publicValues[20] * E1496
  let E1498 : F := publicValues[7] - publicValues[39]
  let E1499 : F := publicValues[20] * E1498
  let E1500 : F := publicValues[8] - publicValues[40]
  let E1501 : F := publicValues[20] * E1500
  let E1502 : F := publicValues[9] - publicValues[41]
  let E1503 : F := publicValues[20] * E1502
  let E1504 : F := publicValues[10] - publicValues[42]
  let E1505 : F := publicValues[20] * E1504
  [
    E1379,
    E1381,
    E1383,
    E1385,
    E1387,
    E1389,
    E1391,
    E1393,
    E1395,
    E1397,
    E1399,
    E1401,
    E1403,
    E1405,
    E1407,
    E1409,
    E1411,
    E1413,
    E1415,
    E1417,
    E1419,
    E1421,
    E1423,
    E1425,
    E1427,
    E1429,
    E1431,
    E1433,
    E1435,
    E1437,
    E1439,
    E1441,
    E1443,
    E1445,
    E1447,
    E1449,
    E1451,
    E1453,
    E1455,
    E1457,
    E1459,
    E1461,
    E1463,
    E1465,
    E1467,
    E1469,
    E1471,
    E1473,
    E1475,
    E1477,
    E1479,
    E1481,
    E1483,
    E1485,
    E1487,
    E1489,
    E1491,
    E1493,
    E1495,
    E1497,
    E1499,
    E1501,
    E1503,
    E1505,
  ]

@[irreducible] def assertsPart12 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1506 : F := publicValues[11] - publicValues[43]
  let E1507 : F := publicValues[20] * E1506
  let E1508 : F := publicValues[12] - publicValues[44]
  let E1509 : F := publicValues[20] * E1508
  let E1510 : F := publicValues[13] - publicValues[45]
  let E1511 : F := publicValues[20] * E1510
  let E1512 : F := publicValues[14] - publicValues[46]
  let E1513 : F := publicValues[20] * E1512
  let E1514 : F := publicValues[15] - publicValues[47]
  let E1515 : F := publicValues[20] * E1514
  let E1516 : F := publicValues[16] - publicValues[48]
  let E1517 : F := publicValues[20] * E1516
  let E1518 : F := publicValues[17] - publicValues[49]
  let E1519 : F := publicValues[20] * E1518
  let E1520 : F := publicValues[18] - publicValues[50]
  let E1521 : F := publicValues[20] * E1520
  let E1522 : F := publicValues[19] - publicValues[51]
  let E1523 : F := publicValues[20] * E1522
  let E1524 : F := publicValues[20] - publicValues[52]
  let E1525 : F := publicValues[20] * E1524
  let E1526 : F := publicValues[21] - publicValues[53]
  let E1527 : F := publicValues[20] * E1526
  let E1528 : F := publicValues[22] - publicValues[54]
  let E1529 : F := publicValues[20] * E1528
  let E1530 : F := publicValues[23] - publicValues[55]
  let E1531 : F := publicValues[20] * E1530
  let E1532 : F := publicValues[24] - publicValues[56]
  let E1533 : F := publicValues[20] * E1532
  let E1534 : F := publicValues[25] - publicValues[57]
  let E1535 : F := publicValues[20] * E1534
  let E1536 : F := publicValues[26] - publicValues[58]
  let E1537 : F := publicValues[20] * E1536
  let E1538 : F := publicValues[27] - publicValues[59]
  let E1539 : F := publicValues[20] * E1538
  let E1540 : F := publicValues[28] - publicValues[60]
  let E1541 : F := publicValues[20] * E1540
  let E1542 : F := publicValues[29] - publicValues[61]
  let E1543 : F := publicValues[20] * E1542
  let E1544 : F := publicValues[30] - publicValues[62]
  let E1545 : F := publicValues[20] * E1544
  let E1546 : F := publicValues[31] - publicValues[63]
  let E1547 : F := publicValues[20] * E1546
  let E1548 : F := publicValues[0] - publicValues[32]
  let E1549 : F := publicValues[21] * E1548
  let E1550 : F := publicValues[1] - publicValues[33]
  let E1551 : F := publicValues[21] * E1550
  let E1552 : F := publicValues[2] - publicValues[34]
  let E1553 : F := publicValues[21] * E1552
  let E1554 : F := publicValues[3] - publicValues[35]
  let E1555 : F := publicValues[21] * E1554
  let E1556 : F := publicValues[4] - publicValues[36]
  let E1557 : F := publicValues[21] * E1556
  let E1558 : F := publicValues[5] - publicValues[37]
  let E1559 : F := publicValues[21] * E1558
  let E1560 : F := publicValues[6] - publicValues[38]
  let E1561 : F := publicValues[21] * E1560
  let E1562 : F := publicValues[7] - publicValues[39]
  let E1563 : F := publicValues[21] * E1562
  let E1564 : F := publicValues[8] - publicValues[40]
  let E1565 : F := publicValues[21] * E1564
  let E1566 : F := publicValues[9] - publicValues[41]
  let E1567 : F := publicValues[21] * E1566
  let E1568 : F := publicValues[10] - publicValues[42]
  let E1569 : F := publicValues[21] * E1568
  let E1570 : F := publicValues[11] - publicValues[43]
  let E1571 : F := publicValues[21] * E1570
  let E1572 : F := publicValues[12] - publicValues[44]
  let E1573 : F := publicValues[21] * E1572
  let E1574 : F := publicValues[13] - publicValues[45]
  let E1575 : F := publicValues[21] * E1574
  let E1576 : F := publicValues[14] - publicValues[46]
  let E1577 : F := publicValues[21] * E1576
  let E1578 : F := publicValues[15] - publicValues[47]
  let E1579 : F := publicValues[21] * E1578
  let E1580 : F := publicValues[16] - publicValues[48]
  let E1581 : F := publicValues[21] * E1580
  let E1582 : F := publicValues[17] - publicValues[49]
  let E1583 : F := publicValues[21] * E1582
  let E1584 : F := publicValues[18] - publicValues[50]
  let E1585 : F := publicValues[21] * E1584
  let E1586 : F := publicValues[19] - publicValues[51]
  let E1587 : F := publicValues[21] * E1586
  let E1588 : F := publicValues[20] - publicValues[52]
  let E1589 : F := publicValues[21] * E1588
  let E1590 : F := publicValues[21] - publicValues[53]
  let E1591 : F := publicValues[21] * E1590
  let E1592 : F := publicValues[22] - publicValues[54]
  let E1593 : F := publicValues[21] * E1592
  let E1594 : F := publicValues[23] - publicValues[55]
  let E1595 : F := publicValues[21] * E1594
  let E1596 : F := publicValues[24] - publicValues[56]
  let E1597 : F := publicValues[21] * E1596
  let E1598 : F := publicValues[25] - publicValues[57]
  let E1599 : F := publicValues[21] * E1598
  let E1600 : F := publicValues[26] - publicValues[58]
  let E1601 : F := publicValues[21] * E1600
  let E1602 : F := publicValues[27] - publicValues[59]
  let E1603 : F := publicValues[21] * E1602
  let E1604 : F := publicValues[28] - publicValues[60]
  let E1605 : F := publicValues[21] * E1604
  let E1606 : F := publicValues[29] - publicValues[61]
  let E1607 : F := publicValues[21] * E1606
  let E1608 : F := publicValues[30] - publicValues[62]
  let E1609 : F := publicValues[21] * E1608
  let E1610 : F := publicValues[31] - publicValues[63]
  let E1611 : F := publicValues[21] * E1610
  let E1612 : F := publicValues[0] - publicValues[32]
  let E1613 : F := publicValues[22] * E1612
  let E1614 : F := publicValues[1] - publicValues[33]
  let E1615 : F := publicValues[22] * E1614
  let E1616 : F := publicValues[2] - publicValues[34]
  let E1617 : F := publicValues[22] * E1616
  let E1618 : F := publicValues[3] - publicValues[35]
  let E1619 : F := publicValues[22] * E1618
  let E1620 : F := publicValues[4] - publicValues[36]
  let E1621 : F := publicValues[22] * E1620
  let E1622 : F := publicValues[5] - publicValues[37]
  let E1623 : F := publicValues[22] * E1622
  let E1624 : F := publicValues[6] - publicValues[38]
  let E1625 : F := publicValues[22] * E1624
  let E1626 : F := publicValues[7] - publicValues[39]
  let E1627 : F := publicValues[22] * E1626
  let E1628 : F := publicValues[8] - publicValues[40]
  let E1629 : F := publicValues[22] * E1628
  let E1630 : F := publicValues[9] - publicValues[41]
  let E1631 : F := publicValues[22] * E1630
  let E1632 : F := publicValues[10] - publicValues[42]
  let E1633 : F := publicValues[22] * E1632
  [
    E1507,
    E1509,
    E1511,
    E1513,
    E1515,
    E1517,
    E1519,
    E1521,
    E1523,
    E1525,
    E1527,
    E1529,
    E1531,
    E1533,
    E1535,
    E1537,
    E1539,
    E1541,
    E1543,
    E1545,
    E1547,
    E1549,
    E1551,
    E1553,
    E1555,
    E1557,
    E1559,
    E1561,
    E1563,
    E1565,
    E1567,
    E1569,
    E1571,
    E1573,
    E1575,
    E1577,
    E1579,
    E1581,
    E1583,
    E1585,
    E1587,
    E1589,
    E1591,
    E1593,
    E1595,
    E1597,
    E1599,
    E1601,
    E1603,
    E1605,
    E1607,
    E1609,
    E1611,
    E1613,
    E1615,
    E1617,
    E1619,
    E1621,
    E1623,
    E1625,
    E1627,
    E1629,
    E1631,
    E1633,
  ]

@[irreducible] def assertsPart13 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1634 : F := publicValues[11] - publicValues[43]
  let E1635 : F := publicValues[22] * E1634
  let E1636 : F := publicValues[12] - publicValues[44]
  let E1637 : F := publicValues[22] * E1636
  let E1638 : F := publicValues[13] - publicValues[45]
  let E1639 : F := publicValues[22] * E1638
  let E1640 : F := publicValues[14] - publicValues[46]
  let E1641 : F := publicValues[22] * E1640
  let E1642 : F := publicValues[15] - publicValues[47]
  let E1643 : F := publicValues[22] * E1642
  let E1644 : F := publicValues[16] - publicValues[48]
  let E1645 : F := publicValues[22] * E1644
  let E1646 : F := publicValues[17] - publicValues[49]
  let E1647 : F := publicValues[22] * E1646
  let E1648 : F := publicValues[18] - publicValues[50]
  let E1649 : F := publicValues[22] * E1648
  let E1650 : F := publicValues[19] - publicValues[51]
  let E1651 : F := publicValues[22] * E1650
  let E1652 : F := publicValues[20] - publicValues[52]
  let E1653 : F := publicValues[22] * E1652
  let E1654 : F := publicValues[21] - publicValues[53]
  let E1655 : F := publicValues[22] * E1654
  let E1656 : F := publicValues[22] - publicValues[54]
  let E1657 : F := publicValues[22] * E1656
  let E1658 : F := publicValues[23] - publicValues[55]
  let E1659 : F := publicValues[22] * E1658
  let E1660 : F := publicValues[24] - publicValues[56]
  let E1661 : F := publicValues[22] * E1660
  let E1662 : F := publicValues[25] - publicValues[57]
  let E1663 : F := publicValues[22] * E1662
  let E1664 : F := publicValues[26] - publicValues[58]
  let E1665 : F := publicValues[22] * E1664
  let E1666 : F := publicValues[27] - publicValues[59]
  let E1667 : F := publicValues[22] * E1666
  let E1668 : F := publicValues[28] - publicValues[60]
  let E1669 : F := publicValues[22] * E1668
  let E1670 : F := publicValues[29] - publicValues[61]
  let E1671 : F := publicValues[22] * E1670
  let E1672 : F := publicValues[30] - publicValues[62]
  let E1673 : F := publicValues[22] * E1672
  let E1674 : F := publicValues[31] - publicValues[63]
  let E1675 : F := publicValues[22] * E1674
  let E1676 : F := publicValues[0] - publicValues[32]
  let E1677 : F := publicValues[23] * E1676
  let E1678 : F := publicValues[1] - publicValues[33]
  let E1679 : F := publicValues[23] * E1678
  let E1680 : F := publicValues[2] - publicValues[34]
  let E1681 : F := publicValues[23] * E1680
  let E1682 : F := publicValues[3] - publicValues[35]
  let E1683 : F := publicValues[23] * E1682
  let E1684 : F := publicValues[4] - publicValues[36]
  let E1685 : F := publicValues[23] * E1684
  let E1686 : F := publicValues[5] - publicValues[37]
  let E1687 : F := publicValues[23] * E1686
  let E1688 : F := publicValues[6] - publicValues[38]
  let E1689 : F := publicValues[23] * E1688
  let E1690 : F := publicValues[7] - publicValues[39]
  let E1691 : F := publicValues[23] * E1690
  let E1692 : F := publicValues[8] - publicValues[40]
  let E1693 : F := publicValues[23] * E1692
  let E1694 : F := publicValues[9] - publicValues[41]
  let E1695 : F := publicValues[23] * E1694
  let E1696 : F := publicValues[10] - publicValues[42]
  let E1697 : F := publicValues[23] * E1696
  let E1698 : F := publicValues[11] - publicValues[43]
  let E1699 : F := publicValues[23] * E1698
  let E1700 : F := publicValues[12] - publicValues[44]
  let E1701 : F := publicValues[23] * E1700
  let E1702 : F := publicValues[13] - publicValues[45]
  let E1703 : F := publicValues[23] * E1702
  let E1704 : F := publicValues[14] - publicValues[46]
  let E1705 : F := publicValues[23] * E1704
  let E1706 : F := publicValues[15] - publicValues[47]
  let E1707 : F := publicValues[23] * E1706
  let E1708 : F := publicValues[16] - publicValues[48]
  let E1709 : F := publicValues[23] * E1708
  let E1710 : F := publicValues[17] - publicValues[49]
  let E1711 : F := publicValues[23] * E1710
  let E1712 : F := publicValues[18] - publicValues[50]
  let E1713 : F := publicValues[23] * E1712
  let E1714 : F := publicValues[19] - publicValues[51]
  let E1715 : F := publicValues[23] * E1714
  let E1716 : F := publicValues[20] - publicValues[52]
  let E1717 : F := publicValues[23] * E1716
  let E1718 : F := publicValues[21] - publicValues[53]
  let E1719 : F := publicValues[23] * E1718
  let E1720 : F := publicValues[22] - publicValues[54]
  let E1721 : F := publicValues[23] * E1720
  let E1722 : F := publicValues[23] - publicValues[55]
  let E1723 : F := publicValues[23] * E1722
  let E1724 : F := publicValues[24] - publicValues[56]
  let E1725 : F := publicValues[23] * E1724
  let E1726 : F := publicValues[25] - publicValues[57]
  let E1727 : F := publicValues[23] * E1726
  let E1728 : F := publicValues[26] - publicValues[58]
  let E1729 : F := publicValues[23] * E1728
  let E1730 : F := publicValues[27] - publicValues[59]
  let E1731 : F := publicValues[23] * E1730
  let E1732 : F := publicValues[28] - publicValues[60]
  let E1733 : F := publicValues[23] * E1732
  let E1734 : F := publicValues[29] - publicValues[61]
  let E1735 : F := publicValues[23] * E1734
  let E1736 : F := publicValues[30] - publicValues[62]
  let E1737 : F := publicValues[23] * E1736
  let E1738 : F := publicValues[31] - publicValues[63]
  let E1739 : F := publicValues[23] * E1738
  let E1740 : F := publicValues[0] - publicValues[32]
  let E1741 : F := publicValues[24] * E1740
  let E1742 : F := publicValues[1] - publicValues[33]
  let E1743 : F := publicValues[24] * E1742
  let E1744 : F := publicValues[2] - publicValues[34]
  let E1745 : F := publicValues[24] * E1744
  let E1746 : F := publicValues[3] - publicValues[35]
  let E1747 : F := publicValues[24] * E1746
  let E1748 : F := publicValues[4] - publicValues[36]
  let E1749 : F := publicValues[24] * E1748
  let E1750 : F := publicValues[5] - publicValues[37]
  let E1751 : F := publicValues[24] * E1750
  let E1752 : F := publicValues[6] - publicValues[38]
  let E1753 : F := publicValues[24] * E1752
  let E1754 : F := publicValues[7] - publicValues[39]
  let E1755 : F := publicValues[24] * E1754
  let E1756 : F := publicValues[8] - publicValues[40]
  let E1757 : F := publicValues[24] * E1756
  let E1758 : F := publicValues[9] - publicValues[41]
  let E1759 : F := publicValues[24] * E1758
  let E1760 : F := publicValues[10] - publicValues[42]
  let E1761 : F := publicValues[24] * E1760
  [
    E1635,
    E1637,
    E1639,
    E1641,
    E1643,
    E1645,
    E1647,
    E1649,
    E1651,
    E1653,
    E1655,
    E1657,
    E1659,
    E1661,
    E1663,
    E1665,
    E1667,
    E1669,
    E1671,
    E1673,
    E1675,
    E1677,
    E1679,
    E1681,
    E1683,
    E1685,
    E1687,
    E1689,
    E1691,
    E1693,
    E1695,
    E1697,
    E1699,
    E1701,
    E1703,
    E1705,
    E1707,
    E1709,
    E1711,
    E1713,
    E1715,
    E1717,
    E1719,
    E1721,
    E1723,
    E1725,
    E1727,
    E1729,
    E1731,
    E1733,
    E1735,
    E1737,
    E1739,
    E1741,
    E1743,
    E1745,
    E1747,
    E1749,
    E1751,
    E1753,
    E1755,
    E1757,
    E1759,
    E1761,
  ]

@[irreducible] def assertsPart14 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1762 : F := publicValues[11] - publicValues[43]
  let E1763 : F := publicValues[24] * E1762
  let E1764 : F := publicValues[12] - publicValues[44]
  let E1765 : F := publicValues[24] * E1764
  let E1766 : F := publicValues[13] - publicValues[45]
  let E1767 : F := publicValues[24] * E1766
  let E1768 : F := publicValues[14] - publicValues[46]
  let E1769 : F := publicValues[24] * E1768
  let E1770 : F := publicValues[15] - publicValues[47]
  let E1771 : F := publicValues[24] * E1770
  let E1772 : F := publicValues[16] - publicValues[48]
  let E1773 : F := publicValues[24] * E1772
  let E1774 : F := publicValues[17] - publicValues[49]
  let E1775 : F := publicValues[24] * E1774
  let E1776 : F := publicValues[18] - publicValues[50]
  let E1777 : F := publicValues[24] * E1776
  let E1778 : F := publicValues[19] - publicValues[51]
  let E1779 : F := publicValues[24] * E1778
  let E1780 : F := publicValues[20] - publicValues[52]
  let E1781 : F := publicValues[24] * E1780
  let E1782 : F := publicValues[21] - publicValues[53]
  let E1783 : F := publicValues[24] * E1782
  let E1784 : F := publicValues[22] - publicValues[54]
  let E1785 : F := publicValues[24] * E1784
  let E1786 : F := publicValues[23] - publicValues[55]
  let E1787 : F := publicValues[24] * E1786
  let E1788 : F := publicValues[24] - publicValues[56]
  let E1789 : F := publicValues[24] * E1788
  let E1790 : F := publicValues[25] - publicValues[57]
  let E1791 : F := publicValues[24] * E1790
  let E1792 : F := publicValues[26] - publicValues[58]
  let E1793 : F := publicValues[24] * E1792
  let E1794 : F := publicValues[27] - publicValues[59]
  let E1795 : F := publicValues[24] * E1794
  let E1796 : F := publicValues[28] - publicValues[60]
  let E1797 : F := publicValues[24] * E1796
  let E1798 : F := publicValues[29] - publicValues[61]
  let E1799 : F := publicValues[24] * E1798
  let E1800 : F := publicValues[30] - publicValues[62]
  let E1801 : F := publicValues[24] * E1800
  let E1802 : F := publicValues[31] - publicValues[63]
  let E1803 : F := publicValues[24] * E1802
  let E1804 : F := publicValues[0] - publicValues[32]
  let E1805 : F := publicValues[25] * E1804
  let E1806 : F := publicValues[1] - publicValues[33]
  let E1807 : F := publicValues[25] * E1806
  let E1808 : F := publicValues[2] - publicValues[34]
  let E1809 : F := publicValues[25] * E1808
  let E1810 : F := publicValues[3] - publicValues[35]
  let E1811 : F := publicValues[25] * E1810
  let E1812 : F := publicValues[4] - publicValues[36]
  let E1813 : F := publicValues[25] * E1812
  let E1814 : F := publicValues[5] - publicValues[37]
  let E1815 : F := publicValues[25] * E1814
  let E1816 : F := publicValues[6] - publicValues[38]
  let E1817 : F := publicValues[25] * E1816
  let E1818 : F := publicValues[7] - publicValues[39]
  let E1819 : F := publicValues[25] * E1818
  let E1820 : F := publicValues[8] - publicValues[40]
  let E1821 : F := publicValues[25] * E1820
  let E1822 : F := publicValues[9] - publicValues[41]
  let E1823 : F := publicValues[25] * E1822
  let E1824 : F := publicValues[10] - publicValues[42]
  let E1825 : F := publicValues[25] * E1824
  let E1826 : F := publicValues[11] - publicValues[43]
  let E1827 : F := publicValues[25] * E1826
  let E1828 : F := publicValues[12] - publicValues[44]
  let E1829 : F := publicValues[25] * E1828
  let E1830 : F := publicValues[13] - publicValues[45]
  let E1831 : F := publicValues[25] * E1830
  let E1832 : F := publicValues[14] - publicValues[46]
  let E1833 : F := publicValues[25] * E1832
  let E1834 : F := publicValues[15] - publicValues[47]
  let E1835 : F := publicValues[25] * E1834
  let E1836 : F := publicValues[16] - publicValues[48]
  let E1837 : F := publicValues[25] * E1836
  let E1838 : F := publicValues[17] - publicValues[49]
  let E1839 : F := publicValues[25] * E1838
  let E1840 : F := publicValues[18] - publicValues[50]
  let E1841 : F := publicValues[25] * E1840
  let E1842 : F := publicValues[19] - publicValues[51]
  let E1843 : F := publicValues[25] * E1842
  let E1844 : F := publicValues[20] - publicValues[52]
  let E1845 : F := publicValues[25] * E1844
  let E1846 : F := publicValues[21] - publicValues[53]
  let E1847 : F := publicValues[25] * E1846
  let E1848 : F := publicValues[22] - publicValues[54]
  let E1849 : F := publicValues[25] * E1848
  let E1850 : F := publicValues[23] - publicValues[55]
  let E1851 : F := publicValues[25] * E1850
  let E1852 : F := publicValues[24] - publicValues[56]
  let E1853 : F := publicValues[25] * E1852
  let E1854 : F := publicValues[25] - publicValues[57]
  let E1855 : F := publicValues[25] * E1854
  let E1856 : F := publicValues[26] - publicValues[58]
  let E1857 : F := publicValues[25] * E1856
  let E1858 : F := publicValues[27] - publicValues[59]
  let E1859 : F := publicValues[25] * E1858
  let E1860 : F := publicValues[28] - publicValues[60]
  let E1861 : F := publicValues[25] * E1860
  let E1862 : F := publicValues[29] - publicValues[61]
  let E1863 : F := publicValues[25] * E1862
  let E1864 : F := publicValues[30] - publicValues[62]
  let E1865 : F := publicValues[25] * E1864
  let E1866 : F := publicValues[31] - publicValues[63]
  let E1867 : F := publicValues[25] * E1866
  let E1868 : F := publicValues[0] - publicValues[32]
  let E1869 : F := publicValues[26] * E1868
  let E1870 : F := publicValues[1] - publicValues[33]
  let E1871 : F := publicValues[26] * E1870
  let E1872 : F := publicValues[2] - publicValues[34]
  let E1873 : F := publicValues[26] * E1872
  let E1874 : F := publicValues[3] - publicValues[35]
  let E1875 : F := publicValues[26] * E1874
  let E1876 : F := publicValues[4] - publicValues[36]
  let E1877 : F := publicValues[26] * E1876
  let E1878 : F := publicValues[5] - publicValues[37]
  let E1879 : F := publicValues[26] * E1878
  let E1880 : F := publicValues[6] - publicValues[38]
  let E1881 : F := publicValues[26] * E1880
  let E1882 : F := publicValues[7] - publicValues[39]
  let E1883 : F := publicValues[26] * E1882
  let E1884 : F := publicValues[8] - publicValues[40]
  let E1885 : F := publicValues[26] * E1884
  let E1886 : F := publicValues[9] - publicValues[41]
  let E1887 : F := publicValues[26] * E1886
  let E1888 : F := publicValues[10] - publicValues[42]
  let E1889 : F := publicValues[26] * E1888
  [
    E1763,
    E1765,
    E1767,
    E1769,
    E1771,
    E1773,
    E1775,
    E1777,
    E1779,
    E1781,
    E1783,
    E1785,
    E1787,
    E1789,
    E1791,
    E1793,
    E1795,
    E1797,
    E1799,
    E1801,
    E1803,
    E1805,
    E1807,
    E1809,
    E1811,
    E1813,
    E1815,
    E1817,
    E1819,
    E1821,
    E1823,
    E1825,
    E1827,
    E1829,
    E1831,
    E1833,
    E1835,
    E1837,
    E1839,
    E1841,
    E1843,
    E1845,
    E1847,
    E1849,
    E1851,
    E1853,
    E1855,
    E1857,
    E1859,
    E1861,
    E1863,
    E1865,
    E1867,
    E1869,
    E1871,
    E1873,
    E1875,
    E1877,
    E1879,
    E1881,
    E1883,
    E1885,
    E1887,
    E1889,
  ]

@[irreducible] def assertsPart15 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E1890 : F := publicValues[11] - publicValues[43]
  let E1891 : F := publicValues[26] * E1890
  let E1892 : F := publicValues[12] - publicValues[44]
  let E1893 : F := publicValues[26] * E1892
  let E1894 : F := publicValues[13] - publicValues[45]
  let E1895 : F := publicValues[26] * E1894
  let E1896 : F := publicValues[14] - publicValues[46]
  let E1897 : F := publicValues[26] * E1896
  let E1898 : F := publicValues[15] - publicValues[47]
  let E1899 : F := publicValues[26] * E1898
  let E1900 : F := publicValues[16] - publicValues[48]
  let E1901 : F := publicValues[26] * E1900
  let E1902 : F := publicValues[17] - publicValues[49]
  let E1903 : F := publicValues[26] * E1902
  let E1904 : F := publicValues[18] - publicValues[50]
  let E1905 : F := publicValues[26] * E1904
  let E1906 : F := publicValues[19] - publicValues[51]
  let E1907 : F := publicValues[26] * E1906
  let E1908 : F := publicValues[20] - publicValues[52]
  let E1909 : F := publicValues[26] * E1908
  let E1910 : F := publicValues[21] - publicValues[53]
  let E1911 : F := publicValues[26] * E1910
  let E1912 : F := publicValues[22] - publicValues[54]
  let E1913 : F := publicValues[26] * E1912
  let E1914 : F := publicValues[23] - publicValues[55]
  let E1915 : F := publicValues[26] * E1914
  let E1916 : F := publicValues[24] - publicValues[56]
  let E1917 : F := publicValues[26] * E1916
  let E1918 : F := publicValues[25] - publicValues[57]
  let E1919 : F := publicValues[26] * E1918
  let E1920 : F := publicValues[26] - publicValues[58]
  let E1921 : F := publicValues[26] * E1920
  let E1922 : F := publicValues[27] - publicValues[59]
  let E1923 : F := publicValues[26] * E1922
  let E1924 : F := publicValues[28] - publicValues[60]
  let E1925 : F := publicValues[26] * E1924
  let E1926 : F := publicValues[29] - publicValues[61]
  let E1927 : F := publicValues[26] * E1926
  let E1928 : F := publicValues[30] - publicValues[62]
  let E1929 : F := publicValues[26] * E1928
  let E1930 : F := publicValues[31] - publicValues[63]
  let E1931 : F := publicValues[26] * E1930
  let E1932 : F := publicValues[0] - publicValues[32]
  let E1933 : F := publicValues[27] * E1932
  let E1934 : F := publicValues[1] - publicValues[33]
  let E1935 : F := publicValues[27] * E1934
  let E1936 : F := publicValues[2] - publicValues[34]
  let E1937 : F := publicValues[27] * E1936
  let E1938 : F := publicValues[3] - publicValues[35]
  let E1939 : F := publicValues[27] * E1938
  let E1940 : F := publicValues[4] - publicValues[36]
  let E1941 : F := publicValues[27] * E1940
  let E1942 : F := publicValues[5] - publicValues[37]
  let E1943 : F := publicValues[27] * E1942
  let E1944 : F := publicValues[6] - publicValues[38]
  let E1945 : F := publicValues[27] * E1944
  let E1946 : F := publicValues[7] - publicValues[39]
  let E1947 : F := publicValues[27] * E1946
  let E1948 : F := publicValues[8] - publicValues[40]
  let E1949 : F := publicValues[27] * E1948
  let E1950 : F := publicValues[9] - publicValues[41]
  let E1951 : F := publicValues[27] * E1950
  let E1952 : F := publicValues[10] - publicValues[42]
  let E1953 : F := publicValues[27] * E1952
  let E1954 : F := publicValues[11] - publicValues[43]
  let E1955 : F := publicValues[27] * E1954
  let E1956 : F := publicValues[12] - publicValues[44]
  let E1957 : F := publicValues[27] * E1956
  let E1958 : F := publicValues[13] - publicValues[45]
  let E1959 : F := publicValues[27] * E1958
  let E1960 : F := publicValues[14] - publicValues[46]
  let E1961 : F := publicValues[27] * E1960
  let E1962 : F := publicValues[15] - publicValues[47]
  let E1963 : F := publicValues[27] * E1962
  let E1964 : F := publicValues[16] - publicValues[48]
  let E1965 : F := publicValues[27] * E1964
  let E1966 : F := publicValues[17] - publicValues[49]
  let E1967 : F := publicValues[27] * E1966
  let E1968 : F := publicValues[18] - publicValues[50]
  let E1969 : F := publicValues[27] * E1968
  let E1970 : F := publicValues[19] - publicValues[51]
  let E1971 : F := publicValues[27] * E1970
  let E1972 : F := publicValues[20] - publicValues[52]
  let E1973 : F := publicValues[27] * E1972
  let E1974 : F := publicValues[21] - publicValues[53]
  let E1975 : F := publicValues[27] * E1974
  let E1976 : F := publicValues[22] - publicValues[54]
  let E1977 : F := publicValues[27] * E1976
  let E1978 : F := publicValues[23] - publicValues[55]
  let E1979 : F := publicValues[27] * E1978
  let E1980 : F := publicValues[24] - publicValues[56]
  let E1981 : F := publicValues[27] * E1980
  let E1982 : F := publicValues[25] - publicValues[57]
  let E1983 : F := publicValues[27] * E1982
  let E1984 : F := publicValues[26] - publicValues[58]
  let E1985 : F := publicValues[27] * E1984
  let E1986 : F := publicValues[27] - publicValues[59]
  let E1987 : F := publicValues[27] * E1986
  let E1988 : F := publicValues[28] - publicValues[60]
  let E1989 : F := publicValues[27] * E1988
  let E1990 : F := publicValues[29] - publicValues[61]
  let E1991 : F := publicValues[27] * E1990
  let E1992 : F := publicValues[30] - publicValues[62]
  let E1993 : F := publicValues[27] * E1992
  let E1994 : F := publicValues[31] - publicValues[63]
  let E1995 : F := publicValues[27] * E1994
  let E1996 : F := publicValues[0] - publicValues[32]
  let E1997 : F := publicValues[28] * E1996
  let E1998 : F := publicValues[1] - publicValues[33]
  let E1999 : F := publicValues[28] * E1998
  let E2000 : F := publicValues[2] - publicValues[34]
  let E2001 : F := publicValues[28] * E2000
  let E2002 : F := publicValues[3] - publicValues[35]
  let E2003 : F := publicValues[28] * E2002
  let E2004 : F := publicValues[4] - publicValues[36]
  let E2005 : F := publicValues[28] * E2004
  let E2006 : F := publicValues[5] - publicValues[37]
  let E2007 : F := publicValues[28] * E2006
  let E2008 : F := publicValues[6] - publicValues[38]
  let E2009 : F := publicValues[28] * E2008
  let E2010 : F := publicValues[7] - publicValues[39]
  let E2011 : F := publicValues[28] * E2010
  let E2012 : F := publicValues[8] - publicValues[40]
  let E2013 : F := publicValues[28] * E2012
  let E2014 : F := publicValues[9] - publicValues[41]
  let E2015 : F := publicValues[28] * E2014
  let E2016 : F := publicValues[10] - publicValues[42]
  let E2017 : F := publicValues[28] * E2016
  [
    E1891,
    E1893,
    E1895,
    E1897,
    E1899,
    E1901,
    E1903,
    E1905,
    E1907,
    E1909,
    E1911,
    E1913,
    E1915,
    E1917,
    E1919,
    E1921,
    E1923,
    E1925,
    E1927,
    E1929,
    E1931,
    E1933,
    E1935,
    E1937,
    E1939,
    E1941,
    E1943,
    E1945,
    E1947,
    E1949,
    E1951,
    E1953,
    E1955,
    E1957,
    E1959,
    E1961,
    E1963,
    E1965,
    E1967,
    E1969,
    E1971,
    E1973,
    E1975,
    E1977,
    E1979,
    E1981,
    E1983,
    E1985,
    E1987,
    E1989,
    E1991,
    E1993,
    E1995,
    E1997,
    E1999,
    E2001,
    E2003,
    E2005,
    E2007,
    E2009,
    E2011,
    E2013,
    E2015,
    E2017,
  ]

@[irreducible] def assertsPart16 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E2018 : F := publicValues[11] - publicValues[43]
  let E2019 : F := publicValues[28] * E2018
  let E2020 : F := publicValues[12] - publicValues[44]
  let E2021 : F := publicValues[28] * E2020
  let E2022 : F := publicValues[13] - publicValues[45]
  let E2023 : F := publicValues[28] * E2022
  let E2024 : F := publicValues[14] - publicValues[46]
  let E2025 : F := publicValues[28] * E2024
  let E2026 : F := publicValues[15] - publicValues[47]
  let E2027 : F := publicValues[28] * E2026
  let E2028 : F := publicValues[16] - publicValues[48]
  let E2029 : F := publicValues[28] * E2028
  let E2030 : F := publicValues[17] - publicValues[49]
  let E2031 : F := publicValues[28] * E2030
  let E2032 : F := publicValues[18] - publicValues[50]
  let E2033 : F := publicValues[28] * E2032
  let E2034 : F := publicValues[19] - publicValues[51]
  let E2035 : F := publicValues[28] * E2034
  let E2036 : F := publicValues[20] - publicValues[52]
  let E2037 : F := publicValues[28] * E2036
  let E2038 : F := publicValues[21] - publicValues[53]
  let E2039 : F := publicValues[28] * E2038
  let E2040 : F := publicValues[22] - publicValues[54]
  let E2041 : F := publicValues[28] * E2040
  let E2042 : F := publicValues[23] - publicValues[55]
  let E2043 : F := publicValues[28] * E2042
  let E2044 : F := publicValues[24] - publicValues[56]
  let E2045 : F := publicValues[28] * E2044
  let E2046 : F := publicValues[25] - publicValues[57]
  let E2047 : F := publicValues[28] * E2046
  let E2048 : F := publicValues[26] - publicValues[58]
  let E2049 : F := publicValues[28] * E2048
  let E2050 : F := publicValues[27] - publicValues[59]
  let E2051 : F := publicValues[28] * E2050
  let E2052 : F := publicValues[28] - publicValues[60]
  let E2053 : F := publicValues[28] * E2052
  let E2054 : F := publicValues[29] - publicValues[61]
  let E2055 : F := publicValues[28] * E2054
  let E2056 : F := publicValues[30] - publicValues[62]
  let E2057 : F := publicValues[28] * E2056
  let E2058 : F := publicValues[31] - publicValues[63]
  let E2059 : F := publicValues[28] * E2058
  let E2060 : F := publicValues[0] - publicValues[32]
  let E2061 : F := publicValues[29] * E2060
  let E2062 : F := publicValues[1] - publicValues[33]
  let E2063 : F := publicValues[29] * E2062
  let E2064 : F := publicValues[2] - publicValues[34]
  let E2065 : F := publicValues[29] * E2064
  let E2066 : F := publicValues[3] - publicValues[35]
  let E2067 : F := publicValues[29] * E2066
  let E2068 : F := publicValues[4] - publicValues[36]
  let E2069 : F := publicValues[29] * E2068
  let E2070 : F := publicValues[5] - publicValues[37]
  let E2071 : F := publicValues[29] * E2070
  let E2072 : F := publicValues[6] - publicValues[38]
  let E2073 : F := publicValues[29] * E2072
  let E2074 : F := publicValues[7] - publicValues[39]
  let E2075 : F := publicValues[29] * E2074
  let E2076 : F := publicValues[8] - publicValues[40]
  let E2077 : F := publicValues[29] * E2076
  let E2078 : F := publicValues[9] - publicValues[41]
  let E2079 : F := publicValues[29] * E2078
  let E2080 : F := publicValues[10] - publicValues[42]
  let E2081 : F := publicValues[29] * E2080
  let E2082 : F := publicValues[11] - publicValues[43]
  let E2083 : F := publicValues[29] * E2082
  let E2084 : F := publicValues[12] - publicValues[44]
  let E2085 : F := publicValues[29] * E2084
  let E2086 : F := publicValues[13] - publicValues[45]
  let E2087 : F := publicValues[29] * E2086
  let E2088 : F := publicValues[14] - publicValues[46]
  let E2089 : F := publicValues[29] * E2088
  let E2090 : F := publicValues[15] - publicValues[47]
  let E2091 : F := publicValues[29] * E2090
  let E2092 : F := publicValues[16] - publicValues[48]
  let E2093 : F := publicValues[29] * E2092
  let E2094 : F := publicValues[17] - publicValues[49]
  let E2095 : F := publicValues[29] * E2094
  let E2096 : F := publicValues[18] - publicValues[50]
  let E2097 : F := publicValues[29] * E2096
  let E2098 : F := publicValues[19] - publicValues[51]
  let E2099 : F := publicValues[29] * E2098
  let E2100 : F := publicValues[20] - publicValues[52]
  let E2101 : F := publicValues[29] * E2100
  let E2102 : F := publicValues[21] - publicValues[53]
  let E2103 : F := publicValues[29] * E2102
  let E2104 : F := publicValues[22] - publicValues[54]
  let E2105 : F := publicValues[29] * E2104
  let E2106 : F := publicValues[23] - publicValues[55]
  let E2107 : F := publicValues[29] * E2106
  let E2108 : F := publicValues[24] - publicValues[56]
  let E2109 : F := publicValues[29] * E2108
  let E2110 : F := publicValues[25] - publicValues[57]
  let E2111 : F := publicValues[29] * E2110
  let E2112 : F := publicValues[26] - publicValues[58]
  let E2113 : F := publicValues[29] * E2112
  let E2114 : F := publicValues[27] - publicValues[59]
  let E2115 : F := publicValues[29] * E2114
  let E2116 : F := publicValues[28] - publicValues[60]
  let E2117 : F := publicValues[29] * E2116
  let E2118 : F := publicValues[29] - publicValues[61]
  let E2119 : F := publicValues[29] * E2118
  let E2120 : F := publicValues[30] - publicValues[62]
  let E2121 : F := publicValues[29] * E2120
  let E2122 : F := publicValues[31] - publicValues[63]
  let E2123 : F := publicValues[29] * E2122
  let E2124 : F := publicValues[0] - publicValues[32]
  let E2125 : F := publicValues[30] * E2124
  let E2126 : F := publicValues[1] - publicValues[33]
  let E2127 : F := publicValues[30] * E2126
  let E2128 : F := publicValues[2] - publicValues[34]
  let E2129 : F := publicValues[30] * E2128
  let E2130 : F := publicValues[3] - publicValues[35]
  let E2131 : F := publicValues[30] * E2130
  let E2132 : F := publicValues[4] - publicValues[36]
  let E2133 : F := publicValues[30] * E2132
  let E2134 : F := publicValues[5] - publicValues[37]
  let E2135 : F := publicValues[30] * E2134
  let E2136 : F := publicValues[6] - publicValues[38]
  let E2137 : F := publicValues[30] * E2136
  let E2138 : F := publicValues[7] - publicValues[39]
  let E2139 : F := publicValues[30] * E2138
  let E2140 : F := publicValues[8] - publicValues[40]
  let E2141 : F := publicValues[30] * E2140
  let E2142 : F := publicValues[9] - publicValues[41]
  let E2143 : F := publicValues[30] * E2142
  let E2144 : F := publicValues[10] - publicValues[42]
  let E2145 : F := publicValues[30] * E2144
  [
    E2019,
    E2021,
    E2023,
    E2025,
    E2027,
    E2029,
    E2031,
    E2033,
    E2035,
    E2037,
    E2039,
    E2041,
    E2043,
    E2045,
    E2047,
    E2049,
    E2051,
    E2053,
    E2055,
    E2057,
    E2059,
    E2061,
    E2063,
    E2065,
    E2067,
    E2069,
    E2071,
    E2073,
    E2075,
    E2077,
    E2079,
    E2081,
    E2083,
    E2085,
    E2087,
    E2089,
    E2091,
    E2093,
    E2095,
    E2097,
    E2099,
    E2101,
    E2103,
    E2105,
    E2107,
    E2109,
    E2111,
    E2113,
    E2115,
    E2117,
    E2119,
    E2121,
    E2123,
    E2125,
    E2127,
    E2129,
    E2131,
    E2133,
    E2135,
    E2137,
    E2139,
    E2141,
    E2143,
    E2145,
  ]

@[irreducible] def assertsPart17 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E2146 : F := publicValues[11] - publicValues[43]
  let E2147 : F := publicValues[30] * E2146
  let E2148 : F := publicValues[12] - publicValues[44]
  let E2149 : F := publicValues[30] * E2148
  let E2150 : F := publicValues[13] - publicValues[45]
  let E2151 : F := publicValues[30] * E2150
  let E2152 : F := publicValues[14] - publicValues[46]
  let E2153 : F := publicValues[30] * E2152
  let E2154 : F := publicValues[15] - publicValues[47]
  let E2155 : F := publicValues[30] * E2154
  let E2156 : F := publicValues[16] - publicValues[48]
  let E2157 : F := publicValues[30] * E2156
  let E2158 : F := publicValues[17] - publicValues[49]
  let E2159 : F := publicValues[30] * E2158
  let E2160 : F := publicValues[18] - publicValues[50]
  let E2161 : F := publicValues[30] * E2160
  let E2162 : F := publicValues[19] - publicValues[51]
  let E2163 : F := publicValues[30] * E2162
  let E2164 : F := publicValues[20] - publicValues[52]
  let E2165 : F := publicValues[30] * E2164
  let E2166 : F := publicValues[21] - publicValues[53]
  let E2167 : F := publicValues[30] * E2166
  let E2168 : F := publicValues[22] - publicValues[54]
  let E2169 : F := publicValues[30] * E2168
  let E2170 : F := publicValues[23] - publicValues[55]
  let E2171 : F := publicValues[30] * E2170
  let E2172 : F := publicValues[24] - publicValues[56]
  let E2173 : F := publicValues[30] * E2172
  let E2174 : F := publicValues[25] - publicValues[57]
  let E2175 : F := publicValues[30] * E2174
  let E2176 : F := publicValues[26] - publicValues[58]
  let E2177 : F := publicValues[30] * E2176
  let E2178 : F := publicValues[27] - publicValues[59]
  let E2179 : F := publicValues[30] * E2178
  let E2180 : F := publicValues[28] - publicValues[60]
  let E2181 : F := publicValues[30] * E2180
  let E2182 : F := publicValues[29] - publicValues[61]
  let E2183 : F := publicValues[30] * E2182
  let E2184 : F := publicValues[30] - publicValues[62]
  let E2185 : F := publicValues[30] * E2184
  let E2186 : F := publicValues[31] - publicValues[63]
  let E2187 : F := publicValues[30] * E2186
  let E2188 : F := publicValues[0] - publicValues[32]
  let E2189 : F := publicValues[31] * E2188
  let E2190 : F := publicValues[1] - publicValues[33]
  let E2191 : F := publicValues[31] * E2190
  let E2192 : F := publicValues[2] - publicValues[34]
  let E2193 : F := publicValues[31] * E2192
  let E2194 : F := publicValues[3] - publicValues[35]
  let E2195 : F := publicValues[31] * E2194
  let E2196 : F := publicValues[4] - publicValues[36]
  let E2197 : F := publicValues[31] * E2196
  let E2198 : F := publicValues[5] - publicValues[37]
  let E2199 : F := publicValues[31] * E2198
  let E2200 : F := publicValues[6] - publicValues[38]
  let E2201 : F := publicValues[31] * E2200
  let E2202 : F := publicValues[7] - publicValues[39]
  let E2203 : F := publicValues[31] * E2202
  let E2204 : F := publicValues[8] - publicValues[40]
  let E2205 : F := publicValues[31] * E2204
  let E2206 : F := publicValues[9] - publicValues[41]
  let E2207 : F := publicValues[31] * E2206
  let E2208 : F := publicValues[10] - publicValues[42]
  let E2209 : F := publicValues[31] * E2208
  let E2210 : F := publicValues[11] - publicValues[43]
  let E2211 : F := publicValues[31] * E2210
  let E2212 : F := publicValues[12] - publicValues[44]
  let E2213 : F := publicValues[31] * E2212
  let E2214 : F := publicValues[13] - publicValues[45]
  let E2215 : F := publicValues[31] * E2214
  let E2216 : F := publicValues[14] - publicValues[46]
  let E2217 : F := publicValues[31] * E2216
  let E2218 : F := publicValues[15] - publicValues[47]
  let E2219 : F := publicValues[31] * E2218
  let E2220 : F := publicValues[16] - publicValues[48]
  let E2221 : F := publicValues[31] * E2220
  let E2222 : F := publicValues[17] - publicValues[49]
  let E2223 : F := publicValues[31] * E2222
  let E2224 : F := publicValues[18] - publicValues[50]
  let E2225 : F := publicValues[31] * E2224
  let E2226 : F := publicValues[19] - publicValues[51]
  let E2227 : F := publicValues[31] * E2226
  let E2228 : F := publicValues[20] - publicValues[52]
  let E2229 : F := publicValues[31] * E2228
  let E2230 : F := publicValues[21] - publicValues[53]
  let E2231 : F := publicValues[31] * E2230
  let E2232 : F := publicValues[22] - publicValues[54]
  let E2233 : F := publicValues[31] * E2232
  let E2234 : F := publicValues[23] - publicValues[55]
  let E2235 : F := publicValues[31] * E2234
  let E2236 : F := publicValues[24] - publicValues[56]
  let E2237 : F := publicValues[31] * E2236
  let E2238 : F := publicValues[25] - publicValues[57]
  let E2239 : F := publicValues[31] * E2238
  let E2240 : F := publicValues[26] - publicValues[58]
  let E2241 : F := publicValues[31] * E2240
  let E2242 : F := publicValues[27] - publicValues[59]
  let E2243 : F := publicValues[31] * E2242
  let E2244 : F := publicValues[28] - publicValues[60]
  let E2245 : F := publicValues[31] * E2244
  let E2246 : F := publicValues[29] - publicValues[61]
  let E2247 : F := publicValues[31] * E2246
  let E2248 : F := publicValues[30] - publicValues[62]
  let E2249 : F := publicValues[31] * E2248
  let E2250 : F := publicValues[31] - publicValues[63]
  let E2251 : F := publicValues[31] * E2250
  let E2252 : F := publicValues[0] - publicValues[32]
  let E2253 : F := publicValues[144] * E2252
  let E2254 : F := publicValues[1] - publicValues[33]
  let E2255 : F := publicValues[144] * E2254
  let E2256 : F := publicValues[2] - publicValues[34]
  let E2257 : F := publicValues[144] * E2256
  let E2258 : F := publicValues[3] - publicValues[35]
  let E2259 : F := publicValues[144] * E2258
  let E2260 : F := publicValues[4] - publicValues[36]
  let E2261 : F := publicValues[144] * E2260
  let E2262 : F := publicValues[5] - publicValues[37]
  let E2263 : F := publicValues[144] * E2262
  let E2264 : F := publicValues[6] - publicValues[38]
  let E2265 : F := publicValues[144] * E2264
  let E2266 : F := publicValues[7] - publicValues[39]
  let E2267 : F := publicValues[144] * E2266
  let E2268 : F := publicValues[8] - publicValues[40]
  let E2269 : F := publicValues[144] * E2268
  let E2270 : F := publicValues[9] - publicValues[41]
  let E2271 : F := publicValues[144] * E2270
  let E2272 : F := publicValues[10] - publicValues[42]
  let E2273 : F := publicValues[144] * E2272
  [
    E2147,
    E2149,
    E2151,
    E2153,
    E2155,
    E2157,
    E2159,
    E2161,
    E2163,
    E2165,
    E2167,
    E2169,
    E2171,
    E2173,
    E2175,
    E2177,
    E2179,
    E2181,
    E2183,
    E2185,
    E2187,
    E2189,
    E2191,
    E2193,
    E2195,
    E2197,
    E2199,
    E2201,
    E2203,
    E2205,
    E2207,
    E2209,
    E2211,
    E2213,
    E2215,
    E2217,
    E2219,
    E2221,
    E2223,
    E2225,
    E2227,
    E2229,
    E2231,
    E2233,
    E2235,
    E2237,
    E2239,
    E2241,
    E2243,
    E2245,
    E2247,
    E2249,
    E2251,
    E2253,
    E2255,
    E2257,
    E2259,
    E2261,
    E2263,
    E2265,
    E2267,
    E2269,
    E2271,
    E2273,
  ]

@[irreducible] def assertsPart18 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E2274 : F := publicValues[11] - publicValues[43]
  let E2275 : F := publicValues[144] * E2274
  let E2276 : F := publicValues[12] - publicValues[44]
  let E2277 : F := publicValues[144] * E2276
  let E2278 : F := publicValues[13] - publicValues[45]
  let E2279 : F := publicValues[144] * E2278
  let E2280 : F := publicValues[14] - publicValues[46]
  let E2281 : F := publicValues[144] * E2280
  let E2282 : F := publicValues[15] - publicValues[47]
  let E2283 : F := publicValues[144] * E2282
  let E2284 : F := publicValues[16] - publicValues[48]
  let E2285 : F := publicValues[144] * E2284
  let E2286 : F := publicValues[17] - publicValues[49]
  let E2287 : F := publicValues[144] * E2286
  let E2288 : F := publicValues[18] - publicValues[50]
  let E2289 : F := publicValues[144] * E2288
  let E2290 : F := publicValues[19] - publicValues[51]
  let E2291 : F := publicValues[144] * E2290
  let E2292 : F := publicValues[20] - publicValues[52]
  let E2293 : F := publicValues[144] * E2292
  let E2294 : F := publicValues[21] - publicValues[53]
  let E2295 : F := publicValues[144] * E2294
  let E2296 : F := publicValues[22] - publicValues[54]
  let E2297 : F := publicValues[144] * E2296
  let E2298 : F := publicValues[23] - publicValues[55]
  let E2299 : F := publicValues[144] * E2298
  let E2300 : F := publicValues[24] - publicValues[56]
  let E2301 : F := publicValues[144] * E2300
  let E2302 : F := publicValues[25] - publicValues[57]
  let E2303 : F := publicValues[144] * E2302
  let E2304 : F := publicValues[26] - publicValues[58]
  let E2305 : F := publicValues[144] * E2304
  let E2306 : F := publicValues[27] - publicValues[59]
  let E2307 : F := publicValues[144] * E2306
  let E2308 : F := publicValues[28] - publicValues[60]
  let E2309 : F := publicValues[144] * E2308
  let E2310 : F := publicValues[29] - publicValues[61]
  let E2311 : F := publicValues[144] * E2310
  let E2312 : F := publicValues[30] - publicValues[62]
  let E2313 : F := publicValues[144] * E2312
  let E2314 : F := publicValues[31] - publicValues[63]
  let E2315 : F := publicValues[144] * E2314
  let E2316 : F := publicValues[146] - 1
  let E2317 : F := publicValues[146] * E2316
  let E2318 : F := publicValues[147] - 1
  let E2319 : F := publicValues[147] * E2318
  let E2320 : F := publicValues[147] - 1
  let E2321 : F := publicValues[146] * E2320
  let E2322 : F := publicValues[88] - 1
  let E2323 : F := publicValues[146] - publicValues[147]
  let E2324 : F := E2322 * E2323
  let E2325 : F := publicValues[88] - 1
  let E2326 : F := publicValues[64] - publicValues[72]
  let E2327 : F := E2325 * E2326
  let E2328 : F := publicValues[65] - publicValues[73]
  let E2329 : F := E2325 * E2328
  let E2330 : F := publicValues[66] - publicValues[74]
  let E2331 : F := E2325 * E2330
  let E2332 : F := publicValues[67] - publicValues[75]
  let E2333 : F := E2325 * E2332
  let E2334 : F := publicValues[68] - publicValues[76]
  let E2335 : F := E2325 * E2334
  let E2336 : F := publicValues[69] - publicValues[77]
  let E2337 : F := E2325 * E2336
  let E2338 : F := publicValues[70] - publicValues[78]
  let E2339 : F := E2325 * E2338
  let E2340 : F := publicValues[71] - publicValues[79]
  let E2341 : F := E2325 * E2340
  let E2342 : F := publicValues[64] - publicValues[72]
  let E2343 : F := publicValues[64] * E2342
  let E2344 : F := publicValues[65] - publicValues[73]
  let E2345 : F := publicValues[64] * E2344
  let E2346 : F := publicValues[66] - publicValues[74]
  let E2347 : F := publicValues[64] * E2346
  let E2348 : F := publicValues[67] - publicValues[75]
  let E2349 : F := publicValues[64] * E2348
  let E2350 : F := publicValues[68] - publicValues[76]
  let E2351 : F := publicValues[64] * E2350
  let E2352 : F := publicValues[69] - publicValues[77]
  let E2353 : F := publicValues[64] * E2352
  let E2354 : F := publicValues[70] - publicValues[78]
  let E2355 : F := publicValues[64] * E2354
  let E2356 : F := publicValues[71] - publicValues[79]
  let E2357 : F := publicValues[64] * E2356
  let E2358 : F := publicValues[64] - publicValues[72]
  let E2359 : F := publicValues[65] * E2358
  let E2360 : F := publicValues[65] - publicValues[73]
  let E2361 : F := publicValues[65] * E2360
  let E2362 : F := publicValues[66] - publicValues[74]
  let E2363 : F := publicValues[65] * E2362
  let E2364 : F := publicValues[67] - publicValues[75]
  let E2365 : F := publicValues[65] * E2364
  let E2366 : F := publicValues[68] - publicValues[76]
  let E2367 : F := publicValues[65] * E2366
  let E2368 : F := publicValues[69] - publicValues[77]
  let E2369 : F := publicValues[65] * E2368
  let E2370 : F := publicValues[70] - publicValues[78]
  let E2371 : F := publicValues[65] * E2370
  let E2372 : F := publicValues[71] - publicValues[79]
  let E2373 : F := publicValues[65] * E2372
  let E2374 : F := publicValues[64] - publicValues[72]
  let E2375 : F := publicValues[66] * E2374
  let E2376 : F := publicValues[65] - publicValues[73]
  let E2377 : F := publicValues[66] * E2376
  let E2378 : F := publicValues[66] - publicValues[74]
  let E2379 : F := publicValues[66] * E2378
  let E2380 : F := publicValues[67] - publicValues[75]
  let E2381 : F := publicValues[66] * E2380
  let E2382 : F := publicValues[68] - publicValues[76]
  let E2383 : F := publicValues[66] * E2382
  let E2384 : F := publicValues[69] - publicValues[77]
  let E2385 : F := publicValues[66] * E2384
  let E2386 : F := publicValues[70] - publicValues[78]
  let E2387 : F := publicValues[66] * E2386
  let E2388 : F := publicValues[71] - publicValues[79]
  let E2389 : F := publicValues[66] * E2388
  let E2390 : F := publicValues[64] - publicValues[72]
  let E2391 : F := publicValues[67] * E2390
  let E2392 : F := publicValues[65] - publicValues[73]
  let E2393 : F := publicValues[67] * E2392
  let E2394 : F := publicValues[66] - publicValues[74]
  let E2395 : F := publicValues[67] * E2394
  let E2396 : F := publicValues[67] - publicValues[75]
  let E2397 : F := publicValues[67] * E2396
  let E2398 : F := publicValues[68] - publicValues[76]
  let E2399 : F := publicValues[67] * E2398
  let E2400 : F := publicValues[69] - publicValues[77]
  let E2401 : F := publicValues[67] * E2400
  let E2402 : F := publicValues[70] - publicValues[78]
  let E2403 : F := publicValues[67] * E2402
  [
    E2275,
    E2277,
    E2279,
    E2281,
    E2283,
    E2285,
    E2287,
    E2289,
    E2291,
    E2293,
    E2295,
    E2297,
    E2299,
    E2301,
    E2303,
    E2305,
    E2307,
    E2309,
    E2311,
    E2313,
    E2315,
    E2317,
    E2319,
    E2321,
    E2324,
    E2327,
    E2329,
    E2331,
    E2333,
    E2335,
    E2337,
    E2339,
    E2341,
    E2343,
    E2345,
    E2347,
    E2349,
    E2351,
    E2353,
    E2355,
    E2357,
    E2359,
    E2361,
    E2363,
    E2365,
    E2367,
    E2369,
    E2371,
    E2373,
    E2375,
    E2377,
    E2379,
    E2381,
    E2383,
    E2385,
    E2387,
    E2389,
    E2391,
    E2393,
    E2395,
    E2397,
    E2399,
    E2401,
    E2403,
  ]

@[irreducible] def assertsPart19 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  let E2404 : F := publicValues[71] - publicValues[79]
  let E2405 : F := publicValues[67] * E2404
  let E2406 : F := publicValues[64] - publicValues[72]
  let E2407 : F := publicValues[68] * E2406
  let E2408 : F := publicValues[65] - publicValues[73]
  let E2409 : F := publicValues[68] * E2408
  let E2410 : F := publicValues[66] - publicValues[74]
  let E2411 : F := publicValues[68] * E2410
  let E2412 : F := publicValues[67] - publicValues[75]
  let E2413 : F := publicValues[68] * E2412
  let E2414 : F := publicValues[68] - publicValues[76]
  let E2415 : F := publicValues[68] * E2414
  let E2416 : F := publicValues[69] - publicValues[77]
  let E2417 : F := publicValues[68] * E2416
  let E2418 : F := publicValues[70] - publicValues[78]
  let E2419 : F := publicValues[68] * E2418
  let E2420 : F := publicValues[71] - publicValues[79]
  let E2421 : F := publicValues[68] * E2420
  let E2422 : F := publicValues[64] - publicValues[72]
  let E2423 : F := publicValues[69] * E2422
  let E2424 : F := publicValues[65] - publicValues[73]
  let E2425 : F := publicValues[69] * E2424
  let E2426 : F := publicValues[66] - publicValues[74]
  let E2427 : F := publicValues[69] * E2426
  let E2428 : F := publicValues[67] - publicValues[75]
  let E2429 : F := publicValues[69] * E2428
  let E2430 : F := publicValues[68] - publicValues[76]
  let E2431 : F := publicValues[69] * E2430
  let E2432 : F := publicValues[69] - publicValues[77]
  let E2433 : F := publicValues[69] * E2432
  let E2434 : F := publicValues[70] - publicValues[78]
  let E2435 : F := publicValues[69] * E2434
  let E2436 : F := publicValues[71] - publicValues[79]
  let E2437 : F := publicValues[69] * E2436
  let E2438 : F := publicValues[64] - publicValues[72]
  let E2439 : F := publicValues[70] * E2438
  let E2440 : F := publicValues[65] - publicValues[73]
  let E2441 : F := publicValues[70] * E2440
  let E2442 : F := publicValues[66] - publicValues[74]
  let E2443 : F := publicValues[70] * E2442
  let E2444 : F := publicValues[67] - publicValues[75]
  let E2445 : F := publicValues[70] * E2444
  let E2446 : F := publicValues[68] - publicValues[76]
  let E2447 : F := publicValues[70] * E2446
  let E2448 : F := publicValues[69] - publicValues[77]
  let E2449 : F := publicValues[70] * E2448
  let E2450 : F := publicValues[70] - publicValues[78]
  let E2451 : F := publicValues[70] * E2450
  let E2452 : F := publicValues[71] - publicValues[79]
  let E2453 : F := publicValues[70] * E2452
  let E2454 : F := publicValues[64] - publicValues[72]
  let E2455 : F := publicValues[71] * E2454
  let E2456 : F := publicValues[65] - publicValues[73]
  let E2457 : F := publicValues[71] * E2456
  let E2458 : F := publicValues[66] - publicValues[74]
  let E2459 : F := publicValues[71] * E2458
  let E2460 : F := publicValues[67] - publicValues[75]
  let E2461 : F := publicValues[71] * E2460
  let E2462 : F := publicValues[68] - publicValues[76]
  let E2463 : F := publicValues[71] * E2462
  let E2464 : F := publicValues[69] - publicValues[77]
  let E2465 : F := publicValues[71] * E2464
  let E2466 : F := publicValues[70] - publicValues[78]
  let E2467 : F := publicValues[71] * E2466
  let E2468 : F := publicValues[71] - publicValues[79]
  let E2469 : F := publicValues[71] * E2468
  let E2470 : F := publicValues[64] - publicValues[72]
  let E2471 : F := publicValues[146] * E2470
  let E2472 : F := publicValues[65] - publicValues[73]
  let E2473 : F := publicValues[146] * E2472
  let E2474 : F := publicValues[66] - publicValues[74]
  let E2475 : F := publicValues[146] * E2474
  let E2476 : F := publicValues[67] - publicValues[75]
  let E2477 : F := publicValues[146] * E2476
  let E2478 : F := publicValues[68] - publicValues[76]
  let E2479 : F := publicValues[146] * E2478
  let E2480 : F := publicValues[69] - publicValues[77]
  let E2481 : F := publicValues[146] * E2480
  let E2482 : F := publicValues[70] - publicValues[78]
  let E2483 : F := publicValues[146] * E2482
  let E2484 : F := publicValues[71] - publicValues[79]
  let E2485 : F := publicValues[146] * E2484
  let E2486 : F := publicValues[151] - 1
  let E2487 : F := publicValues[151] * E2486
  let E2488 : F := publicValues[151] - 1
  let E2489 : F := publicValues[151] * E2488
  [
    E2405,
    E2407,
    E2409,
    E2411,
    E2413,
    E2415,
    E2417,
    E2419,
    E2421,
    E2423,
    E2425,
    E2427,
    E2429,
    E2431,
    E2433,
    E2435,
    E2437,
    E2439,
    E2441,
    E2443,
    E2445,
    E2447,
    E2449,
    E2451,
    E2453,
    E2455,
    E2457,
    E2459,
    E2461,
    E2463,
    E2465,
    E2467,
    E2469,
    E2471,
    E2473,
    E2475,
    E2477,
    E2479,
    E2481,
    E2483,
    E2485,
    E2487,
    E2489,
  ]

@[irreducible] def asserts {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List F :=
  assertsPart0 publicValues ++ assertsPart1 publicValues ++ assertsPart2 publicValues ++ assertsPart3 publicValues ++ assertsPart4 publicValues ++ assertsPart5 publicValues ++ assertsPart6 publicValues ++ assertsPart7 publicValues ++ assertsPart8 publicValues ++ assertsPart9 publicValues ++ assertsPart10 publicValues ++ assertsPart11 publicValues ++ assertsPart12 publicValues ++ assertsPart13 publicValues ++ assertsPart14 publicValues ++ assertsPart15 publicValues ++ assertsPart16 publicValues ++ assertsPart17 publicValues ++ assertsPart18 publicValues ++ assertsPart19 publicValues

@[irreducible] def interactionsPart0 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List (Interaction F) :=
  let E0 : F := publicValues[113] * 256
  let E1 : F := publicValues[114] + E0
  let E2 : F := publicValues[115] * 65536
  let E3 : F := publicValues[116] + E2
  let E4 : F := publicValues[117] * 256
  let E5 : F := publicValues[118] + E4
  let E6 : F := publicValues[119] * 65536
  let E7 : F := publicValues[120] + E6
  let E8 : F := publicValues[116] - 1
  let E9 : F := E8 * ((8 : F)⁻¹)
  let E10 : F := publicValues[120] - 1
  let E11 : F := E10 * ((8 : F)⁻¹)
  [
    ⟨.send, (.byte 6 publicValues[113] 16 0), 1⟩,
    ⟨.send, (.byte 6 E9 13 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[117] 16 0), 1⟩,
    ⟨.send, (.byte 6 E11 13 0), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[114] publicValues[115]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[118] publicValues[119]), 1⟩,
    ⟨.send, (.byte 6 publicValues[80] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[83] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[81] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[84] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[82] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[85] 16 0), 1⟩,
    ⟨.send, (.state E1 E3 publicValues[80] publicValues[81] publicValues[82]), 1⟩,
    ⟨.receive, (.state E5 E7 publicValues[83] publicValues[84] publicValues[85]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[0] publicValues[1]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[2] publicValues[3]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[32] publicValues[33]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[34] publicValues[35]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[4] publicValues[5]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[6] publicValues[7]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[36] publicValues[37]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[38] publicValues[39]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[8] publicValues[9]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[10] publicValues[11]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[40] publicValues[41]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[42] publicValues[43]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[12] publicValues[13]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[14] publicValues[15]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[44] publicValues[45]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[46] publicValues[47]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[16] publicValues[17]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[18] publicValues[19]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[48] publicValues[49]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[50] publicValues[51]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[20] publicValues[21]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[22] publicValues[23]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[52] publicValues[53]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[54] publicValues[55]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[24] publicValues[25]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[26] publicValues[27]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[56] publicValues[57]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[58] publicValues[59]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[28] publicValues[29]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[30] publicValues[31]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[60] publicValues[61]), 1⟩,
    ⟨.send, (.byte 3 0 publicValues[62] publicValues[63]), 1⟩,
    ⟨.send, (.raw .globalAccumulation [0, 21053971, 90322736, 156256384, 23627556, 34171264, 126183783, 25645942, 2020310104, 1513506566, 1843922297, 2003644209, 805967281, 1882435203, 1623804682]), 1⟩,
    ⟨.receive, (.raw .globalAccumulation [publicValues[129], publicValues[130], publicValues[131], publicValues[132], publicValues[133], publicValues[134], publicValues[135], publicValues[136], publicValues[137], publicValues[138], publicValues[139], publicValues[140], publicValues[141], publicValues[142], publicValues[143]]), 1⟩,
    ⟨.send, (.byte 6 publicValues[89] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[92] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[90] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[93] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[91] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[94] 16 0), 1⟩,
    ⟨.send, (.raw .memoryGlobalInitControl [0, publicValues[89], publicValues[90], publicValues[91], 1]), 1⟩,
    ⟨.receive, (.raw .memoryGlobalInitControl [publicValues[125], publicValues[92], publicValues[93], publicValues[94], 1]), 1⟩,
    ⟨.send, (.byte 6 publicValues[95] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[98] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[96] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[99] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[97] 16 0), 1⟩,
    ⟨.send, (.byte 6 publicValues[100] 16 0), 1⟩,
    ⟨.send, (.raw .memoryGlobalFinalizeControl [0, publicValues[95], publicValues[96], publicValues[97], 1]), 1⟩,
    ⟨.receive, (.raw .memoryGlobalFinalizeControl [publicValues[126], publicValues[98], publicValues[99], publicValues[100], 1]), 1⟩,
  ]

@[irreducible] def interactionsPart1 {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List (Interaction F) :=
  [
    ⟨.send, (.raw .pageProtGlobalInitControl [0, publicValues[101], publicValues[102], publicValues[103], 1]), publicValues[151]⟩,
    ⟨.receive, (.raw .pageProtGlobalInitControl [publicValues[127], publicValues[104], publicValues[105], publicValues[106], 1]), publicValues[151]⟩,
    ⟨.send, (.raw .pageProtGlobalFinalizeControl [0, publicValues[107], publicValues[108], publicValues[109], 1]), publicValues[151]⟩,
    ⟨.receive, (.raw .pageProtGlobalFinalizeControl [publicValues[128], publicValues[110], publicValues[111], publicValues[112], 1]), publicValues[151]⟩,
  ]

@[irreducible] def interactions {F : Type} [Field F] [CoeHead F ℕ]
  (publicValues : (Vector F 160))
  : List (Interaction F) :=
  interactionsPart0 publicValues ++ interactionsPart1 publicValues

end PublicValuesOracle

end SP1Clean.Extracted
