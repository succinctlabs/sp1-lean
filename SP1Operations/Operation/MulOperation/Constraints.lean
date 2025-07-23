import SP1Foundations
import SP1Operations.Operation.MulOperation.Operation
import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.U16MSBOperation

namespace MulOperation

set_option maxHeartbeats 500000
section constraints

def constraints
  (a_word : (Word (Fin BB)))
  (b_word : (Word (Fin BB)))
  (c_word : (Word (Fin BB)))
  (cols : MulOperation)
  (is_real : (Fin BB))
  (is_mul : (Fin BB))
  (is_mulh : (Fin BB))
  (is_mulw : (Fin BB))
  (is_mulhu : (Fin BB))
  (is_mulhsu : (Fin BB))
  : SP1ConstraintList :=
  let ⟨⟨⟨[E0, E1, E2, E3, E4, E5, E6, E7]⟩, _⟩, CS0⟩ := U16toU8OperationSafe.constraints #v[b_word[0], b_word[1], b_word[2], b_word[3]] { low_bytes := #v[cols.b_lower_byte.low_bytes[0], cols.b_lower_byte.low_bytes[1], cols.b_lower_byte.low_bytes[2], cols.b_lower_byte.low_bytes[3]] } is_real
  let ⟨⟨⟨[E8, E9, E10, E11, E12, E13, E14, E15]⟩, _⟩, CS1⟩ := U16toU8OperationSafe.constraints #v[c_word[0], c_word[1], c_word[2], c_word[3]] { low_bytes := #v[cols.c_lower_byte.low_bytes[0], cols.c_lower_byte.low_bytes[1], cols.c_lower_byte.low_bytes[2], cols.c_lower_byte.low_bytes[3]] } is_real
  let CS2 : SP1ConstraintList := U16MSBOperation.constraints a_word[1] { msb := cols.product_msb.msb } is_mulw
  let E16 : Fin BB := is_mulh + is_mulhsu
  let E17 : Fin BB := E16 * cols.b_msb
  let E18 : Fin BB := cols.b_sign_extend - E17
  let E19 : Fin BB := is_mulh * cols.c_msb
  let E20 : Fin BB := cols.c_sign_extend - E19
  let E21 : Fin BB := cols.b_sign_extend * 255
  let E22 : Fin BB := cols.c_sign_extend * 255
  let E23 : Fin BB := cols.b_sign_extend * 255
  let E24 : Fin BB := cols.c_sign_extend * 255
  let E25 : Fin BB := cols.b_sign_extend * 255
  let E26 : Fin BB := cols.c_sign_extend * 255
  let E27 : Fin BB := cols.b_sign_extend * 255
  let E28 : Fin BB := cols.c_sign_extend * 255
  let E29 : Fin BB := cols.b_sign_extend * 255
  let E30 : Fin BB := cols.c_sign_extend * 255
  let E31 : Fin BB := cols.b_sign_extend * 255
  let E32 : Fin BB := cols.c_sign_extend * 255
  let E33 : Fin BB := cols.b_sign_extend * 255
  let E34 : Fin BB := cols.c_sign_extend * 255
  let E35 : Fin BB := cols.b_sign_extend * 255
  let E36 : Fin BB := cols.c_sign_extend * 255
  let E37 : Fin BB := E0 * E8
  let E38 : Fin BB := 0 + E37
  let E39 : Fin BB := E0 * E9
  let E40 : Fin BB := 0 + E39
  let E41 : Fin BB := E0 * E10
  let E42 : Fin BB := 0 + E41
  let E43 : Fin BB := E0 * E11
  let E44 : Fin BB := 0 + E43
  let E45 : Fin BB := E0 * E12
  let E46 : Fin BB := 0 + E45
  let E47 : Fin BB := E0 * E13
  let E48 : Fin BB := 0 + E47
  let E49 : Fin BB := E0 * E14
  let E50 : Fin BB := 0 + E49
  let E51 : Fin BB := E0 * E15
  let E52 : Fin BB := 0 + E51
  let E53 : Fin BB := E0 * E22
  let E54 : Fin BB := 0 + E53
  let E55 : Fin BB := E0 * E24
  let E56 : Fin BB := 0 + E55
  let E57 : Fin BB := E0 * E26
  let E58 : Fin BB := 0 + E57
  let E59 : Fin BB := E0 * E28
  let E60 : Fin BB := 0 + E59
  let E61 : Fin BB := E0 * E30
  let E62 : Fin BB := 0 + E61
  let E63 : Fin BB := E0 * E32
  let E64 : Fin BB := 0 + E63
  let E65 : Fin BB := E0 * E34
  let E66 : Fin BB := 0 + E65
  let E67 : Fin BB := E0 * E36
  let E68 : Fin BB := 0 + E67
  let E69 : Fin BB := E1 * E8
  let E70 : Fin BB := E40 + E69
  let E71 : Fin BB := E1 * E9
  let E72 : Fin BB := E42 + E71
  let E73 : Fin BB := E1 * E10
  let E74 : Fin BB := E44 + E73
  let E75 : Fin BB := E1 * E11
  let E76 : Fin BB := E46 + E75
  let E77 : Fin BB := E1 * E12
  let E78 : Fin BB := E48 + E77
  let E79 : Fin BB := E1 * E13
  let E80 : Fin BB := E50 + E79
  let E81 : Fin BB := E1 * E14
  let E82 : Fin BB := E52 + E81
  let E83 : Fin BB := E1 * E15
  let E84 : Fin BB := E54 + E83
  let E85 : Fin BB := E1 * E22
  let E86 : Fin BB := E56 + E85
  let E87 : Fin BB := E1 * E24
  let E88 : Fin BB := E58 + E87
  let E89 : Fin BB := E1 * E26
  let E90 : Fin BB := E60 + E89
  let E91 : Fin BB := E1 * E28
  let E92 : Fin BB := E62 + E91
  let E93 : Fin BB := E1 * E30
  let E94 : Fin BB := E64 + E93
  let E95 : Fin BB := E1 * E32
  let E96 : Fin BB := E66 + E95
  let E97 : Fin BB := E1 * E34
  let E98 : Fin BB := E68 + E97
  let E99 : Fin BB := E2 * E8
  let E100 : Fin BB := E72 + E99
  let E101 : Fin BB := E2 * E9
  let E102 : Fin BB := E74 + E101
  let E103 : Fin BB := E2 * E10
  let E104 : Fin BB := E76 + E103
  let E105 : Fin BB := E2 * E11
  let E106 : Fin BB := E78 + E105
  let E107 : Fin BB := E2 * E12
  let E108 : Fin BB := E80 + E107
  let E109 : Fin BB := E2 * E13
  let E110 : Fin BB := E82 + E109
  let E111 : Fin BB := E2 * E14
  let E112 : Fin BB := E84 + E111
  let E113 : Fin BB := E2 * E15
  let E114 : Fin BB := E86 + E113
  let E115 : Fin BB := E2 * E22
  let E116 : Fin BB := E88 + E115
  let E117 : Fin BB := E2 * E24
  let E118 : Fin BB := E90 + E117
  let E119 : Fin BB := E2 * E26
  let E120 : Fin BB := E92 + E119
  let E121 : Fin BB := E2 * E28
  let E122 : Fin BB := E94 + E121
  let E123 : Fin BB := E2 * E30
  let E124 : Fin BB := E96 + E123
  let E125 : Fin BB := E2 * E32
  let E126 : Fin BB := E98 + E125
  let E127 : Fin BB := E3 * E8
  let E128 : Fin BB := E102 + E127
  let E129 : Fin BB := E3 * E9
  let E130 : Fin BB := E104 + E129
  let E131 : Fin BB := E3 * E10
  let E132 : Fin BB := E106 + E131
  let E133 : Fin BB := E3 * E11
  let E134 : Fin BB := E108 + E133
  let E135 : Fin BB := E3 * E12
  let E136 : Fin BB := E110 + E135
  let E137 : Fin BB := E3 * E13
  let E138 : Fin BB := E112 + E137
  let E139 : Fin BB := E3 * E14
  let E140 : Fin BB := E114 + E139
  let E141 : Fin BB := E3 * E15
  let E142 : Fin BB := E116 + E141
  let E143 : Fin BB := E3 * E22
  let E144 : Fin BB := E118 + E143
  let E145 : Fin BB := E3 * E24
  let E146 : Fin BB := E120 + E145
  let E147 : Fin BB := E3 * E26
  let E148 : Fin BB := E122 + E147
  let E149 : Fin BB := E3 * E28
  let E150 : Fin BB := E124 + E149
  let E151 : Fin BB := E3 * E30
  let E152 : Fin BB := E126 + E151
  let E153 : Fin BB := E4 * E8
  let E154 : Fin BB := E130 + E153
  let E155 : Fin BB := E4 * E9
  let E156 : Fin BB := E132 + E155
  let E157 : Fin BB := E4 * E10
  let E158 : Fin BB := E134 + E157
  let E159 : Fin BB := E4 * E11
  let E160 : Fin BB := E136 + E159
  let E161 : Fin BB := E4 * E12
  let E162 : Fin BB := E138 + E161
  let E163 : Fin BB := E4 * E13
  let E164 : Fin BB := E140 + E163
  let E165 : Fin BB := E4 * E14
  let E166 : Fin BB := E142 + E165
  let E167 : Fin BB := E4 * E15
  let E168 : Fin BB := E144 + E167
  let E169 : Fin BB := E4 * E22
  let E170 : Fin BB := E146 + E169
  let E171 : Fin BB := E4 * E24
  let E172 : Fin BB := E148 + E171
  let E173 : Fin BB := E4 * E26
  let E174 : Fin BB := E150 + E173
  let E175 : Fin BB := E4 * E28
  let E176 : Fin BB := E152 + E175
  let E177 : Fin BB := E5 * E8
  let E178 : Fin BB := E156 + E177
  let E179 : Fin BB := E5 * E9
  let E180 : Fin BB := E158 + E179
  let E181 : Fin BB := E5 * E10
  let E182 : Fin BB := E160 + E181
  let E183 : Fin BB := E5 * E11
  let E184 : Fin BB := E162 + E183
  let E185 : Fin BB := E5 * E12
  let E186 : Fin BB := E164 + E185
  let E187 : Fin BB := E5 * E13
  let E188 : Fin BB := E166 + E187
  let E189 : Fin BB := E5 * E14
  let E190 : Fin BB := E168 + E189
  let E191 : Fin BB := E5 * E15
  let E192 : Fin BB := E170 + E191
  let E193 : Fin BB := E5 * E22
  let E194 : Fin BB := E172 + E193
  let E195 : Fin BB := E5 * E24
  let E196 : Fin BB := E174 + E195
  let E197 : Fin BB := E5 * E26
  let E198 : Fin BB := E176 + E197
  let E199 : Fin BB := E6 * E8
  let E200 : Fin BB := E180 + E199
  let E201 : Fin BB := E6 * E9
  let E202 : Fin BB := E182 + E201
  let E203 : Fin BB := E6 * E10
  let E204 : Fin BB := E184 + E203
  let E205 : Fin BB := E6 * E11
  let E206 : Fin BB := E186 + E205
  let E207 : Fin BB := E6 * E12
  let E208 : Fin BB := E188 + E207
  let E209 : Fin BB := E6 * E13
  let E210 : Fin BB := E190 + E209
  let E211 : Fin BB := E6 * E14
  let E212 : Fin BB := E192 + E211
  let E213 : Fin BB := E6 * E15
  let E214 : Fin BB := E194 + E213
  let E215 : Fin BB := E6 * E22
  let E216 : Fin BB := E196 + E215
  let E217 : Fin BB := E6 * E24
  let E218 : Fin BB := E198 + E217
  let E219 : Fin BB := E7 * E8
  let E220 : Fin BB := E202 + E219
  let E221 : Fin BB := E7 * E9
  let E222 : Fin BB := E204 + E221
  let E223 : Fin BB := E7 * E10
  let E224 : Fin BB := E206 + E223
  let E225 : Fin BB := E7 * E11
  let E226 : Fin BB := E208 + E225
  let E227 : Fin BB := E7 * E12
  let E228 : Fin BB := E210 + E227
  let E229 : Fin BB := E7 * E13
  let E230 : Fin BB := E212 + E229
  let E231 : Fin BB := E7 * E14
  let E232 : Fin BB := E214 + E231
  let E233 : Fin BB := E7 * E15
  let E234 : Fin BB := E216 + E233
  let E235 : Fin BB := E7 * E22
  let E236 : Fin BB := E218 + E235
  let E237 : Fin BB := E21 * E8
  let E238 : Fin BB := E222 + E237
  let E239 : Fin BB := E21 * E9
  let E240 : Fin BB := E224 + E239
  let E241 : Fin BB := E21 * E10
  let E242 : Fin BB := E226 + E241
  let E243 : Fin BB := E21 * E11
  let E244 : Fin BB := E228 + E243
  let E245 : Fin BB := E21 * E12
  let E246 : Fin BB := E230 + E245
  let E247 : Fin BB := E21 * E13
  let E248 : Fin BB := E232 + E247
  let E249 : Fin BB := E21 * E14
  let E250 : Fin BB := E234 + E249
  let E251 : Fin BB := E21 * E15
  let E252 : Fin BB := E236 + E251
  let E253 : Fin BB := E23 * E8
  let E254 : Fin BB := E240 + E253
  let E255 : Fin BB := E23 * E9
  let E256 : Fin BB := E242 + E255
  let E257 : Fin BB := E23 * E10
  let E258 : Fin BB := E244 + E257
  let E259 : Fin BB := E23 * E11
  let E260 : Fin BB := E246 + E259
  let E261 : Fin BB := E23 * E12
  let E262 : Fin BB := E248 + E261
  let E263 : Fin BB := E23 * E13
  let E264 : Fin BB := E250 + E263
  let E265 : Fin BB := E23 * E14
  let E266 : Fin BB := E252 + E265
  let E267 : Fin BB := E25 * E8
  let E268 : Fin BB := E256 + E267
  let E269 : Fin BB := E25 * E9
  let E270 : Fin BB := E258 + E269
  let E271 : Fin BB := E25 * E10
  let E272 : Fin BB := E260 + E271
  let E273 : Fin BB := E25 * E11
  let E274 : Fin BB := E262 + E273
  let E275 : Fin BB := E25 * E12
  let E276 : Fin BB := E264 + E275
  let E277 : Fin BB := E25 * E13
  let E278 : Fin BB := E266 + E277
  let E279 : Fin BB := E27 * E8
  let E280 : Fin BB := E270 + E279
  let E281 : Fin BB := E27 * E9
  let E282 : Fin BB := E272 + E281
  let E283 : Fin BB := E27 * E10
  let E284 : Fin BB := E274 + E283
  let E285 : Fin BB := E27 * E11
  let E286 : Fin BB := E276 + E285
  let E287 : Fin BB := E27 * E12
  let E288 : Fin BB := E278 + E287
  let E289 : Fin BB := E29 * E8
  let E290 : Fin BB := E282 + E289
  let E291 : Fin BB := E29 * E9
  let E292 : Fin BB := E284 + E291
  let E293 : Fin BB := E29 * E10
  let E294 : Fin BB := E286 + E293
  let E295 : Fin BB := E29 * E11
  let E296 : Fin BB := E288 + E295
  let E297 : Fin BB := E31 * E8
  let E298 : Fin BB := E292 + E297
  let E299 : Fin BB := E31 * E9
  let E300 : Fin BB := E294 + E299
  let E301 : Fin BB := E31 * E10
  let E302 : Fin BB := E296 + E301
  let E303 : Fin BB := E33 * E8
  let E304 : Fin BB := E300 + E303
  let E305 : Fin BB := E33 * E9
  let E306 : Fin BB := E302 + E305
  let E307 : Fin BB := E35 * E8
  let E308 : Fin BB := E306 + E307
  let E309 : Fin BB := cols.carry[0] * 256
  let E310 : Fin BB := E38 - E309
  let E311 : Fin BB := cols.product[0] - E310
  let E312 : Fin BB := is_real * E311
  let E313 : Fin BB := E70 + cols.carry[0]
  let E314 : Fin BB := cols.carry[1] * 256
  let E315 : Fin BB := E313 - E314
  let E316 : Fin BB := cols.product[1] - E315
  let E317 : Fin BB := is_real * E316
  let E318 : Fin BB := E100 + cols.carry[1]
  let E319 : Fin BB := cols.carry[2] * 256
  let E320 : Fin BB := E318 - E319
  let E321 : Fin BB := cols.product[2] - E320
  let E322 : Fin BB := is_real * E321
  let E323 : Fin BB := E128 + cols.carry[2]
  let E324 : Fin BB := cols.carry[3] * 256
  let E325 : Fin BB := E323 - E324
  let E326 : Fin BB := cols.product[3] - E325
  let E327 : Fin BB := is_real * E326
  let E328 : Fin BB := E154 + cols.carry[3]
  let E329 : Fin BB := cols.carry[4] * 256
  let E330 : Fin BB := E328 - E329
  let E331 : Fin BB := cols.product[4] - E330
  let E332 : Fin BB := is_real * E331
  let E333 : Fin BB := E178 + cols.carry[4]
  let E334 : Fin BB := cols.carry[5] * 256
  let E335 : Fin BB := E333 - E334
  let E336 : Fin BB := cols.product[5] - E335
  let E337 : Fin BB := is_real * E336
  let E338 : Fin BB := E200 + cols.carry[5]
  let E339 : Fin BB := cols.carry[6] * 256
  let E340 : Fin BB := E338 - E339
  let E341 : Fin BB := cols.product[6] - E340
  let E342 : Fin BB := is_real * E341
  let E343 : Fin BB := E220 + cols.carry[6]
  let E344 : Fin BB := cols.carry[7] * 256
  let E345 : Fin BB := E343 - E344
  let E346 : Fin BB := cols.product[7] - E345
  let E347 : Fin BB := is_real * E346
  let E348 : Fin BB := E238 + cols.carry[7]
  let E349 : Fin BB := cols.carry[8] * 256
  let E350 : Fin BB := E348 - E349
  let E351 : Fin BB := cols.product[8] - E350
  let E352 : Fin BB := is_real * E351
  let E353 : Fin BB := E254 + cols.carry[8]
  let E354 : Fin BB := cols.carry[9] * 256
  let E355 : Fin BB := E353 - E354
  let E356 : Fin BB := cols.product[9] - E355
  let E357 : Fin BB := is_real * E356
  let E358 : Fin BB := E268 + cols.carry[9]
  let E359 : Fin BB := cols.carry[10] * 256
  let E360 : Fin BB := E358 - E359
  let E361 : Fin BB := cols.product[10] - E360
  let E362 : Fin BB := is_real * E361
  let E363 : Fin BB := E280 + cols.carry[10]
  let E364 : Fin BB := cols.carry[11] * 256
  let E365 : Fin BB := E363 - E364
  let E366 : Fin BB := cols.product[11] - E365
  let E367 : Fin BB := is_real * E366
  let E368 : Fin BB := E290 + cols.carry[11]
  let E369 : Fin BB := cols.carry[12] * 256
  let E370 : Fin BB := E368 - E369
  let E371 : Fin BB := cols.product[12] - E370
  let E372 : Fin BB := is_real * E371
  let E373 : Fin BB := E298 + cols.carry[12]
  let E374 : Fin BB := cols.carry[13] * 256
  let E375 : Fin BB := E373 - E374
  let E376 : Fin BB := cols.product[13] - E375
  let E377 : Fin BB := is_real * E376
  let E378 : Fin BB := E304 + cols.carry[13]
  let E379 : Fin BB := cols.carry[14] * 256
  let E380 : Fin BB := E378 - E379
  let E381 : Fin BB := cols.product[14] - E380
  let E382 : Fin BB := is_real * E381
  let E383 : Fin BB := E308 + cols.carry[14]
  let E384 : Fin BB := cols.carry[15] * 256
  let E385 : Fin BB := E383 - E384
  let E386 : Fin BB := cols.product[15] - E385
  let E387 : Fin BB := is_real * E386
  let E388 : Fin BB := is_mulh + is_mulhu
  let E389 : Fin BB := E388 + is_mulhsu
  let E390 : Fin BB := cols.product[1] * 256
  let E391 : Fin BB := cols.product[0] + E390
  let E392 : Fin BB := E391 - a_word[0]
  let E393 : Fin BB := is_mulw * E392
  let E394 : Fin BB := cols.product[1] * 256
  let E395 : Fin BB := cols.product[0] + E394
  let E396 : Fin BB := E395 - a_word[0]
  let E397 : Fin BB := is_mul * E396
  let E398 : Fin BB := cols.product[9] * 256
  let E399 : Fin BB := cols.product[8] + E398
  let E400 : Fin BB := E399 - a_word[0]
  let E401 : Fin BB := E389 * E400
  let E402 : Fin BB := cols.product[3] * 256
  let E403 : Fin BB := cols.product[2] + E402
  let E404 : Fin BB := E403 - a_word[1]
  let E405 : Fin BB := is_mulw * E404
  let E406 : Fin BB := cols.product[3] * 256
  let E407 : Fin BB := cols.product[2] + E406
  let E408 : Fin BB := E407 - a_word[1]
  let E409 : Fin BB := is_mul * E408
  let E410 : Fin BB := cols.product[11] * 256
  let E411 : Fin BB := cols.product[10] + E410
  let E412 : Fin BB := E411 - a_word[1]
  let E413 : Fin BB := E389 * E412
  let E414 : Fin BB := cols.product_msb.msb * 65535
  let E415 : Fin BB := E414 - a_word[2]
  let E416 : Fin BB := is_mulw * E415
  let E417 : Fin BB := cols.product[5] * 256
  let E418 : Fin BB := cols.product[4] + E417
  let E419 : Fin BB := E418 - a_word[2]
  let E420 : Fin BB := is_mul * E419
  let E421 : Fin BB := cols.product[13] * 256
  let E422 : Fin BB := cols.product[12] + E421
  let E423 : Fin BB := E422 - a_word[2]
  let E424 : Fin BB := E389 * E423
  let E425 : Fin BB := cols.product_msb.msb * 65535
  let E426 : Fin BB := E425 - a_word[3]
  let E427 : Fin BB := is_mulw * E426
  let E428 : Fin BB := cols.product[7] * 256
  let E429 : Fin BB := cols.product[6] + E428
  let E430 : Fin BB := E429 - a_word[3]
  let E431 : Fin BB := is_mul * E430
  let E432 : Fin BB := cols.product[15] * 256
  let E433 : Fin BB := cols.product[14] + E432
  let E434 : Fin BB := E433 - a_word[3]
  let E435 : Fin BB := E389 * E434
  let E436 : Fin BB := is_mul + is_mulh
  let E437 : Fin BB := E436 + is_mulhu
  let E438 : Fin BB := E437 + is_mulhsu
  let E439 : Fin BB := E438 + is_mulw
  let E440 : Fin BB := cols.b_msb - 1
  let E441 : Fin BB := cols.b_msb * E440
  let E442 : Fin BB := cols.c_msb - 1
  let E443 : Fin BB := cols.c_msb * E442
  let E444 : Fin BB := cols.b_sign_extend - 1
  let E445 : Fin BB := cols.b_sign_extend * E444
  let E446 : Fin BB := cols.c_sign_extend - 1
  let E447 : Fin BB := cols.c_sign_extend * E446
  let E448 : Fin BB := is_mul - 1
  let E449 : Fin BB := is_mul * E448
  let E450 : Fin BB := is_mulh - 1
  let E451 : Fin BB := is_mulh * E450
  let E452 : Fin BB := is_mulhu - 1
  let E453 : Fin BB := is_mulhu * E452
  let E454 : Fin BB := is_mulhsu - 1
  let E455 : Fin BB := is_mulhsu * E454
  let E456 : Fin BB := is_mulw - 1
  let E457 : Fin BB := is_mulw * E456
  let E458 : Fin BB := E439 - 1
  let E459 : Fin BB := E439 * E458
  let E460 : Fin BB := is_real - 1
  let E461 : Fin BB := is_real * E460
  let E462 : Fin BB := cols.b_msb - 1
  let E463 : Fin BB := cols.b_sign_extend * E462
  let E464 : Fin BB := cols.c_msb - 1
  let E465 : Fin BB := cols.c_sign_extend * E464
  [
    (.send (.byte (ByteOpcode.ofNat 5) cols.b_msb E7 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 5) cols.c_msb E15 0) is_real),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E312),
    (.assertZero E317),
    (.assertZero E322),
    (.assertZero E327),
    (.assertZero E332),
    (.assertZero E337),
    (.assertZero E342),
    (.assertZero E347),
    (.assertZero E352),
    (.assertZero E357),
    (.assertZero E362),
    (.assertZero E367),
    (.assertZero E372),
    (.assertZero E377),
    (.assertZero E382),
    (.assertZero E387),
    (.assertZero E393),
    (.assertZero E397),
    (.assertZero E401),
    (.assertZero E405),
    (.assertZero E409),
    (.assertZero E413),
    (.assertZero E416),
    (.assertZero E420),
    (.assertZero E424),
    (.assertZero E427),
    (.assertZero E431),
    (.assertZero E435),
    (.assertZero E441),
    (.assertZero E443),
    (.assertZero E445),
    (.assertZero E447),
    (.assertZero E449),
    (.assertZero E451),
    (.assertZero E453),
    (.assertZero E455),
    (.assertZero E457),
    (.assertZero E459),
    (.assertZero E461),
    (.assertZero E463),
    (.assertZero E465),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[0] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[1] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[2] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[3] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[4] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[5] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[6] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[7] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[8] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[9] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[10] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[11] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[12] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[13] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[14] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) cols.carry[15] 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[0] cols.product[1]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[2] cols.product[3]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[4] cols.product[5]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[6] cols.product[7]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[8] cols.product[9]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[10] cols.product[11]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[12] cols.product[13]) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.product[14] cols.product[15]) is_real),
  ] ++ CS0 ++ CS1 ++ CS2

end constraints
