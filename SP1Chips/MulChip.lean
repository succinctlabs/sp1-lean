import SP1Foundations

namespace MulChip

def constraints (Main : Vector (Fin BB) 88) : SP1ConstraintList :=
  let ⟨⟨⟨[E0, E1, E2, E3, E4, E5, E6, E7]⟩, _⟩, CS0⟩ := U16toU8OperationSafe.constraints #v[Main[15], Main[16], Main[17], Main[18]] { low_bytes := #v[Main[68], Main[69], Main[70], Main[71]] } Main[82]
  let ⟨⟨⟨[E8, E9, E10, E11, E12, E13, E14, E15]⟩, _⟩, CS1⟩ := U16toU8OperationSafe.constraints #v[Main[25], Main[26], Main[27], Main[28]] { low_bytes := #v[Main[72], Main[73], Main[74], Main[75]] } Main[82]
  let E16 : Fin BB := Main[87] - 1
  let E17 : Fin BB := Main[87] * E16
  let E18 : Fin BB := Main[78] - 1
  let E19 : Fin BB := Main[78] * E18
  let E20 : Fin BB := 2 * Main[33]
  let E21 : Fin BB := Main[78] * 65536
  let E22 : Fin BB := E20 - E21
  let E23 : Fin BB := Main[84] + Main[86]
  let E24 : Fin BB := E23 * Main[76]
  let E25 : Fin BB := Main[79] - E24
  let E26 : Fin BB := Main[84] * Main[77]
  let E27 : Fin BB := Main[80] - E26
  let E28 : Fin BB := Main[79] * 255
  let E29 : Fin BB := Main[80] * 255
  let E30 : Fin BB := Main[79] * 255
  let E31 : Fin BB := Main[80] * 255
  let E32 : Fin BB := Main[79] * 255
  let E33 : Fin BB := Main[80] * 255
  let E34 : Fin BB := Main[79] * 255
  let E35 : Fin BB := Main[80] * 255
  let E36 : Fin BB := Main[79] * 255
  let E37 : Fin BB := Main[80] * 255
  let E38 : Fin BB := Main[79] * 255
  let E39 : Fin BB := Main[80] * 255
  let E40 : Fin BB := Main[79] * 255
  let E41 : Fin BB := Main[80] * 255
  let E42 : Fin BB := Main[79] * 255
  let E43 : Fin BB := Main[80] * 255
  let E44 : Fin BB := E0 * E8
  let E45 : Fin BB := 0 + E44
  let E46 : Fin BB := E0 * E9
  let E47 : Fin BB := 0 + E46
  let E48 : Fin BB := E0 * E10
  let E49 : Fin BB := 0 + E48
  let E50 : Fin BB := E0 * E11
  let E51 : Fin BB := 0 + E50
  let E52 : Fin BB := E0 * E12
  let E53 : Fin BB := 0 + E52
  let E54 : Fin BB := E0 * E13
  let E55 : Fin BB := 0 + E54
  let E56 : Fin BB := E0 * E14
  let E57 : Fin BB := 0 + E56
  let E58 : Fin BB := E0 * E15
  let E59 : Fin BB := 0 + E58
  let E60 : Fin BB := E0 * E29
  let E61 : Fin BB := 0 + E60
  let E62 : Fin BB := E0 * E31
  let E63 : Fin BB := 0 + E62
  let E64 : Fin BB := E0 * E33
  let E65 : Fin BB := 0 + E64
  let E66 : Fin BB := E0 * E35
  let E67 : Fin BB := 0 + E66
  let E68 : Fin BB := E0 * E37
  let E69 : Fin BB := 0 + E68
  let E70 : Fin BB := E0 * E39
  let E71 : Fin BB := 0 + E70
  let E72 : Fin BB := E0 * E41
  let E73 : Fin BB := 0 + E72
  let E74 : Fin BB := E0 * E43
  let E75 : Fin BB := 0 + E74
  let E76 : Fin BB := E1 * E8
  let E77 : Fin BB := E47 + E76
  let E78 : Fin BB := E1 * E9
  let E79 : Fin BB := E49 + E78
  let E80 : Fin BB := E1 * E10
  let E81 : Fin BB := E51 + E80
  let E82 : Fin BB := E1 * E11
  let E83 : Fin BB := E53 + E82
  let E84 : Fin BB := E1 * E12
  let E85 : Fin BB := E55 + E84
  let E86 : Fin BB := E1 * E13
  let E87 : Fin BB := E57 + E86
  let E88 : Fin BB := E1 * E14
  let E89 : Fin BB := E59 + E88
  let E90 : Fin BB := E1 * E15
  let E91 : Fin BB := E61 + E90
  let E92 : Fin BB := E1 * E29
  let E93 : Fin BB := E63 + E92
  let E94 : Fin BB := E1 * E31
  let E95 : Fin BB := E65 + E94
  let E96 : Fin BB := E1 * E33
  let E97 : Fin BB := E67 + E96
  let E98 : Fin BB := E1 * E35
  let E99 : Fin BB := E69 + E98
  let E100 : Fin BB := E1 * E37
  let E101 : Fin BB := E71 + E100
  let E102 : Fin BB := E1 * E39
  let E103 : Fin BB := E73 + E102
  let E104 : Fin BB := E1 * E41
  let E105 : Fin BB := E75 + E104
  let E106 : Fin BB := E2 * E8
  let E107 : Fin BB := E79 + E106
  let E108 : Fin BB := E2 * E9
  let E109 : Fin BB := E81 + E108
  let E110 : Fin BB := E2 * E10
  let E111 : Fin BB := E83 + E110
  let E112 : Fin BB := E2 * E11
  let E113 : Fin BB := E85 + E112
  let E114 : Fin BB := E2 * E12
  let E115 : Fin BB := E87 + E114
  let E116 : Fin BB := E2 * E13
  let E117 : Fin BB := E89 + E116
  let E118 : Fin BB := E2 * E14
  let E119 : Fin BB := E91 + E118
  let E120 : Fin BB := E2 * E15
  let E121 : Fin BB := E93 + E120
  let E122 : Fin BB := E2 * E29
  let E123 : Fin BB := E95 + E122
  let E124 : Fin BB := E2 * E31
  let E125 : Fin BB := E97 + E124
  let E126 : Fin BB := E2 * E33
  let E127 : Fin BB := E99 + E126
  let E128 : Fin BB := E2 * E35
  let E129 : Fin BB := E101 + E128
  let E130 : Fin BB := E2 * E37
  let E131 : Fin BB := E103 + E130
  let E132 : Fin BB := E2 * E39
  let E133 : Fin BB := E105 + E132
  let E134 : Fin BB := E3 * E8
  let E135 : Fin BB := E109 + E134
  let E136 : Fin BB := E3 * E9
  let E137 : Fin BB := E111 + E136
  let E138 : Fin BB := E3 * E10
  let E139 : Fin BB := E113 + E138
  let E140 : Fin BB := E3 * E11
  let E141 : Fin BB := E115 + E140
  let E142 : Fin BB := E3 * E12
  let E143 : Fin BB := E117 + E142
  let E144 : Fin BB := E3 * E13
  let E145 : Fin BB := E119 + E144
  let E146 : Fin BB := E3 * E14
  let E147 : Fin BB := E121 + E146
  let E148 : Fin BB := E3 * E15
  let E149 : Fin BB := E123 + E148
  let E150 : Fin BB := E3 * E29
  let E151 : Fin BB := E125 + E150
  let E152 : Fin BB := E3 * E31
  let E153 : Fin BB := E127 + E152
  let E154 : Fin BB := E3 * E33
  let E155 : Fin BB := E129 + E154
  let E156 : Fin BB := E3 * E35
  let E157 : Fin BB := E131 + E156
  let E158 : Fin BB := E3 * E37
  let E159 : Fin BB := E133 + E158
  let E160 : Fin BB := E4 * E8
  let E161 : Fin BB := E137 + E160
  let E162 : Fin BB := E4 * E9
  let E163 : Fin BB := E139 + E162
  let E164 : Fin BB := E4 * E10
  let E165 : Fin BB := E141 + E164
  let E166 : Fin BB := E4 * E11
  let E167 : Fin BB := E143 + E166
  let E168 : Fin BB := E4 * E12
  let E169 : Fin BB := E145 + E168
  let E170 : Fin BB := E4 * E13
  let E171 : Fin BB := E147 + E170
  let E172 : Fin BB := E4 * E14
  let E173 : Fin BB := E149 + E172
  let E174 : Fin BB := E4 * E15
  let E175 : Fin BB := E151 + E174
  let E176 : Fin BB := E4 * E29
  let E177 : Fin BB := E153 + E176
  let E178 : Fin BB := E4 * E31
  let E179 : Fin BB := E155 + E178
  let E180 : Fin BB := E4 * E33
  let E181 : Fin BB := E157 + E180
  let E182 : Fin BB := E4 * E35
  let E183 : Fin BB := E159 + E182
  let E184 : Fin BB := E5 * E8
  let E185 : Fin BB := E163 + E184
  let E186 : Fin BB := E5 * E9
  let E187 : Fin BB := E165 + E186
  let E188 : Fin BB := E5 * E10
  let E189 : Fin BB := E167 + E188
  let E190 : Fin BB := E5 * E11
  let E191 : Fin BB := E169 + E190
  let E192 : Fin BB := E5 * E12
  let E193 : Fin BB := E171 + E192
  let E194 : Fin BB := E5 * E13
  let E195 : Fin BB := E173 + E194
  let E196 : Fin BB := E5 * E14
  let E197 : Fin BB := E175 + E196
  let E198 : Fin BB := E5 * E15
  let E199 : Fin BB := E177 + E198
  let E200 : Fin BB := E5 * E29
  let E201 : Fin BB := E179 + E200
  let E202 : Fin BB := E5 * E31
  let E203 : Fin BB := E181 + E202
  let E204 : Fin BB := E5 * E33
  let E205 : Fin BB := E183 + E204
  let E206 : Fin BB := E6 * E8
  let E207 : Fin BB := E187 + E206
  let E208 : Fin BB := E6 * E9
  let E209 : Fin BB := E189 + E208
  let E210 : Fin BB := E6 * E10
  let E211 : Fin BB := E191 + E210
  let E212 : Fin BB := E6 * E11
  let E213 : Fin BB := E193 + E212
  let E214 : Fin BB := E6 * E12
  let E215 : Fin BB := E195 + E214
  let E216 : Fin BB := E6 * E13
  let E217 : Fin BB := E197 + E216
  let E218 : Fin BB := E6 * E14
  let E219 : Fin BB := E199 + E218
  let E220 : Fin BB := E6 * E15
  let E221 : Fin BB := E201 + E220
  let E222 : Fin BB := E6 * E29
  let E223 : Fin BB := E203 + E222
  let E224 : Fin BB := E6 * E31
  let E225 : Fin BB := E205 + E224
  let E226 : Fin BB := E7 * E8
  let E227 : Fin BB := E209 + E226
  let E228 : Fin BB := E7 * E9
  let E229 : Fin BB := E211 + E228
  let E230 : Fin BB := E7 * E10
  let E231 : Fin BB := E213 + E230
  let E232 : Fin BB := E7 * E11
  let E233 : Fin BB := E215 + E232
  let E234 : Fin BB := E7 * E12
  let E235 : Fin BB := E217 + E234
  let E236 : Fin BB := E7 * E13
  let E237 : Fin BB := E219 + E236
  let E238 : Fin BB := E7 * E14
  let E239 : Fin BB := E221 + E238
  let E240 : Fin BB := E7 * E15
  let E241 : Fin BB := E223 + E240
  let E242 : Fin BB := E7 * E29
  let E243 : Fin BB := E225 + E242
  let E244 : Fin BB := E28 * E8
  let E245 : Fin BB := E229 + E244
  let E246 : Fin BB := E28 * E9
  let E247 : Fin BB := E231 + E246
  let E248 : Fin BB := E28 * E10
  let E249 : Fin BB := E233 + E248
  let E250 : Fin BB := E28 * E11
  let E251 : Fin BB := E235 + E250
  let E252 : Fin BB := E28 * E12
  let E253 : Fin BB := E237 + E252
  let E254 : Fin BB := E28 * E13
  let E255 : Fin BB := E239 + E254
  let E256 : Fin BB := E28 * E14
  let E257 : Fin BB := E241 + E256
  let E258 : Fin BB := E28 * E15
  let E259 : Fin BB := E243 + E258
  let E260 : Fin BB := E30 * E8
  let E261 : Fin BB := E247 + E260
  let E262 : Fin BB := E30 * E9
  let E263 : Fin BB := E249 + E262
  let E264 : Fin BB := E30 * E10
  let E265 : Fin BB := E251 + E264
  let E266 : Fin BB := E30 * E11
  let E267 : Fin BB := E253 + E266
  let E268 : Fin BB := E30 * E12
  let E269 : Fin BB := E255 + E268
  let E270 : Fin BB := E30 * E13
  let E271 : Fin BB := E257 + E270
  let E272 : Fin BB := E30 * E14
  let E273 : Fin BB := E259 + E272
  let E274 : Fin BB := E32 * E8
  let E275 : Fin BB := E263 + E274
  let E276 : Fin BB := E32 * E9
  let E277 : Fin BB := E265 + E276
  let E278 : Fin BB := E32 * E10
  let E279 : Fin BB := E267 + E278
  let E280 : Fin BB := E32 * E11
  let E281 : Fin BB := E269 + E280
  let E282 : Fin BB := E32 * E12
  let E283 : Fin BB := E271 + E282
  let E284 : Fin BB := E32 * E13
  let E285 : Fin BB := E273 + E284
  let E286 : Fin BB := E34 * E8
  let E287 : Fin BB := E277 + E286
  let E288 : Fin BB := E34 * E9
  let E289 : Fin BB := E279 + E288
  let E290 : Fin BB := E34 * E10
  let E291 : Fin BB := E281 + E290
  let E292 : Fin BB := E34 * E11
  let E293 : Fin BB := E283 + E292
  let E294 : Fin BB := E34 * E12
  let E295 : Fin BB := E285 + E294
  let E296 : Fin BB := E36 * E8
  let E297 : Fin BB := E289 + E296
  let E298 : Fin BB := E36 * E9
  let E299 : Fin BB := E291 + E298
  let E300 : Fin BB := E36 * E10
  let E301 : Fin BB := E293 + E300
  let E302 : Fin BB := E36 * E11
  let E303 : Fin BB := E295 + E302
  let E304 : Fin BB := E38 * E8
  let E305 : Fin BB := E299 + E304
  let E306 : Fin BB := E38 * E9
  let E307 : Fin BB := E301 + E306
  let E308 : Fin BB := E38 * E10
  let E309 : Fin BB := E303 + E308
  let E310 : Fin BB := E40 * E8
  let E311 : Fin BB := E307 + E310
  let E312 : Fin BB := E40 * E9
  let E313 : Fin BB := E309 + E312
  let E314 : Fin BB := E42 * E8
  let E315 : Fin BB := E313 + E314
  let E316 : Fin BB := Main[36] * 256
  let E317 : Fin BB := E45 - E316
  let E318 : Fin BB := Main[52] - E317
  let E319 : Fin BB := Main[82] * E318
  let E320 : Fin BB := E77 + Main[36]
  let E321 : Fin BB := Main[37] * 256
  let E322 : Fin BB := E320 - E321
  let E323 : Fin BB := Main[53] - E322
  let E324 : Fin BB := Main[82] * E323
  let E325 : Fin BB := E107 + Main[37]
  let E326 : Fin BB := Main[38] * 256
  let E327 : Fin BB := E325 - E326
  let E328 : Fin BB := Main[54] - E327
  let E329 : Fin BB := Main[82] * E328
  let E330 : Fin BB := E135 + Main[38]
  let E331 : Fin BB := Main[39] * 256
  let E332 : Fin BB := E330 - E331
  let E333 : Fin BB := Main[55] - E332
  let E334 : Fin BB := Main[82] * E333
  let E335 : Fin BB := E161 + Main[39]
  let E336 : Fin BB := Main[40] * 256
  let E337 : Fin BB := E335 - E336
  let E338 : Fin BB := Main[56] - E337
  let E339 : Fin BB := Main[82] * E338
  let E340 : Fin BB := E185 + Main[40]
  let E341 : Fin BB := Main[41] * 256
  let E342 : Fin BB := E340 - E341
  let E343 : Fin BB := Main[57] - E342
  let E344 : Fin BB := Main[82] * E343
  let E345 : Fin BB := E207 + Main[41]
  let E346 : Fin BB := Main[42] * 256
  let E347 : Fin BB := E345 - E346
  let E348 : Fin BB := Main[58] - E347
  let E349 : Fin BB := Main[82] * E348
  let E350 : Fin BB := E227 + Main[42]
  let E351 : Fin BB := Main[43] * 256
  let E352 : Fin BB := E350 - E351
  let E353 : Fin BB := Main[59] - E352
  let E354 : Fin BB := Main[82] * E353
  let E355 : Fin BB := E245 + Main[43]
  let E356 : Fin BB := Main[44] * 256
  let E357 : Fin BB := E355 - E356
  let E358 : Fin BB := Main[60] - E357
  let E359 : Fin BB := Main[82] * E358
  let E360 : Fin BB := E261 + Main[44]
  let E361 : Fin BB := Main[45] * 256
  let E362 : Fin BB := E360 - E361
  let E363 : Fin BB := Main[61] - E362
  let E364 : Fin BB := Main[82] * E363
  let E365 : Fin BB := E275 + Main[45]
  let E366 : Fin BB := Main[46] * 256
  let E367 : Fin BB := E365 - E366
  let E368 : Fin BB := Main[62] - E367
  let E369 : Fin BB := Main[82] * E368
  let E370 : Fin BB := E287 + Main[46]
  let E371 : Fin BB := Main[47] * 256
  let E372 : Fin BB := E370 - E371
  let E373 : Fin BB := Main[63] - E372
  let E374 : Fin BB := Main[82] * E373
  let E375 : Fin BB := E297 + Main[47]
  let E376 : Fin BB := Main[48] * 256
  let E377 : Fin BB := E375 - E376
  let E378 : Fin BB := Main[64] - E377
  let E379 : Fin BB := Main[82] * E378
  let E380 : Fin BB := E305 + Main[48]
  let E381 : Fin BB := Main[49] * 256
  let E382 : Fin BB := E380 - E381
  let E383 : Fin BB := Main[65] - E382
  let E384 : Fin BB := Main[82] * E383
  let E385 : Fin BB := E311 + Main[49]
  let E386 : Fin BB := Main[50] * 256
  let E387 : Fin BB := E385 - E386
  let E388 : Fin BB := Main[66] - E387
  let E389 : Fin BB := Main[82] * E388
  let E390 : Fin BB := E315 + Main[50]
  let E391 : Fin BB := Main[51] * 256
  let E392 : Fin BB := E390 - E391
  let E393 : Fin BB := Main[67] - E392
  let E394 : Fin BB := Main[82] * E393
  let E395 : Fin BB := Main[84] + Main[85]
  let E396 : Fin BB := E395 + Main[86]
  let E397 : Fin BB := Main[53] * 256
  let E398 : Fin BB := Main[52] + E397
  let E399 : Fin BB := E398 - Main[32]
  let E400 : Fin BB := Main[87] * E399
  let E401 : Fin BB := Main[53] * 256
  let E402 : Fin BB := Main[52] + E401
  let E403 : Fin BB := E402 - Main[32]
  let E404 : Fin BB := Main[83] * E403
  let E405 : Fin BB := Main[61] * 256
  let E406 : Fin BB := Main[60] + E405
  let E407 : Fin BB := E406 - Main[32]
  let E408 : Fin BB := E396 * E407
  let E409 : Fin BB := Main[55] * 256
  let E410 : Fin BB := Main[54] + E409
  let E411 : Fin BB := E410 - Main[33]
  let E412 : Fin BB := Main[87] * E411
  let E413 : Fin BB := Main[55] * 256
  let E414 : Fin BB := Main[54] + E413
  let E415 : Fin BB := E414 - Main[33]
  let E416 : Fin BB := Main[83] * E415
  let E417 : Fin BB := Main[63] * 256
  let E418 : Fin BB := Main[62] + E417
  let E419 : Fin BB := E418 - Main[33]
  let E420 : Fin BB := E396 * E419
  let E421 : Fin BB := Main[78] * 65535
  let E422 : Fin BB := E421 - Main[34]
  let E423 : Fin BB := Main[87] * E422
  let E424 : Fin BB := Main[57] * 256
  let E425 : Fin BB := Main[56] + E424
  let E426 : Fin BB := E425 - Main[34]
  let E427 : Fin BB := Main[83] * E426
  let E428 : Fin BB := Main[65] * 256
  let E429 : Fin BB := Main[64] + E428
  let E430 : Fin BB := E429 - Main[34]
  let E431 : Fin BB := E396 * E430
  let E432 : Fin BB := Main[78] * 65535
  let E433 : Fin BB := E432 - Main[35]
  let E434 : Fin BB := Main[87] * E433
  let E435 : Fin BB := Main[59] * 256
  let E436 : Fin BB := Main[58] + E435
  let E437 : Fin BB := E436 - Main[35]
  let E438 : Fin BB := Main[83] * E437
  let E439 : Fin BB := Main[67] * 256
  let E440 : Fin BB := Main[66] + E439
  let E441 : Fin BB := E440 - Main[35]
  let E442 : Fin BB := E396 * E441
  let E443 : Fin BB := Main[83] + Main[84]
  let E444 : Fin BB := E443 + Main[85]
  let E445 : Fin BB := E444 + Main[86]
  let E446 : Fin BB := E445 + Main[87]
  let E447 : Fin BB := Main[76] - 1
  let E448 : Fin BB := Main[76] * E447
  let E449 : Fin BB := Main[77] - 1
  let E450 : Fin BB := Main[77] * E449
  let E451 : Fin BB := Main[79] - 1
  let E452 : Fin BB := Main[79] * E451
  let E453 : Fin BB := Main[80] - 1
  let E454 : Fin BB := Main[80] * E453
  let E455 : Fin BB := Main[83] - 1
  let E456 : Fin BB := Main[83] * E455
  let E457 : Fin BB := Main[84] - 1
  let E458 : Fin BB := Main[84] * E457
  let E459 : Fin BB := Main[85] - 1
  let E460 : Fin BB := Main[85] * E459
  let E461 : Fin BB := Main[86] - 1
  let E462 : Fin BB := Main[86] * E461
  let E463 : Fin BB := Main[87] - 1
  let E464 : Fin BB := Main[87] * E463
  let E465 : Fin BB := E446 - 1
  let E466 : Fin BB := E446 * E465
  let E467 : Fin BB := Main[82] - 1
  let E468 : Fin BB := Main[82] * E467
  let E469 : Fin BB := Main[76] - 1
  let E470 : Fin BB := Main[79] * E469
  let E471 : Fin BB := Main[77] - 1
  let E472 : Fin BB := Main[80] * E471
  let E473 : Fin BB := Main[83] + Main[84]
  let E474 : Fin BB := E473 + Main[85]
  let E475 : Fin BB := E474 + Main[86]
  let E476 : Fin BB := E475 + Main[87]
  let E477 : Fin BB := Main[82] - E476
  let E478 : Fin BB := Main[83] - 1
  let E479 : Fin BB := Main[83] * E478
  let E480 : Fin BB := Main[84] - 1
  let E481 : Fin BB := Main[84] * E480
  let E482 : Fin BB := Main[85] - 1
  let E483 : Fin BB := Main[85] * E482
  let E484 : Fin BB := Main[87] - 1
  let E485 : Fin BB := Main[87] * E484
  let E486 : Fin BB := Main[86] - 1
  let E487 : Fin BB := Main[86] * E486
  let E488 : Fin BB := Main[82] - 1
  let E489 : Fin BB := Main[82] * E488
  let E490 : Fin BB := Main[83] * 11
  let E491 : Fin BB := Main[84] * 12
  let E492 : Fin BB := E490 + E491
  let E493 : Fin BB := Main[85] * 13
  let E494 : Fin BB := E492 + E493
  let E495 : Fin BB := Main[86] * 14
  let E496 : Fin BB := E494 + E495
  let E497 : Fin BB := Main[87] * 47
  let E498 : Fin BB := E496 + E497
  let E499 : Fin BB := Main[3] + 4
  let E500 : Fin BB := Main[1] * 65536
  let E501 : Fin BB := Main[2] + E500
  let E502 : Fin BB := Main[82] - 1
  let E503 : Fin BB := Main[82] * E502
  let E504 : Fin BB := E501 + 8
  let E505 : Fin BB := Main[2] - 1
  let E506 : Fin BB := E505 * 1761607681
  let E507 : Fin BB := Main[1] * 65536
  let E508 : Fin BB := Main[2] + E507
  let CS2 : SP1ConstraintList := ALUTypeReader.constraints Main[0] E508 #v[Main[3], Main[4], Main[5]] E498 #v[Main[32], Main[33], Main[34], Main[35]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := #v[Main[21], Main[22], Main[23], Main[24]], op_c_memory := { prev_value := #v[Main[25], Main[26], Main[27], Main[28]], access_timestamp := { prev_low := Main[29], diff_low_limb := Main[30] } }, imm_c := Main[31] } Main[82]
  [
    (.send (.byte (ByteOpcode.ofNat 5) Main[76] E7 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 5) Main[77] E15 0) Main[82]),
    (.assertZero E17),
    (.assertZero E19),
    (.send (.byte (ByteOpcode.ofNat 7) E22 16 0) Main[87]),
    (.assertZero E25),
    (.assertZero E27),
    (.assertZero E319),
    (.assertZero E324),
    (.assertZero E329),
    (.assertZero E334),
    (.assertZero E339),
    (.assertZero E344),
    (.assertZero E349),
    (.assertZero E354),
    (.assertZero E359),
    (.assertZero E364),
    (.assertZero E369),
    (.assertZero E374),
    (.assertZero E379),
    (.assertZero E384),
    (.assertZero E389),
    (.assertZero E394),
    (.assertZero E400),
    (.assertZero E404),
    (.assertZero E408),
    (.assertZero E412),
    (.assertZero E416),
    (.assertZero E420),
    (.assertZero E423),
    (.assertZero E427),
    (.assertZero E431),
    (.assertZero E434),
    (.assertZero E438),
    (.assertZero E442),
    (.assertZero E448),
    (.assertZero E450),
    (.assertZero E452),
    (.assertZero E454),
    (.assertZero E456),
    (.assertZero E458),
    (.assertZero E460),
    (.assertZero E462),
    (.assertZero E464),
    (.assertZero E466),
    (.assertZero E468),
    (.assertZero E470),
    (.assertZero E472),
    (.send (.byte (ByteOpcode.ofNat 7) Main[36] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[37] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[38] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[39] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[40] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[41] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[42] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[43] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[44] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[45] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[46] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[47] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[48] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[49] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[50] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) Main[51] 16 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[52] Main[53]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[54] Main[55]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[56] Main[57]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[58] Main[59]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[60] Main[61]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[62] Main[63]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[64] Main[65]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[66] Main[67]) Main[82]),
    (.assertZero E477),
    (.assertZero E479),
    (.assertZero E481),
    (.assertZero E483),
    (.assertZero E485),
    (.assertZero E487),
    (.assertZero E489),
    (.assertZero E503),
    (.receive (.state Main[0] E501 Main[3] Main[4] Main[5]) Main[82]),
    (.send (.state Main[0] E504 E499 Main[4] Main[5]) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 7) E506 13 0) Main[82]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[82]),
  ] ++ CS0 ++ CS1 ++ CS2

end MulChip
