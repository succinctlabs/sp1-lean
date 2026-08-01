import SP1Clean.FormalModel.Contracts.DivRemColumns
import Clean.Circuit.Basic

/-! # `DivRemChip` — the chip's own assertZero constraints (the `[E13…E367, op_a_0]` list).

The `DivRemChip.Columns.asserts` own-constraint tail, as a pure `Var Columns → List (Expression …)`
function. Kept pure (no `Circuit` monad) so the ~360-step `let E…` chain elaborates without the
per-operation offset whnf of a `do`-block; `Defs.main` emits it with one `assertZeros`. Numerals are
pinned to `Expression` by per-binding ascriptions. -/

namespace SP1Clean.DivRemChip

variable {p : ℕ} [Fact p.Prime]

set_option linter.unusedVariables false in
-- Ladder-measured 2026-07-27 (lowering the real ceiling, re-elaborating each rung): 40000 FAILS
-- (`isDefEq` / `synthesize pending MVars` timeout mid-chain), 100000 ok. The 368-`let` chain's
-- floor is genuinely > 40000; 500000 keeps ~5x margin. Was 8000000. The twelve membership
-- theorems below needed no override at all (all pass under 20000) and carry none.
set_option maxHeartbeats 500000 in
/-- SP1's `Columns.eval` own-constraint list (the `[E13…E367, adapter.op_a_0]` tail).

**Generic over the carrier `R`** so the one chain serves both levels: the chip/`DivRemCore` `main`s
emit it at `R = Expression (ZMod p)` (the constraint expressions), while the `DivRemCore.CoreSpec`
raw bundle (`OwnAssertsHold`) states the same list at `R = ZMod p` (the evaluated row). The
`DivRemCore.ownAsserts_map_eval` transport lemma connects the two instantiations. -/
def ownAsserts {R : Type} [Add R] [Sub R] [Mul R] [Zero R] [One R]
    [OfNat R 65535] [OfNat R 65536] (cols : Columns R) : List R :=
  let E0 : R := cols.is_divw + cols.is_remw
  let E1 : R := E0 + cols.is_divuw
  let E2 : R := E1 + cols.is_remuw
  let E3 : R := cols.is_divu + cols.is_remu
  let E4 : R := E3 + cols.is_div
  let E5 : R := E4 + cols.is_rem
  let E6 : R := cols.is_divw + cols.is_remw
  let E7 : R := cols.is_divuw + cols.is_remuw
  let E8 : R := cols.is_div + cols.is_rem
  let E9 : R := E8 + cols.is_divw
  let E10 : R := E9 + cols.is_remw
  let E11 : R := (1 : R) - E2
  let E12 : R := cols.is_real * E11
  let E13 : R := cols.is_real_not_word - E12
  let E14 : R := cols.b_msb.msb * E10
  let E15 : R := E14 - cols.b_neg
  let E16 : R := cols.rem_msb.msb * E10
  let E17 : R := E16 - cols.rem_neg
  let E18 : R := cols.c_msb.msb * E10
  let E19 : R := E18 - cols.c_neg
  let E20 : R := cols.adapter.op_b_memory.prev_value[0] - cols.b[0]
  let E21 : R := cols.adapter.op_c_memory.prev_value[0] - cols.c[0]
  let E22 : R := cols.adapter.op_b_memory.prev_value[1] - cols.b[1]
  let E23 : R := cols.adapter.op_c_memory.prev_value[1] - cols.c[1]
  let E24 : R := (1 : R) - E2
  let E25 : R := cols.adapter.op_b_memory.prev_value[2] * E24
  let E26 : R := cols.b_neg * E2
  let E27 : R := E26 * 65535
  let E28 : R := E25 + E27
  let E29 : R := cols.b[2] - E28
  let E30 : R := (1 : R) - E2
  let E31 : R := cols.adapter.op_c_memory.prev_value[2] * E30
  let E32 : R := cols.c_neg * E2
  let E33 : R := E32 * 65535
  let E34 : R := E31 + E33
  let E35 : R := cols.c[2] - E34
  let E36 : R := (1 : R) - E2
  let E37 : R := cols.adapter.op_b_memory.prev_value[3] * E36
  let E38 : R := cols.b_neg * E2
  let E39 : R := E38 * 65535
  let E40 : R := E37 + E39
  let E41 : R := cols.b[3] - E40
  let E42 : R := (1 : R) - E2
  let E43 : R := cols.adapter.op_c_memory.prev_value[3] * E42
  let E44 : R := cols.c_neg * E2
  let E45 : R := E44 * 65535
  let E46 : R := E43 + E45
  let E47 : R := cols.c[3] - E46
  let E48 : R := cols.quotient_comp[0] - cols.quotient[0]
  let E49 : R := cols.quotient_comp[1] - cols.quotient[1]
  let E50 : R := cols.quotient_comp[2] - 0
  let E51 : R := E7 * E50
  let E52 : R := cols.quot_msb.msb * 65535
  let E53 : R := cols.quotient_comp[2] - E52
  let E54 : R := E6 * E53
  let E55 : R := cols.quot_msb.msb * 65535
  let E56 : R := cols.quotient[2] - E55
  let E57 : R := E2 * E56
  let E58 : R := cols.quotient_comp[2] - cols.quotient[2]
  let E59 : R := E5 * E58
  let E60 : R := cols.quotient_comp[3] - 0
  let E61 : R := E7 * E60
  let E62 : R := cols.quot_msb.msb * 65535
  let E63 : R := cols.quotient_comp[3] - E62
  let E64 : R := E6 * E63
  let E65 : R := cols.quot_msb.msb * 65535
  let E66 : R := cols.quotient[3] - E65
  let E67 : R := E2 * E66
  let E68 : R := cols.quotient_comp[3] - cols.quotient[3]
  let E69 : R := E5 * E68
  let E70 : R := cols.remainder_comp[0] - cols.remainder[0]
  let E71 : R := cols.remainder_comp[1] - cols.remainder[1]
  let E72 : R := cols.remainder_comp[2] - 0
  let E73 : R := E7 * E72
  let E74 : R := cols.rem_msb.msb * 65535
  let E75 : R := cols.remainder_comp[2] - E74
  let E76 : R := E6 * E75
  let E77 : R := cols.rem_msb.msb * 65535
  let E78 : R := cols.remainder[2] - E77
  let E79 : R := E2 * E78
  let E80 : R := cols.remainder_comp[2] - cols.remainder[2]
  let E81 : R := E5 * E80
  let E82 : R := cols.remainder_comp[3] - 0
  let E83 : R := E7 * E82
  let E84 : R := cols.rem_msb.msb * 65535
  let E85 : R := cols.remainder_comp[3] - E84
  let E86 : R := E6 * E85
  let E87 : R := cols.rem_msb.msb * 65535
  let E88 : R := cols.remainder[3] - E87
  let E89 : R := E2 * E88
  let E90 : R := cols.remainder_comp[3] - cols.remainder[3]
  let E91 : R := E5 * E90
  let E92 : R := cols.is_div + cols.is_rem
  let E93 : R := cols.is_divu + cols.is_remu
  let E94 : R := cols.is_overflow_b.is_diff_zero.result * cols.is_overflow_c.is_diff_zero.result
  let E95 : R := E94 * E10
  let E96 : R := cols.is_overflow - E95
  let E97 : R := (1 : R) - cols.is_overflow
  let E98 : R := cols.b_neg * E97
  let E99 : R := cols.b_neg_not_overflow - E98
  let E100 : R := (1 : R) - cols.b_neg
  let E101 : R := (1 : R) - cols.is_overflow
  let E102 : R := E100 * E101
  let E103 : R := cols.b_not_neg_not_overflow - E102
  let E104 : R := cols.quotient[0] - cols.b[0]
  let E105 : R := cols.is_overflow * E104
  let E106 : R := cols.remainder[0] - 0
  let E107 : R := cols.is_overflow * E106
  let E108 : R := cols.quotient[1] - cols.b[1]
  let E109 : R := cols.is_overflow * E108
  let E110 : R := cols.remainder[1] - 0
  let E111 : R := cols.is_overflow * E110
  let E112 : R := cols.quotient[2] - cols.b[2]
  let E113 : R := cols.is_overflow * E112
  let E114 : R := cols.remainder[2] - 0
  let E115 : R := cols.is_overflow * E114
  let E116 : R := cols.quotient[3] - cols.b[3]
  let E117 : R := cols.is_overflow * E116
  let E118 : R := cols.remainder[3] - 0
  let E119 : R := cols.is_overflow * E118
  let E120 : R := cols.rem_neg * 65535
  let E121 : R := cols.c_times_quotient[0] + cols.remainder_comp[0]
  let E122 : R := cols.carry[0] * 65536
  let E123 : R := E121 - E122
  let E124 : R := cols.c_times_quotient[1] + cols.remainder_comp[1]
  let E125 : R := cols.carry[1] * 65536
  let E126 : R := E124 - E125
  let E127 : R := E126 + cols.carry[0]
  let E128 : R := cols.c_times_quotient[2] + cols.remainder_comp[2]
  let E129 : R := cols.carry[2] * 65536
  let E130 : R := E128 - E129
  let E131 : R := E130 + cols.carry[1]
  let E132 : R := cols.c_times_quotient[3] + cols.remainder_comp[3]
  let E133 : R := cols.carry[3] * 65536
  let E134 : R := E132 - E133
  let E135 : R := E134 + cols.carry[2]
  let E136 : R := cols.c_times_quotient[4] + E120
  let E137 : R := cols.carry[4] * 65536
  let E138 : R := E136 - E137
  let E139 : R := E138 + cols.carry[3]
  let E140 : R := cols.c_times_quotient[5] + E120
  let E141 : R := cols.carry[5] * 65536
  let E142 : R := E140 - E141
  let E143 : R := E142 + cols.carry[4]
  let E144 : R := cols.c_times_quotient[6] + E120
  let E145 : R := cols.carry[6] * 65536
  let E146 : R := E144 - E145
  let E147 : R := E146 + cols.carry[5]
  let E148 : R := cols.c_times_quotient[7] + E120
  let E149 : R := cols.carry[7] * 65536
  let E150 : R := E148 - E149
  let E151 : R := E150 + cols.carry[6]
  let E152 : R := cols.is_overflow - 1
  let E153 : R := cols.b[0] - E123
  let E154 : R := E152 * E153
  let E155 : R := cols.is_overflow - 1
  let E156 : R := cols.b[1] - E127
  let E157 : R := E155 * E156
  let E158 : R := cols.is_overflow - 1
  let E159 : R := cols.b[2] - E131
  let E160 : R := E158 * E159
  let E161 : R := cols.is_overflow - 1
  let E162 : R := cols.b[3] - E135
  let E163 : R := E161 * E162
  let E164 : R := cols.is_overflow - 1
  let E165 : R := cols.b_neg * 65535
  let E166 : R := E165 - E139
  let E167 : R := E164 * E166
  let E168 : R := cols.is_overflow - 1
  let E169 : R := cols.b_neg * 65535
  let E170 : R := E169 - E143
  let E171 : R := E168 * E170
  let E172 : R := cols.is_overflow - 1
  let E173 : R := cols.b_neg * 65535
  let E174 : R := E173 - E147
  let E175 : R := E172 * E174
  let E176 : R := cols.is_overflow - 1
  let E177 : R := cols.b_neg * 65535
  let E178 : R := E177 - E151
  let E179 : R := E176 * E178
  let E180 : R := cols.is_divu + cols.is_div
  let E181 : R := E180 + cols.is_divw
  let E182 : R := E181 + cols.is_divuw
  let E183 : R := cols.quotient[0] - cols.a[0]
  let E184 : R := E182 * E183
  let E185 : R := cols.is_remu + cols.is_rem
  let E186 : R := E185 + cols.is_remw
  let E187 : R := E186 + cols.is_remuw
  let E188 : R := cols.remainder[0] - cols.a[0]
  let E189 : R := E187 * E188
  let E190 : R := cols.is_divu + cols.is_div
  let E191 : R := E190 + cols.is_divw
  let E192 : R := E191 + cols.is_divuw
  let E193 : R := cols.quotient[1] - cols.a[1]
  let E194 : R := E192 * E193
  let E195 : R := cols.is_remu + cols.is_rem
  let E196 : R := E195 + cols.is_remw
  let E197 : R := E196 + cols.is_remuw
  let E198 : R := cols.remainder[1] - cols.a[1]
  let E199 : R := E197 * E198
  let E200 : R := cols.is_divu + cols.is_div
  let E201 : R := E200 + cols.is_divw
  let E202 : R := E201 + cols.is_divuw
  let E203 : R := cols.quotient[2] - cols.a[2]
  let E204 : R := E202 * E203
  let E205 : R := cols.is_remu + cols.is_rem
  let E206 : R := E205 + cols.is_remw
  let E207 : R := E206 + cols.is_remuw
  let E208 : R := cols.remainder[2] - cols.a[2]
  let E209 : R := E207 * E208
  let E210 : R := cols.is_divu + cols.is_div
  let E211 : R := E210 + cols.is_divw
  let E212 : R := E211 + cols.is_divuw
  let E213 : R := cols.quotient[3] - cols.a[3]
  let E214 : R := E212 * E213
  let E215 : R := cols.is_remu + cols.is_rem
  let E216 : R := E215 + cols.is_remw
  let E217 : R := E216 + cols.is_remuw
  let E218 : R := cols.remainder[3] - cols.a[3]
  let E219 : R := E217 * E218
  let E220 : R := (0 : R) + cols.remainder[0]
  let E221 : R := E220 + cols.remainder[1]
  let E222 : R := E221 + cols.remainder[2]
  let E223 : R := E222 + cols.remainder[3]
  let E224 : R := cols.b_neg - 1
  let E225 : R := cols.rem_neg * E224
  let E226 : R := (1 : R) - cols.rem_neg
  let E227 : R := E226 * cols.b_neg
  let E228 : R := E223 * E227
  let E229 : R := cols.quotient[0] - 65535
  let E230 : R := cols.is_c_0.result * E229
  let E231 : R := cols.quotient[1] - 65535
  let E232 : R := cols.is_c_0.result * E231
  let E233 : R := cols.quotient[2] - 65535
  let E234 : R := cols.is_c_0.result * E233
  let E235 : R := cols.quotient[3] - 65535
  let E236 : R := cols.is_c_0.result * E235
  let E237 : R := cols.remainder_comp[0] - cols.b[0]
  let E238 : R := cols.is_c_0.result * E237
  let E239 : R := cols.remainder_comp[1] - cols.b[1]
  let E240 : R := cols.is_c_0.result * E239
  let E241 : R := cols.remainder_comp[2] - cols.b[2]
  let E242 : R := cols.is_c_0.result * E241
  let E243 : R := cols.remainder_comp[3] - cols.b[3]
  let E244 : R := cols.is_c_0.result * E243
  let E245 : R := cols.c_neg - 1
  let E246 : R := cols.c[0] - cols.abs_c[0]
  let E247 : R := E245 * E246
  let E248 : R := cols.rem_neg - 1
  let E249 : R := cols.remainder_comp[0] - cols.abs_remainder[0]
  let E250 : R := E248 * E249
  let E251 : R := cols.c_neg - 1
  let E252 : R := cols.c[1] - cols.abs_c[1]
  let E253 : R := E251 * E252
  let E254 : R := cols.rem_neg - 1
  let E255 : R := cols.remainder_comp[1] - cols.abs_remainder[1]
  let E256 : R := E254 * E255
  let E257 : R := cols.c_neg - 1
  let E258 : R := cols.c[2] - cols.abs_c[2]
  let E259 : R := E257 * E258
  let E260 : R := cols.rem_neg - 1
  let E261 : R := cols.remainder_comp[2] - cols.abs_remainder[2]
  let E262 : R := E260 * E261
  let E263 : R := cols.c_neg - 1
  let E264 : R := cols.c[3] - cols.abs_c[3]
  let E265 : R := E263 * E264
  let E266 : R := cols.rem_neg - 1
  let E267 : R := cols.remainder_comp[3] - cols.abs_remainder[3]
  let E268 : R := E266 * E267
  let E269 : R := (0 : R) - cols.c_neg_operation.value[0]
  let E270 : R := cols.abs_c_alu_event * E269
  let E271 : R := (0 : R) - cols.c_neg_operation.value[1]
  let E272 : R := cols.abs_c_alu_event * E271
  let E273 : R := (0 : R) - cols.c_neg_operation.value[2]
  let E274 : R := cols.abs_c_alu_event * E273
  let E275 : R := (0 : R) - cols.c_neg_operation.value[3]
  let E276 : R := cols.abs_c_alu_event * E275
  let E277 : R := (0 : R) - cols.rem_neg_operation.value[0]
  let E278 : R := cols.abs_rem_alu_event * E277
  let E279 : R := (0 : R) - cols.rem_neg_operation.value[1]
  let E280 : R := cols.abs_rem_alu_event * E279
  let E281 : R := (0 : R) - cols.rem_neg_operation.value[2]
  let E282 : R := cols.abs_rem_alu_event * E281
  let E283 : R := (0 : R) - cols.rem_neg_operation.value[3]
  let E284 : R := cols.abs_rem_alu_event * E283
  let E285 : R := cols.c_neg * cols.is_real
  let E286 : R := cols.abs_c_alu_event - E285
  let E287 : R := cols.rem_neg * cols.is_real
  let E288 : R := cols.abs_rem_alu_event - E287
  let E289 : R := cols.is_c_0.result * 1
  let E290 : R := (1 : R) - cols.is_c_0.result
  let E291 : R := E290 * cols.abs_c[0]
  let E292 : R := E289 + E291
  let E293 : R := (1 : R) - cols.is_c_0.result
  let E294 : R := E293 * cols.abs_c[1]
  let E295 : R := (1 : R) - cols.is_c_0.result
  let E296 : R := E295 * cols.abs_c[2]
  let E297 : R := (1 : R) - cols.is_c_0.result
  let E298 : R := E297 * cols.abs_c[3]
  let E299 : R := cols.max_abs_c_or_1[0] - E292
  let E300 : R := cols.max_abs_c_or_1[1] - E294
  let E301 : R := cols.max_abs_c_or_1[2] - E296
  let E302 : R := cols.max_abs_c_or_1[3] - E298
  let E303 : R := (1 : R) - cols.is_c_0.result
  let E304 : R := E303 * cols.is_real
  let E305 : R := E304 - cols.remainder_check_multiplicity
  let E306 : R := (1 : R) - cols.remainder_lt_operation.u16_compare_operation.bit
  let E307 : R := cols.remainder_check_multiplicity * E306
  let E308 : R := cols.carry[0] - 1
  let E309 : R := cols.carry[0] * E308
  let E310 : R := cols.carry[1] - 1
  let E311 : R := cols.carry[1] * E310
  let E312 : R := cols.carry[2] - 1
  let E313 : R := cols.carry[2] * E312
  let E314 : R := cols.carry[3] - 1
  let E315 : R := cols.carry[3] * E314
  let E316 : R := cols.carry[4] - 1
  let E317 : R := cols.carry[4] * E316
  let E318 : R := cols.carry[5] - 1
  let E319 : R := cols.carry[5] * E318
  let E320 : R := cols.carry[6] - 1
  let E321 : R := cols.carry[6] * E320
  let E322 : R := cols.carry[7] - 1
  let E323 : R := cols.carry[7] * E322
  let E324 : R := cols.is_div - 1
  let E325 : R := cols.is_div * E324
  let E326 : R := cols.is_divu - 1
  let E327 : R := cols.is_divu * E326
  let E328 : R := cols.is_rem - 1
  let E329 : R := cols.is_rem * E328
  let E330 : R := cols.is_remu - 1
  let E331 : R := cols.is_remu * E330
  let E332 : R := cols.is_divw - 1
  let E333 : R := cols.is_divw * E332
  let E334 : R := cols.is_remw - 1
  let E335 : R := cols.is_remw * E334
  let E336 : R := cols.is_divuw - 1
  let E337 : R := cols.is_divuw * E336
  let E338 : R := cols.is_remuw - 1
  let E339 : R := cols.is_remuw * E338
  let E340 : R := cols.is_overflow - 1
  let E341 : R := cols.is_overflow * E340
  let E342 : R := cols.is_real_not_word - 1
  let E343 : R := cols.is_real_not_word * E342
  let E344 : R := cols.b_neg - 1
  let E345 : R := cols.b_neg * E344
  let E346 : R := cols.b_neg_not_overflow - 1
  let E347 : R := cols.b_neg_not_overflow * E346
  let E348 : R := cols.b_not_neg_not_overflow - 1
  let E349 : R := cols.b_not_neg_not_overflow * E348
  let E350 : R := cols.rem_neg - 1
  let E351 : R := cols.rem_neg * E350
  let E352 : R := cols.c_neg - 1
  let E353 : R := cols.c_neg * E352
  let E354 : R := cols.is_real - 1
  let E355 : R := cols.is_real * E354
  let E356 : R := cols.abs_c_alu_event - 1
  let E357 : R := cols.abs_c_alu_event * E356
  let E358 : R := cols.abs_rem_alu_event - 1
  let E359 : R := cols.abs_rem_alu_event * E358
  let E360 : R := cols.is_divu + cols.is_remu
  let E361 : R := E360 + cols.is_div
  let E362 : R := E361 + cols.is_rem
  let E363 : R := E362 + cols.is_divw
  let E364 : R := E363 + cols.is_remw
  let E365 : R := E364 + cols.is_divuw
  let E366 : R := E365 + cols.is_remuw
  let E367 : R := (1 : R) - E366
  [E13, E15, E17, E19, E20, E21, E22, E23, E29, E35, E41, E47, E48, E49, E51, E54, E57, E59, E61, E64, E67, E69, E70, E71, E73, E76, E79, E81, E83, E86, E89, E91, E96, E99, E103, E105, E107, E109, E111, E113, E115, E117, E119, E154, E157, E160, E163, E167, E171, E175, E179, E184, E189, E194, E199, E204, E209, E214, E219, E225, E228, E230, E232, E234, E236, E238, E240, E242, E244, E247, E250, E253, E256, E259, E262, E265, E268, E270, E272, E274, E276, E278, E280, E282, E284, E286, E288, E299, E300, E301, E302, E305, E307, E309, E311, E313, E315, E317, E319, E321, E323, E325, E327, E329, E331, E333, E335, E337, E339, E341, E343, E345, E347, E349, E351, E353, E355, E357, E359, E367, cols.adapter.op_a_0]

/-- `E355`, the chip selector's boolean gate, is part of the pure DivRem own-assertion list. -/
theorem isReal_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_real * (cols.is_real - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_div` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isDiv_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_div * (cols.is_div - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_divu` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isDivu_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_divu * (cols.is_divu - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_rem` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isRem_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_rem * (cols.is_rem - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_remu` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isRemu_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_remu * (cols.is_remu - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_divw` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isDivw_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_divw * (cols.is_divw - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_remw` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isRemw_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_remw * (cols.is_remw - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_divuw` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isDivuw_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_divuw * (cols.is_divuw - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The `is_remuw` selector's boolean gate is part of the pure DivRem own-assertion list. -/
theorem isRemuw_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_remuw * (cols.is_remuw - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- `E343`, the `is_real_not_word` scalar's boolean gate, is part of the pure DivRem own-assertion
list (the upper-Mul gate's binariness lever). -/
theorem isRealNotWord_gate_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.is_real_not_word * (cols.is_real_not_word - 1) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- `E367`, the eight-flag one-hot sum, is part of the pure DivRem own-assertion list. -/
theorem flagsSum_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    (1 : Expression (ZMod p)) - (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem +
      cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw) ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

/-- The physical non-`x0` routing assertion is the final entry of the pure DivRem own-assertion
list.  Keeping this membership folded lets whole-chip grounding recover the route without
unfolding the arithmetic evidence contract. -/
theorem opA0_mem_ownAsserts (cols : Var Columns (ZMod p)) :
    cols.adapter.op_a_0 ∈ ownAsserts cols := by
  simp only [ownAsserts]
  repeat first
    | exact List.Mem.head _
    | apply List.Mem.tail

end SP1Clean.DivRemChip
