-- import SP1Foundations

-- structure U16MSBOperation where
--   msb : Fin BB

-- namespace U16MSBOperation

-- def constraints
--   (a : Fin BB)
--   (cols : U16MSBOperation)
--   (is_real : Fin BB)
--   : SP1ConstraintList :=
--   let E0 : Fin BB := is_real - 1
--   let E1 : Fin BB := is_real * E0
--   let E2 : Fin BB := cols.msb - 1
--   let E3 : Fin BB := cols.msb * E2
--   let E4 : Fin BB := 2 * a
--   let E5 : Fin BB := cols.msb * 65536
--   let E6 : Fin BB := E4 - E5
--   [
--     .assertZero E1,
--     .assertZero E3,
--     .send (.byte (ByteOpcode.ofNat 6) E6 16 0) is_real
--   ]

-- end U16MSBOperation
