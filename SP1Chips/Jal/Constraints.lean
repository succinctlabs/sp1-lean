import SP1Operations.Operation.AddOperation

namespace Jal

section constraints

-- Generated Lean code for chip JalChip
def constraints (Main : Vector (Fin BB) 31) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30]$ - 1
  let E1 : Fin BB := Main[30]$ * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3]$, Main[4]$, Main[5]$, 0] #v[Main[14]$, Main[15]$, Main[16]$, Main[17]$] { value := #v[Main[22]$, Main[23]$, Main[24]$, Main[25]$] } Main[30]$
  let E2 : Fin BB := Main[1]$ * 65536
  let E3 : Fin BB := Main[2]$ + E2
  let E4 : Fin BB := Main[30]$ - 1
  let E5 : Fin BB := Main[30]$ * E4
  let E6 : Fin BB := E3 + 8
  let E7 : Fin BB := Main[2]$ - 1
  let E8 : Fin BB := E7 * 1761607681
  let E9 : Fin BB := Main[30]$ - 1
  let E10 : Fin BB := E9 * Main[13]$
  let E11 : Fin BB := Main[30]$ - Main[13]$
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3]$, Main[4]$, Main[5]$, 0] #v[4, 0, 0, 0] { value := #v[Main[26]$, Main[27]$, Main[28]$, Main[29]$] } E11
  let E12 : Fin BB := Main[13]$ * Main[26]$
  let E13 : Fin BB := Main[13]$ * Main[27]$
  let E14 : Fin BB := Main[13]$ * Main[28]$
  let E15 : Fin BB := Main[1]$ * 65536
  let E16 : Fin BB := Main[2]$ + E15
  let E17 : Fin BB := Main[30]$ - 1
  let E18 : Fin BB := Main[30]$ * E17
  let E19 : Fin BB := Main[26]$ - 0
  let E20 : Fin BB := Main[13]$ * E19
  let E21 : Fin BB := Main[27]$ - 0
  let E22 : Fin BB := Main[13]$ * E21
  let E23 : Fin BB := Main[28]$ - 0
  let E24 : Fin BB := Main[13]$ * E23
  let E25 : Fin BB := Main[29]$ - 0
  let E26 : Fin BB := Main[13]$ * E25
  let E27 : Fin BB := E16 + 3
  let E28 : Fin BB := Main[30]$ - 1
  let E29 : Fin BB := Main[30]$ * E28
  let E30 : Fin BB := E27 - Main[11]$
  let E31 : Fin BB := E30 - 1
  let E32 : Fin BB := E31 - Main[12]$
  let E33 : Fin BB := E32 * 2013235201
  CS0 ++ CS1 ++ [
    (.assertZero E1),
    (.assertZero Main[25]$),
    (.assertZero E5),
    (.receive (.state Main[0]$ E3 Main[3]$ Main[4]$ Main[5]$) Main[30]$),
    (.send (.state Main[0]$ E6 Main[22]$ Main[23]$ Main[24]$) Main[30]$),
    (.send (.byte (ByteOpcode.ofNat 6) E8 13 0) Main[30]$),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1]$ 0) Main[30]$),
    (.assertZero E10),
    (.assertZero Main[29]$),
    (.assertZero E12),
    (.assertZero E13),
    (.assertZero E14),
    (.assertZero E18),
    (.send (.program Main[3]$ Main[4]$ Main[5]$ (Opcode.ofNat 33) Main[6]$ Main[14]$ Main[15]$ Main[16]$ Main[17]$ Main[18]$ Main[19]$ Main[20]$ Main[21]$ Main[13]$ 1 1 111 0 0) Main[30]$),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E26),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[12]$ 16 0) Main[30]$),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E33 0) Main[30]$),
    (.send (.memory Main[0]$ Main[11]$ Main[6]$ 0 0 Main[7]$ Main[8]$ Main[9]$ Main[10]$) Main[30]$),
    (.receive (.memory Main[0]$ E27 Main[6]$ 0 0 Main[26]$ Main[27]$ Main[28]$ Main[29]$) Main[30]$),
  ]

end constraints
