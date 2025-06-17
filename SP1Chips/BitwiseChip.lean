import SP1Operations
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace BitwiseChip

/-

Constraints for chip Bitwise (main):
   Expr(0) = Main(30) + Main(31)
   Expr(2) = Expr(0) + Main(32)
   Expr(4) = Main(30) - 1
   Expr(6) = Main(30) * Expr(4)
   Assert(Expr(6) == 0)
   Expr(8) = Main(31) - 1
   Expr(10) = Main(31) * Expr(8)
   Assert(Expr(10) == 0)
   Expr(12) = Main(32) - 1
   Expr(14) = Main(32) * Expr(12)
   Assert(Expr(14) == 0)
   Expr(16) = Expr(2) - 1
   Expr(18) = Expr(2) * Expr(16)
   Assert(Expr(18) == 0)
   Expr(20) = Main(30) * 2
   Expr(22) = Main(31) * 1
   Expr(24) = Expr(20) + Expr(22)
   Expr(26) = Main(32) * 0
   Expr(28) = Expr(24) + Expr(26)
   Expr(30) = Main(30) * 3
   Expr(32) = Main(31) * 4
   Expr(34) = Expr(30) + Expr(32)
   Expr(36) = Main(32) * 5
   Expr(38) = Expr(34) + Expr(36)
   Word(Expr(40), Expr(41)) = BitwiseU16Operation(Word(Main(11), Main(12)), Word(Main(17), Main(18)), BitwiseU16Operation { b_low_bytes: U16toU8Operation { low_bytes: [IrVar(Main(22)), IrVar(Main(23))] }, c_low_bytes: U16toU8Operation { low_bytes: [IrVar(Main(24)), IrVar(Main(25))] }, bitwise_operation: BitwiseOperation { result: [IrVar(Main(26)), IrVar(Main(27)), IrVar(Main(28)), IrVar(Main(29))] } }, Expr(28), Expr(2), )
   Expr(42) = Main(3) + 4
   CPUState(CPUState { shard: IrVar(Main(0)), clk_high_limb: IrVar(Main(1)), clk_low_limb: IrVar(Main(2)), pc: IrVar(Main(3)) }, Expr(42), 4, Expr(2), )
   Expr(44) = 16384 * Main(1)
   Expr(46) = Expr(44) + Main(2)
   ALUTypeReader(Main(0), Expr(46), Main(3), Expr(38), Word(Expr(40), Expr(41)), ALUTypeReader { op_a: IrVar(Main(4)), op_a_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(Main(5)), IrVar(Main(6))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(Main(7)), diff_low_limb: IrVar(Main(8)) } }, op_a_0: IrVar(Main(9)), op_b: IrVar(Main(10)), op_b_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(Main(11)), IrVar(Main(12))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(Main(13)), diff_low_limb: IrVar(Main(14)) } }, op_c: Word([IrVar(Main(15)), IrVar(Main(16))]), op_c_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(Main(17)), IrVar(Main(18))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(Main(19)), diff_low_limb: IrVar(Main(20)) } }, imm_c: IrVar(Main(21)) }, Expr(2), )

fn ALUTypeReader(
    Input(0),
    Input(1),
    Input(2),
    Input(3),
    Word(Input(4), Input(5)),
    ALUTypeReader { op_a: IrVar(InputArg(6)), op_a_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(InputArg(7)), IrVar(InputArg(8))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(InputArg(9)), diff_low_limb: IrVar(InputArg(10)) } }, op_a_0: IrVar(InputArg(11)), op_b: IrVar(InputArg(12)), op_b_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(InputArg(13)), IrVar(InputArg(14))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(InputArg(15)), diff_low_limb: IrVar(InputArg(16)) } }, op_c: Word([IrVar(InputArg(17)), IrVar(InputArg(18))]), op_c_memory: MemoryAccessInShardCols { prev_value: Word([IrVar(InputArg(19)), IrVar(InputArg(20))]), access_timestamp: MemoryAccessInShardTimestamp { prev_clk: IrVar(InputArg(21)), diff_low_limb: IrVar(InputArg(22)) } }, imm_c: IrVar(InputArg(23)) },
    Input(24)) {
   Expr(0) = Input(24) - 1
   Expr(2) = Input(24) * Expr(0)
   Assert(Expr(2) == 0)
   Expr(4) = Input(24) - 1
   Expr(6) = Input(23) - 0
   Expr(8) = Expr(4) * Expr(6)
   Assert(Expr(8) == 0)
   Expr(10) = 0 + Input(12)
   Send(kind: Program, scope: Local, multiplicity: Input(24), values: [Input(2), Input(3), Input(6), Expr(10), 0, Input(17), Input(18), Input(11), 0, Input(23)])
   Expr(12) = Input(4) - 0
   Expr(14) = Input(11) * Expr(12)
   Assert(Expr(14) == 0)
   Expr(16) = Input(5) - 0
   Expr(18) = Input(11) * Expr(16)
   Assert(Expr(18) == 0)
   Expr(20) = Input(1) + 3
   Expr(22) = Input(24) - 1
   Expr(24) = Input(24) * Expr(22)
   Assert(Expr(24) == 0)
   Expr(26) = Expr(20) - Input(9)
   Expr(28) = Expr(26) - 1
   Expr(30) = Expr(28) - Input(10)
   Expr(32) = Expr(30) * 2013143041
   Send(kind: Byte, scope: Local, multiplicity: Input(24), values: [6, Input(10), 14, 0])
   Send(kind: Byte, scope: Local, multiplicity: Input(24), values: [6, Expr(32), 14, 0])
   Send(kind: Memory, scope: Local, multiplicity: Input(24), values: [Input(0), Input(9), Input(6), Input(7), Input(8)])
   Receive(kind: Memory, scope: Local, multiplicity: Input(24), values: [Input(0), Expr(20), Input(6), Input(4), Input(5)])
   Expr(34) = Input(1) + 2
   Expr(36) = Input(24) - 1
   Expr(38) = Input(24) * Expr(36)
   Assert(Expr(38) == 0)
   Expr(40) = Expr(34) - Input(15)
   Expr(42) = Expr(40) - 1
   Expr(44) = Expr(42) - Input(16)
   Expr(46) = Expr(44) * 2013143041
   Send(kind: Byte, scope: Local, multiplicity: Input(24), values: [6, Input(16), 14, 0])
   Send(kind: Byte, scope: Local, multiplicity: Input(24), values: [6, Expr(46), 14, 0])
   Send(kind: Memory, scope: Local, multiplicity: Input(24), values: [Input(0), Input(15), Input(12), Input(13), Input(14)])
   Receive(kind: Memory, scope: Local, multiplicity: Input(24), values: [Input(0), Expr(34), Input(12), Input(13), Input(14)])
   Expr(48) = Input(1) + 1
   Expr(50) = Input(24) - Input(23)
   Expr(52) = Expr(50) - 1
   Expr(54) = Expr(50) * Expr(52)
   Assert(Expr(54) == 0)
   Expr(56) = Expr(48) - Input(21)
   Expr(58) = Expr(56) - 1
   Expr(60) = Expr(58) - Input(22)
   Expr(62) = Expr(60) * 2013143041
   Send(kind: Byte, scope: Local, multiplicity: Expr(50), values: [6, Input(22), 14, 0])
   Send(kind: Byte, scope: Local, multiplicity: Expr(50), values: [6, Expr(62), 14, 0])
   Send(kind: Memory, scope: Local, multiplicity: Expr(50), values: [Input(0), Input(21), Input(17), Input(19), Input(20)])
   Receive(kind: Memory, scope: Local, multiplicity: Expr(50), values: [Input(0), Expr(48), Input(17), Input(19), Input(20)])
   Expr(64) = Input(19) - Input(17)
   Expr(66) = Input(23) * Expr(64)
   Assert(Expr(66) == 0)
   Expr(68) = Input(20) - Input(18)
   Expr(70) = Input(23) * Expr(68)
   Assert(Expr(70) == 0)
}

fn BitwiseOperation(
    [IrVar(InputArg(0)), IrVar(InputArg(1)), IrVar(InputArg(2)), IrVar(InputArg(3))],
    [IrVar(InputArg(4)), IrVar(InputArg(5)), IrVar(InputArg(6)), IrVar(InputArg(7))],
    BitwiseOperation { result: [IrVar(InputArg(8)), IrVar(InputArg(9)), IrVar(InputArg(10)), IrVar(InputArg(11))] },
    Input(12),
    Input(13)) {
   Send(kind: Byte, scope: Local, multiplicity: Input(13), values: [Input(12), Input(8), Input(0), Input(4)])
   Send(kind: Byte, scope: Local, multiplicity: Input(13), values: [Input(12), Input(9), Input(1), Input(5)])
   Send(kind: Byte, scope: Local, multiplicity: Input(13), values: [Input(12), Input(10), Input(2), Input(6)])
   Send(kind: Byte, scope: Local, multiplicity: Input(13), values: [Input(12), Input(11), Input(3), Input(7)])
}

fn BitwiseU16Operation(
    Word(Input(0), Input(1)),
    Word(Input(2), Input(3)),
    BitwiseU16Operation { b_low_bytes: U16toU8Operation { low_bytes: [IrVar(InputArg(4)), IrVar(InputArg(5))] }, c_low_bytes: U16toU8Operation { low_bytes: [IrVar(InputArg(6)), IrVar(InputArg(7))] }, bitwise_operation: BitwiseOperation { result: [IrVar(InputArg(8)), IrVar(InputArg(9)), IrVar(InputArg(10)), IrVar(InputArg(11))] } },
    Input(12),
    Input(13))->Word(Output(0), Output(1)) {
   Expr(0) = Input(13) - 1
   Expr(2) = Input(13) * Expr(0)
   Assert(Expr(2) == 0)
   [Expr(4), Expr(5), Expr(6), Expr(7)] = U16toU8OperationUnsafe([IrVar(InputArg(0)), IrVar(InputArg(1))], U16toU8Operation { low_bytes: [IrVar(InputArg(4)), IrVar(InputArg(5))] }, )
   [Expr(8), Expr(9), Expr(10), Expr(11)] = U16toU8OperationUnsafe([IrVar(InputArg(2)), IrVar(InputArg(3))], U16toU8Operation { low_bytes: [IrVar(InputArg(6)), IrVar(InputArg(7))] }, )
   BitwiseOperation([Expr(4), Expr(5), Expr(6), Expr(7)], [Expr(8), Expr(9), Expr(10), Expr(11)], BitwiseOperation { result: [IrVar(InputArg(8)), IrVar(InputArg(9)), IrVar(InputArg(10)), IrVar(InputArg(11))] }, Input(12), Input(13), )
   Expr(12) = Input(9) * 256
   Expr(14) = Input(8) + Expr(12)
   Expr(16) = Input(11) * 256
   Expr(18) = Input(10) + Expr(16)
   Output(0) = Expr(14)
   Output(1) = Expr(18)
}

fn CPUState(
    CPUState { shard: IrVar(InputArg(0)), clk_high_limb: IrVar(InputArg(1)), clk_low_limb: IrVar(InputArg(2)), pc: IrVar(InputArg(3)) },
    Input(4),
    Input(5),
    Input(6)) {
   Expr(0) = 16384 * Input(1)
   Expr(2) = Expr(0) + Input(2)
   Expr(4) = Input(6) - 1
   Expr(6) = Input(6) * Expr(4)
   Assert(Expr(6) == 0)
   Receive(kind: State, scope: Local, multiplicity: Input(6), values: [Input(0), Expr(2), Input(3)])
   Expr(8) = Expr(2) + Input(5)
   Send(kind: State, scope: Local, multiplicity: Input(6), values: [Input(0), Expr(8), Input(4)])
   Send(kind: Byte, scope: Local, multiplicity: Input(6), values: [6, Input(1), 14, 0])
   Send(kind: Byte, scope: Local, multiplicity: Input(6), values: [6, Input(2), 14, 0])
}

fn U16toU8OperationUnsafe(
    [IrVar(InputArg(0)), IrVar(InputArg(1))],
    U16toU8Operation { low_bytes: [IrVar(InputArg(2)), IrVar(InputArg(3))] })->[IrVar(OutputArg(0)), IrVar(OutputArg(1)), IrVar(OutputArg(2)), IrVar(OutputArg(3))] {
   Expr(0) = Input(0) - Input(2)
   Expr(2) = Expr(0) * 2005401601
   Expr(4) = Input(1) - Input(3)
   Expr(6) = Expr(4) * 2005401601
   Output(0) = Input(2)
   Output(1) = Expr(2)
   Output(2) = Input(3)
   Output(3) = Expr(6)
}

-/

def constraints
  (Main : Vector BabyBear 23)
  : List SP1Constraint :=
  let E0 : BabyBear := Main[22] - 1
  let E2 : BabyBear := Main[22] * E0
  let E4 : BabyBear := Main[3] + 4
  let E6 : BabyBear := 16384 * Main[1]
  let E8 : BabyBear := E6 + Main[2]
  [ .assertZero E2
  ]
  ++ (AddOperation.constraints #v[Main[11], Main[12], Main[16], Main[17], Main[20], Main[21], Main[22]])
  ++ (CPUState.constraints
      { shard := Main[0]
      , clk_high_limb := Main[1]
      , clk_low_limb := Main[2]
      , pc := Main[3] }
      E4
      4
      Main[22])
  ++ (RTypeReader.constraints
    Main[0]
    E8
    -- Main[3]
    -- 0
    #v[Main[20], Main[21]]
    { op_a := Main[4]
    , op_a_memory :=
        { prev_value := #v[Main[5], Main[6]]
        , access_timestamp :=
            { prev_clk := Main[7]
            , diff_low_limb := Main[8]
            }
        }
    , op_a_0 := Main[9]
    , op_b := Main[10]
    , op_b_memory :=
        { prev_value := #v[Main[11], Main[12]]
        , access_timestamp :=
            { prev_clk := Main[13]
            , diff_low_limb := Main[14]
            }
        }
    , op_c := Main[15]
    , op_c_memory :=
        { prev_value := #v[Main[16], Main[17]]
        , access_timestamp :=
            { prev_clk := Main[18]
            , diff_low_limb := Main[19]
            }
        }
    }
    Main[22])

lemma bound_of_constraints (Main : Vector BabyBear 23)
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  linarith

def sp1_add
    (Main : Vector BabyBear 23)
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (h_is_real : Main[22] = 1)
    (rd rs1 rs2 : regidx) :
    SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let rs1_value ← rX_bits rs1
  let rs2_value ← rX_bits rs2
  wX_bits rd (BitVec.ofNatLT (Main[20].val + Main[21].val * 65536) (bound_of_constraints Main cstrs h_is_real))

def spec_add
    (rd rs1 rs2 : regidx) :
    SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  pure ()

theorem sp1_add_implies_spec_add (Main : Vector BabyBear 23)
    (cstrs : List.Forall SP1Constraint.toProp (constraints Main))
    (h_is_real : Main[22] = 1) (rd rs1 rs2 : regidx) :
    sp1_add Main cstrs h_is_real rd rs1 rs2 = spec_add rd rs1 rs2 := by
  unfold sp1_add spec_add
  simp only [sp1_add, spec_add]
  -- Extract the various constraints from the assumption
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  clear cstrs

  have read_b : RTypeReader.registerMatch rs1 Main[11] Main[12] :=
    RTypeReader.read_b_fun _ _ adapter_cstrs
  have read_c : RTypeReader.registerMatch rs2 Main[16] Main[17] :=
    RTypeReader.read_c_fun _ _ adapter_cstrs

  simp [RTypeReader.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at adapter_cstrs
  simp [SP1Constraint.toProp, sub_eq_zero] at orig_cstrs

  let M11_U16 : U16 := ⟨Main[11], adapter_cstrs.right.right.right.right.right.right.right.left.left⟩
  let M12_U16 : U16 := ⟨Main[12], adapter_cstrs.right.right.right.right.right.right.right.left.right⟩
  let M16_U16 : U16 := ⟨Main[16], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.left⟩
  let M17_U16 : U16 := ⟨Main[17], adapter_cstrs.right.right.right.right.right.right.right.right.right.right.right⟩
  let M20_U16 : U16 := ⟨Main[20], adapter_cstrs.right.right.right.right.left.left⟩
  let M21_U16 : U16 := ⟨Main[21], adapter_cstrs.right.right.right.right.left.right⟩
  let M22_U1  : U1  := ⟨Main[22], by clear * - orig_cstrs; aesop⟩

  let add_spec := AddOperation.correct M20_U16 M21_U16 M11_U16 M12_U16 M16_U16 M17_U16 M22_U1 add_cstrs
  simp only [AddOperation.spec] at add_spec

  have res_eq_bv_add := add_spec (by clear * - h_is_real; aesop)
  simp [BitVec.ofU16] at res_eq_bv_add
  rw [res_eq_bv_add]

  simp only [execute_RTYPE, Nat.reducePow, Nat.reduceMul, bind_pure_comp, bind_assoc,
    bind_map_left, map_bind, Functor.map_map, id_map']

  specialize read_b (by
    have := M11_U16.in_range
    have := M12_U16.in_range
    linarith)
  specialize read_c (by
    have := M16_U16.in_range
    have := M17_U16.in_range
    linarith
  )
  simp [read_b, read_c]

  rfl

end BitwiseChip
