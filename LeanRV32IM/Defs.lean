import LeanRV32IM.Sail.Sail
import LeanRV32IM.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr

abbrev xlenbits := (BitVec 32)

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq, Repr

abbrev nat1 := Int

abbrev max_mem_access : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev xlen : Int := 32

abbrev log2_xlen : Int := (bif xlen = 32 then 5 else 6)

abbrev xlen_bytes : Int := (bif xlen = 32 then 4 else 8)

abbrev physaddrbits_len : Int := (bif xlen = 32 then 34 else 64)

abbrev asidlen : Int := (bif xlen = 32 then 9 else 16)

abbrev asidbits := (BitVec (bif 32 = 32 then 9 else 16))

abbrev ext_d_supported : Bool := false

abbrev flen_bytes : Int := (bif ext_d_supported then 8 else 4)

abbrev flen : Int := (bif false then 8 else 4 * 8)

abbrev flenbits := (BitVec (bif false then 8 else 4 * 8))

abbrev vlenmax : Int := 65536

abbrev physaddrbits := (BitVec (bif 32 = 32 then 34 else 64))

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq, Repr

abbrev mem_meta := Unit

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving BEq, Inhabited, Repr

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving BEq, Inhabited, Repr

inductive barrier_kind where | Barrier_RISCV_rw_rw | Barrier_RISCV_r_rw | Barrier_RISCV_r_r | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_w_rw | Barrier_RISCV_rw_r | Barrier_RISCV_r_w | Barrier_RISCV_w_r | Barrier_RISCV_tso | Barrier_RISCV_i
  deriving BEq, Inhabited, Repr

structure RISCV_strong_access where
  variety : Access_variety
  deriving BEq, Inhabited, Repr

abbrev RVFI_DII_Instruction_Packet := (BitVec 64)

abbrev RVFI_DII_Execution_Packet_InstMetaData := (BitVec 192)

abbrev RVFI_DII_Execution_Packet_PC := (BitVec 128)

abbrev RVFI_DII_Execution_Packet_Ext_Integer := (BitVec 320)

abbrev RVFI_DII_Execution_Packet_Ext_MemAccess := (BitVec 704)

abbrev RVFI_DII_Execution_Packet_V1 := (BitVec 704)

abbrev RVFI_DII_Execution_PacketV2 := (BitVec 512)

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Zicbom | Ext_Zicboz | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihpm | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zalrsc | Ext_Zawrs | Ext_Zfa | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Sscofpmf | Ext_Sstc | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Smcntrpmf
  deriving BEq, Inhabited, Repr

abbrev exc_code := (BitVec 8)

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev ext_ptw_error := Unit

abbrev ext_exc_type := Unit

abbrev half := (BitVec 16)

abbrev word := (BitVec 32)

abbrev instbits := (BitVec 32)

abbrev pagesize_bits : Int := 12

inductive cregidx where
  | Cregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr

abbrev csreg := (BitVec 12)

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr

inductive Architecture where | RV32 | RV64 | RV128
  deriving BEq, Inhabited, Repr

abbrev arch_xlen := (BitVec 2)

abbrev priv_level := (BitVec 2)

inductive Privilege where | User | Supervisor | Machine
  deriving BEq, Inhabited, Repr

/-- Type quantifiers: k_a : Type -/
inductive AccessType (k_a : Type) where
  | Read (_ : k_a)
  | Write (_ : k_a)
  | ReadWrite (_ : (k_a × k_a))
  | InstructionFetch (_ : Unit)
  deriving Inhabited, BEq, Repr

inductive ExceptionType where
  | E_Fetch_Addr_Align (_ : Unit)
  | E_Fetch_Access_Fault (_ : Unit)
  | E_Illegal_Instr (_ : Unit)
  | E_Breakpoint (_ : Unit)
  | E_Load_Addr_Align (_ : Unit)
  | E_Load_Access_Fault (_ : Unit)
  | E_SAMO_Addr_Align (_ : Unit)
  | E_SAMO_Access_Fault (_ : Unit)
  | E_U_EnvCall (_ : Unit)
  | E_S_EnvCall (_ : Unit)
  | E_Reserved_10 (_ : Unit)
  | E_M_EnvCall (_ : Unit)
  | E_Fetch_Page_Fault (_ : Unit)
  | E_Load_Page_Fault (_ : Unit)
  | E_Reserved_14 (_ : Unit)
  | E_SAMO_Page_Fault (_ : Unit)
  | E_Extension (_ : ext_exc_type)
  deriving Inhabited, BEq, Repr

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, Inhabited, Repr

inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, Inhabited, Repr

structure mul_op where
  high : Bool
  signed_rs1 : Bool
  signed_rs2 : Bool
  deriving BEq, Inhabited, Repr

inductive rop where | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, Inhabited, Repr

inductive sop where | SLLI | SRLI | SRAI
  deriving BEq, Inhabited, Repr

inductive uop where | LUI | AUIPC
  deriving BEq, Inhabited, Repr

abbrev word_width := Int

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | JAL (_ : ((BitVec 21) × regidx))
  | JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width))
  | FENCE (_ : ((BitVec 4) × (BitVec 4)))
  | FENCE_TSO (_ : Unit)
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  deriving Inhabited, BEq, Repr

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Update (_ : Unit)
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq, Repr

inductive WaitReason where | WAIT_WFI | WAIT_WRS_STO | WAIT_WRS_NTO
  deriving BEq, Inhabited, Repr



inductive InterruptType where | I_U_Software | I_S_Software | I_M_Software | I_U_Timer | I_S_Timer | I_M_Timer | I_U_External | I_S_External | I_M_External
  deriving BEq, Inhabited, Repr

abbrev tv_mode := (BitVec 2)

inductive TrapVectorMode where | TV_Direct | TV_Vector | TV_Reserved
  deriving BEq, Inhabited, Repr

abbrev ext_status := (BitVec 2)

inductive ExtStatus where | Off | Initial | Clean | Dirty
  deriving BEq, Inhabited, Repr

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving BEq, Inhabited, Repr

abbrev csrRW := (BitVec 2)

inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
  deriving BEq, Inhabited, Repr

inductive sopw where | SLLIW | SRLIW | SRAIW
  deriving BEq, Inhabited, Repr

inductive amoop where | AMOSWAP | AMOADD | AMOXOR | AMOAND | AMOOR | AMOMIN | AMOMAX | AMOMINU | AMOMAXU
  deriving BEq, Inhabited, Repr

inductive csrop where | CSRRW | CSRRS | CSRRC
  deriving BEq, Inhabited, Repr

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving BEq, Inhabited, Repr

inductive brop_zba where | SH1ADD | SH2ADD | SH3ADD
  deriving BEq, Inhabited, Repr

inductive brop_zbb where | ANDN | ORN | XNOR | MAX | MAXU | MIN | MINU | ROL | ROR
  deriving BEq, Inhabited, Repr

inductive brop_zbkb where | PACK | PACKH
  deriving BEq, Inhabited, Repr

inductive brop_zbs where | BCLR | BEXT | BINV | BSET
  deriving BEq, Inhabited, Repr

inductive bropw_zba where | ADDUW | SH1ADDUW | SH2ADDUW | SH3ADDUW
  deriving BEq, Inhabited, Repr

inductive bropw_zbb where | ROLW | RORW
  deriving BEq, Inhabited, Repr

inductive biop_zbs where | BCLRI | BEXTI | BINVI | BSETI
  deriving BEq, Inhabited, Repr

inductive extop_zbb where | SEXTB | SEXTH | ZEXTH
  deriving BEq, Inhabited, Repr

inductive zicondop where | CZERO_EQZ | CZERO_NEZ
  deriving BEq, Inhabited, Repr

inductive wrsop where | WRS_STO | WRS_NTO
  deriving BEq, Inhabited, Repr



abbrev level_range (k_v : Nat) := Nat

abbrev pte_bits k_v := (BitVec (bif k_v = 32 then 32 else 64))

abbrev ppn_bits k_v := (BitVec (bif k_v = 32 then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

abbrev ext_access_type := Unit

abbrev regtype := xlenbits

abbrev Misa := (BitVec 32)

abbrev Mstatus := (BitVec 64)

abbrev Seccfg := (BitVec 64)

abbrev MEnvcfg := (BitVec 64)

abbrev SEnvcfg := (BitVec 32)

abbrev Minterrupts := (BitVec 32)

abbrev Medeleg := (BitVec 64)

abbrev Mtvec := (BitVec 32)

abbrev Mcause := (BitVec 32)

abbrev Counteren := (BitVec 32)

abbrev Counterin := (BitVec 32)

abbrev Sstatus := (BitVec 64)

abbrev Sinterrupts := (BitVec 32)

abbrev Satp64 := (BitVec 64)

abbrev Satp32 := (BitVec 32)

abbrev Vtype := (BitVec 32)

abbrev SEW_pow := Nat

abbrev LMUL_pow := Int

abbrev sew_bitsize := Int



inductive agtype where | UNDISTURBED | AGNOSTIC
  deriving BEq, Inhabited, Repr

/-- Type quantifiers: k_a : Type -/
inductive Ext_FetchAddr_Check (k_a : Type) where
  | Ext_FetchAddr_OK (_ : virtaddr)
  | Ext_FetchAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr

/-- Type quantifiers: k_a : Type -/
inductive Ext_ControlAddr_Check (k_a : Type) where
  | Ext_ControlAddr_OK (_ : virtaddr)
  | Ext_ControlAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr

inductive Ext_PhysAddr_Check where
  | Ext_PhysAddr_OK (_ : Unit)
  | Ext_PhysAddr_Error (_ : ExceptionType)
  deriving Inhabited, BEq, Repr

abbrev ext_fetch_addr_error := Unit

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

abbrev ext_exception := Unit

structure sync_exception where
  trap : ExceptionType
  excinfo : (Option xlenbits)
  ext : (Option ext_exception)
  deriving BEq, Inhabited, Repr

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving BEq, Inhabited, Repr

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving BEq, Inhabited, Repr

abbrev vreglenbits := (BitVec 65536)

abbrev vregtype := vreglenbits

inductive vvfunct6 where | VV_VADD | VV_VSUB | VV_VMINU | VV_VMIN | VV_VMAXU | VV_VMAX | VV_VAND | VV_VOR | VV_VXOR | VV_VRGATHER | VV_VRGATHEREI16 | VV_VSADDU | VV_VSADD | VV_VSSUBU | VV_VSSUB | VV_VSLL | VV_VSMUL | VV_VSRL | VV_VSRA | VV_VSSRL | VV_VSSRA
  deriving BEq, Inhabited, Repr

inductive vvcmpfunct6 where | VVCMP_VMSEQ | VVCMP_VMSNE | VVCMP_VMSLTU | VVCMP_VMSLT | VVCMP_VMSLEU | VVCMP_VMSLE
  deriving BEq, Inhabited, Repr

inductive vvmfunct6 where | VVM_VMADC | VVM_VMSBC
  deriving BEq, Inhabited, Repr

inductive vvmcfunct6 where | VVMC_VMADC | VVMC_VMSBC
  deriving BEq, Inhabited, Repr

inductive vvmsfunct6 where | VVMS_VADC | VVMS_VSBC
  deriving BEq, Inhabited, Repr

inductive vxmfunct6 where | VXM_VMADC | VXM_VMSBC
  deriving BEq, Inhabited, Repr

inductive vxmcfunct6 where | VXMC_VMADC | VXMC_VMSBC
  deriving BEq, Inhabited, Repr

inductive vxmsfunct6 where | VXMS_VADC | VXMS_VSBC
  deriving BEq, Inhabited, Repr

inductive vimfunct6 where | VIM_VMADC
  deriving BEq, Inhabited, Repr

inductive vimcfunct6 where | VIMC_VMADC
  deriving BEq, Inhabited, Repr

inductive vimsfunct6 where | VIMS_VADC
  deriving BEq, Inhabited, Repr

inductive vxcmpfunct6 where | VXCMP_VMSEQ | VXCMP_VMSNE | VXCMP_VMSLTU | VXCMP_VMSLT | VXCMP_VMSLEU | VXCMP_VMSLE | VXCMP_VMSGTU | VXCMP_VMSGT
  deriving BEq, Inhabited, Repr

inductive vicmpfunct6 where | VICMP_VMSEQ | VICMP_VMSNE | VICMP_VMSLEU | VICMP_VMSLE | VICMP_VMSGTU | VICMP_VMSGT
  deriving BEq, Inhabited, Repr

inductive nvfunct6 where | NV_VNCLIPU | NV_VNCLIP
  deriving BEq, Inhabited, Repr

inductive nvsfunct6 where | NVS_VNSRL | NVS_VNSRA
  deriving BEq, Inhabited, Repr

inductive nxfunct6 where | NX_VNCLIPU | NX_VNCLIP
  deriving BEq, Inhabited, Repr

inductive nxsfunct6 where | NXS_VNSRL | NXS_VNSRA
  deriving BEq, Inhabited, Repr

inductive mmfunct6 where | MM_VMAND | MM_VMNAND | MM_VMANDN | MM_VMXOR | MM_VMOR | MM_VMNOR | MM_VMORN | MM_VMXNOR
  deriving BEq, Inhabited, Repr

inductive nifunct6 where | NI_VNCLIPU | NI_VNCLIP
  deriving BEq, Inhabited, Repr

inductive nisfunct6 where | NIS_VNSRL | NIS_VNSRA
  deriving BEq, Inhabited, Repr

inductive wvvfunct6 where | WVV_VADD | WVV_VSUB | WVV_VADDU | WVV_VSUBU | WVV_VWMUL | WVV_VWMULU | WVV_VWMULSU
  deriving BEq, Inhabited, Repr

inductive wvfunct6 where | WV_VADD | WV_VSUB | WV_VADDU | WV_VSUBU
  deriving BEq, Inhabited, Repr

inductive wvxfunct6 where | WVX_VADD | WVX_VSUB | WVX_VADDU | WVX_VSUBU | WVX_VWMUL | WVX_VWMULU | WVX_VWMULSU
  deriving BEq, Inhabited, Repr

inductive wxfunct6 where | WX_VADD | WX_VSUB | WX_VADDU | WX_VSUBU
  deriving BEq, Inhabited, Repr

inductive vextfunct6 where | VEXT2_ZVF2 | VEXT2_SVF2 | VEXT4_ZVF4 | VEXT4_SVF4 | VEXT8_ZVF8 | VEXT8_SVF8
  deriving BEq, Inhabited, Repr

inductive vxfunct6 where | VX_VADD | VX_VSUB | VX_VRSUB | VX_VMINU | VX_VMIN | VX_VMAXU | VX_VMAX | VX_VAND | VX_VOR | VX_VXOR | VX_VSADDU | VX_VSADD | VX_VSSUBU | VX_VSSUB | VX_VSLL | VX_VSMUL | VX_VSRL | VX_VSRA | VX_VSSRL | VX_VSSRA
  deriving BEq, Inhabited, Repr

inductive vifunct6 where | VI_VADD | VI_VRSUB | VI_VAND | VI_VOR | VI_VXOR | VI_VSADDU | VI_VSADD | VI_VSLL | VI_VSRL | VI_VSRA | VI_VSSRL | VI_VSSRA
  deriving BEq, Inhabited, Repr

inductive vxsgfunct6 where | VX_VSLIDEUP | VX_VSLIDEDOWN | VX_VRGATHER
  deriving BEq, Inhabited, Repr

inductive visgfunct6 where | VI_VSLIDEUP | VI_VSLIDEDOWN | VI_VRGATHER
  deriving BEq, Inhabited, Repr

inductive mvvfunct6 where | MVV_VAADDU | MVV_VAADD | MVV_VASUBU | MVV_VASUB | MVV_VMUL | MVV_VMULH | MVV_VMULHU | MVV_VMULHSU | MVV_VDIVU | MVV_VDIV | MVV_VREMU | MVV_VREM
  deriving BEq, Inhabited, Repr

inductive mvvmafunct6 where | MVV_VMACC | MVV_VNMSAC | MVV_VMADD | MVV_VNMSUB
  deriving BEq, Inhabited, Repr

inductive rmvvfunct6 where | MVV_VREDSUM | MVV_VREDAND | MVV_VREDOR | MVV_VREDXOR | MVV_VREDMINU | MVV_VREDMIN | MVV_VREDMAXU | MVV_VREDMAX
  deriving BEq, Inhabited, Repr

inductive rivvfunct6 where | IVV_VWREDSUMU | IVV_VWREDSUM
  deriving BEq, Inhabited, Repr

inductive rfvvfunct6 where | FVV_VFREDOSUM | FVV_VFREDUSUM | FVV_VFREDMAX | FVV_VFREDMIN | FVV_VFWREDOSUM | FVV_VFWREDUSUM
  deriving BEq, Inhabited, Repr

inductive wmvvfunct6 where | WMVV_VWMACCU | WMVV_VWMACC | WMVV_VWMACCSU
  deriving BEq, Inhabited, Repr

inductive mvxfunct6 where | MVX_VAADDU | MVX_VAADD | MVX_VASUBU | MVX_VASUB | MVX_VSLIDE1UP | MVX_VSLIDE1DOWN | MVX_VMUL | MVX_VMULH | MVX_VMULHU | MVX_VMULHSU | MVX_VDIVU | MVX_VDIV | MVX_VREMU | MVX_VREM
  deriving BEq, Inhabited, Repr

inductive mvxmafunct6 where | MVX_VMACC | MVX_VNMSAC | MVX_VMADD | MVX_VNMSUB
  deriving BEq, Inhabited, Repr

inductive wmvxfunct6 where | WMVX_VWMACCU | WMVX_VWMACC | WMVX_VWMACCUS | WMVX_VWMACCSU
  deriving BEq, Inhabited, Repr

inductive maskfunct3 where | VV_VMERGE | VI_VMERGE | VX_VMERGE
  deriving BEq, Inhabited, Repr

inductive vlewidth where | VLE8 | VLE16 | VLE32 | VLE64
  deriving BEq, Inhabited, Repr

inductive fvvfunct6 where | FVV_VADD | FVV_VSUB | FVV_VMIN | FVV_VMAX | FVV_VSGNJ | FVV_VSGNJN | FVV_VSGNJX | FVV_VDIV | FVV_VMUL
  deriving BEq, Inhabited, Repr

inductive fvvmafunct6 where | FVV_VMADD | FVV_VNMADD | FVV_VMSUB | FVV_VNMSUB | FVV_VMACC | FVV_VNMACC | FVV_VMSAC | FVV_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwvvfunct6 where | FWVV_VADD | FWVV_VSUB | FWVV_VMUL
  deriving BEq, Inhabited, Repr

inductive fwvvmafunct6 where | FWVV_VMACC | FWVV_VNMACC | FWVV_VMSAC | FWVV_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwvfunct6 where | FWV_VADD | FWV_VSUB
  deriving BEq, Inhabited, Repr

inductive fvvmfunct6 where | FVVM_VMFEQ | FVVM_VMFLE | FVVM_VMFLT | FVVM_VMFNE
  deriving BEq, Inhabited, Repr

inductive vfunary0 where | FV_CVT_XU_F | FV_CVT_X_F | FV_CVT_F_XU | FV_CVT_F_X | FV_CVT_RTZ_XU_F | FV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vfwunary0 where | FWV_CVT_XU_F | FWV_CVT_X_F | FWV_CVT_F_XU | FWV_CVT_F_X | FWV_CVT_F_F | FWV_CVT_RTZ_XU_F | FWV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vfnunary0 where | FNV_CVT_XU_F | FNV_CVT_X_F | FNV_CVT_F_XU | FNV_CVT_F_X | FNV_CVT_F_F | FNV_CVT_ROD_F_F | FNV_CVT_RTZ_XU_F | FNV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vfunary1 where | FVV_VSQRT | FVV_VRSQRT7 | FVV_VREC7 | FVV_VCLASS
  deriving BEq, Inhabited, Repr

inductive fvffunct6 where | VF_VADD | VF_VSUB | VF_VMIN | VF_VMAX | VF_VSGNJ | VF_VSGNJN | VF_VSGNJX | VF_VDIV | VF_VRDIV | VF_VMUL | VF_VRSUB | VF_VSLIDE1UP | VF_VSLIDE1DOWN
  deriving BEq, Inhabited, Repr

inductive fvfmafunct6 where | VF_VMADD | VF_VNMADD | VF_VMSUB | VF_VNMSUB | VF_VMACC | VF_VNMACC | VF_VMSAC | VF_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwvffunct6 where | FWVF_VADD | FWVF_VSUB | FWVF_VMUL
  deriving BEq, Inhabited, Repr

inductive fwvfmafunct6 where | FWVF_VMACC | FWVF_VNMACC | FWVF_VMSAC | FWVF_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwffunct6 where | FWF_VADD | FWF_VSUB
  deriving BEq, Inhabited, Repr

inductive fvfmfunct6 where | VFM_VMFEQ | VFM_VMFLE | VFM_VMFLT | VFM_VMFNE | VFM_VMFGT | VFM_VMFGE
  deriving BEq, Inhabited, Repr

inductive vmlsop where | VLM | VSM
  deriving BEq, Inhabited, Repr

inductive vregidx where
  | Vregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr

inductive vregno where
  | Vregno (_ : Nat)
  deriving Inhabited, BEq, Repr

abbrev Vcsr := (BitVec 3)

abbrev bits_rm := (BitVec 3)

abbrev bits_fflags := (BitVec 5)

abbrev bits_H := (BitVec 16)

abbrev bits_S := (BitVec 32)

abbrev bits_D := (BitVec 64)

abbrev bits_W := (BitVec 32)

abbrev bits_WU := (BitVec 32)

abbrev bits_L := (BitVec 64)

abbrev bits_LU := (BitVec 64)

abbrev fregtype := flenbits

inductive f_madd_op_H where | FMADD_H | FMSUB_H | FNMSUB_H | FNMADD_H
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_H where | FADD_H | FSUB_H | FMUL_H | FDIV_H
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_H where | FSQRT_H | FCVT_H_S | FCVT_H_D | FCVT_S_H | FCVT_D_H
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_H where | FCVT_W_H | FCVT_WU_H | FCVT_L_H | FCVT_LU_H
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_H where | FCVT_H_W | FCVT_H_WU | FCVT_H_L | FCVT_H_LU
  deriving BEq, Inhabited, Repr

inductive f_un_x_op_H where | FCLASS_H | FMV_X_H
  deriving BEq, Inhabited, Repr

inductive f_un_f_op_H where | FMV_H_X
  deriving BEq, Inhabited, Repr

inductive f_bin_f_op_H where | FSGNJ_H | FSGNJN_H | FSGNJX_H | FMIN_H | FMAX_H
  deriving BEq, Inhabited, Repr

inductive f_bin_x_op_H where | FEQ_H | FLT_H | FLE_H
  deriving BEq, Inhabited, Repr

inductive rounding_mode where | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM | RM_DYN
  deriving BEq, Inhabited, Repr

inductive f_madd_op_S where | FMADD_S | FMSUB_S | FNMSUB_S | FNMADD_S
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_S where | FADD_S | FSUB_S | FMUL_S | FDIV_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_S where | FSQRT_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_S where | FCVT_W_S | FCVT_WU_S | FCVT_L_S | FCVT_LU_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_S where | FCVT_S_W | FCVT_S_WU | FCVT_S_L | FCVT_S_LU
  deriving BEq, Inhabited, Repr

inductive f_un_op_f_S where | FMV_W_X
  deriving BEq, Inhabited, Repr

inductive f_un_op_x_S where | FCLASS_S | FMV_X_W
  deriving BEq, Inhabited, Repr

inductive f_bin_op_f_S where | FSGNJ_S | FSGNJN_S | FSGNJX_S | FMIN_S | FMAX_S
  deriving BEq, Inhabited, Repr

inductive f_bin_op_x_S where | FEQ_S | FLT_S | FLE_S
  deriving BEq, Inhabited, Repr

inductive f_madd_op_D where | FMADD_D | FMSUB_D | FNMSUB_D | FNMADD_D
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_D where | FADD_D | FSUB_D | FMUL_D | FDIV_D
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_D where | FSQRT_D | FCVT_S_D | FCVT_D_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_D where | FCVT_W_D | FCVT_WU_D | FCVT_L_D | FCVT_LU_D
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_D where | FCVT_D_W | FCVT_D_WU | FCVT_D_L | FCVT_D_LU
  deriving BEq, Inhabited, Repr

inductive f_bin_f_op_D where | FSGNJ_D | FSGNJN_D | FSGNJX_D | FMIN_D | FMAX_D
  deriving BEq, Inhabited, Repr

inductive f_bin_x_op_D where | FEQ_D | FLT_D | FLE_D
  deriving BEq, Inhabited, Repr

inductive f_un_x_op_D where | FCLASS_D | FMV_X_D
  deriving BEq, Inhabited, Repr

inductive f_un_f_op_D where | FMV_D_X
  deriving BEq, Inhabited, Repr

inductive fregidx where
  | Fregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr

inductive fregno where
  | Fregno (_ : Nat)
  deriving Inhabited, BEq, Repr

inductive cfregidx where
  | Cfregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr

abbrev Fcsr := (BitVec 32)

abbrev HpmEvent := (BitVec 64)

abbrev hpmidx := Nat

inductive seed_opst where | BIST | ES16 | WAIT | DEAD
  deriving BEq, Inhabited, Repr

abbrev CountSmcntrpmf := (BitVec 64)

inductive ctl_result where
  | CTL_TRAP (_ : sync_exception)
  | CTL_SRET (_ : Unit)
  | CTL_MRET (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev MemoryOpResult k_a := (Result k_a ExceptionType)

abbrev htif_cmd := (BitVec 64)

inductive ExecutionResult where
  | Retire_Success (_ : Unit)
  | Enter_Wait (_ : WaitReason)
  | Illegal_Instruction (_ : Unit)
  | Trap (_ : (Privilege × ctl_result × xlenbits))
  | Memory_Exception (_ : (virtaddr × ExceptionType))
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, BEq, Repr

inductive zvk_vsha2_funct6 where | ZVK_VSHA2CH_VV | ZVK_VSHA2CL_VV
  deriving BEq, Inhabited, Repr

inductive zvk_vsm4r_funct6 where | ZVK_VSM4R_VV | ZVK_VSM4R_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesdf_funct6 where | ZVK_VAESDF_VV | ZVK_VAESDF_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesdm_funct6 where | ZVK_VAESDM_VV | ZVK_VAESDM_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesef_funct6 where | ZVK_VAESEF_VV | ZVK_VAESEF_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesem_funct6 where | ZVK_VAESEM_VV | ZVK_VAESEM_VS
  deriving BEq, Inhabited, Repr

abbrev pte_flags_bits := (BitVec 8)

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × ext_ptw_fail))
  deriving Inhabited, BEq, Repr

abbrev tlb_vpn_bits : Int := (57 - 12)

abbrev tlb_ppn_bits : Int := 44

structure TLB_Entry where
  asid : asidbits
  global : Bool
  vpn : (BitVec (57 - 12))
  levelMask : (BitVec (57 - 12))
  ppn : (BitVec 44)
  pte : (BitVec 64)
  pteAddr : physaddr
  deriving BEq, Inhabited, Repr

abbrev num_tlb_entries : Int := 64

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, is_sv_mode(k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  global : Bool
  deriving BEq, Inhabited, Repr

abbrev PTW_Result k_v := (Result ((PTW_Output k_v) × ext_ptw) (PTW_Error × ext_ptw))

abbrev TR_Result k_paddr k_failure := (Result (k_paddr × ext_ptw) (k_failure × ext_ptw))



inductive Register : Type where
  | satp
  | tlb
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | stimecmp
  | mtimecmp
  | plat_clint_size
  | plat_clint_base
  | plat_rom_size
  | plat_rom_base
  | plat_ram_size
  | plat_ram_base
  | minstretcfg
  | mcyclecfg
  | mhpmcounter
  | mhpmevent
  | fcsr
  | f31
  | f30
  | f29
  | f28
  | f27
  | f26
  | f25
  | f24
  | f23
  | f22
  | f21
  | f20
  | f19
  | f18
  | f17
  | f16
  | f15
  | f14
  | f13
  | f12
  | f11
  | f10
  | f9
  | f8
  | f7
  | f6
  | f5
  | f4
  | f3
  | f2
  | f1
  | f0
  | float_fflags
  | float_result
  | vcsr
  | vr31
  | vr30
  | vr29
  | vr28
  | vr27
  | vr26
  | vr25
  | vr24
  | vr23
  | vr22
  | vr21
  | vr20
  | vr19
  | vr18
  | vr17
  | vr16
  | vr15
  | vr14
  | vr13
  | vr12
  | vr11
  | vr10
  | vr9
  | vr8
  | vr7
  | vr6
  | vr5
  | vr4
  | vr3
  | vr2
  | vr1
  | vr0
  | pmpaddr_n
  | pmpcfg_n
  | vtype
  | vl
  | vstart
  | tselect
  | stval
  | scause
  | sepc
  | sscratch
  | stvec
  | mconfigptr
  | mhartid
  | marchid
  | mimpid
  | mvendorid
  | minstret_increment
  | minstret
  | mtime
  | mcycle
  | mcountinhibit
  | mcounteren
  | scounteren
  | mscratch
  | mtval
  | mepc
  | mcause
  | mtvec
  | mideleg
  | medeleg
  | mip
  | mie
  | senvcfg
  | menvcfg
  | mseccfg
  | mstatus
  | misa
  | cur_inst
  | cur_privilege
  | x31
  | x30
  | x29
  | x28
  | x27
  | x26
  | x25
  | x24
  | x23
  | x22
  | x21
  | x20
  | x19
  | x18
  | x17
  | x16
  | x15
  | x14
  | x13
  | x12
  | x11
  | x10
  | x9
  | x8
  | x7
  | x6
  | x5
  | x4
  | x3
  | x2
  | x1
  | nextPC
  | PC
  | rvfi_mem_data_present
  | rvfi_mem_data
  | rvfi_int_data_present
  | rvfi_int_data
  | rvfi_pc_data
  | rvfi_inst_data
  | rvfi_instruction
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .satp => (BitVec 32)
  | .tlb => (Vector (Option TLB_Entry) 64)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .stimecmp => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .plat_clint_size => (BitVec (bif 32 = 32 then 34 else 64))
  | .plat_clint_base => (BitVec (bif 32 = 32 then 34 else 64))
  | .plat_rom_size => (BitVec (bif 32 = 32 then 34 else 64))
  | .plat_rom_base => (BitVec (bif 32 = 32 then 34 else 64))
  | .plat_ram_size => (BitVec (bif 32 = 32 then 34 else 64))
  | .plat_ram_base => (BitVec (bif 32 = 32 then 34 else 64))
  | .minstretcfg => (BitVec 64)
  | .mcyclecfg => (BitVec 64)
  | .mhpmcounter => (Vector (BitVec 64) 32)
  | .mhpmevent => (Vector (BitVec 64) 32)
  | .fcsr => (BitVec 32)
  | .f31 => (BitVec (bif false then 8 else 4 * 8))
  | .f30 => (BitVec (bif false then 8 else 4 * 8))
  | .f29 => (BitVec (bif false then 8 else 4 * 8))
  | .f28 => (BitVec (bif false then 8 else 4 * 8))
  | .f27 => (BitVec (bif false then 8 else 4 * 8))
  | .f26 => (BitVec (bif false then 8 else 4 * 8))
  | .f25 => (BitVec (bif false then 8 else 4 * 8))
  | .f24 => (BitVec (bif false then 8 else 4 * 8))
  | .f23 => (BitVec (bif false then 8 else 4 * 8))
  | .f22 => (BitVec (bif false then 8 else 4 * 8))
  | .f21 => (BitVec (bif false then 8 else 4 * 8))
  | .f20 => (BitVec (bif false then 8 else 4 * 8))
  | .f19 => (BitVec (bif false then 8 else 4 * 8))
  | .f18 => (BitVec (bif false then 8 else 4 * 8))
  | .f17 => (BitVec (bif false then 8 else 4 * 8))
  | .f16 => (BitVec (bif false then 8 else 4 * 8))
  | .f15 => (BitVec (bif false then 8 else 4 * 8))
  | .f14 => (BitVec (bif false then 8 else 4 * 8))
  | .f13 => (BitVec (bif false then 8 else 4 * 8))
  | .f12 => (BitVec (bif false then 8 else 4 * 8))
  | .f11 => (BitVec (bif false then 8 else 4 * 8))
  | .f10 => (BitVec (bif false then 8 else 4 * 8))
  | .f9 => (BitVec (bif false then 8 else 4 * 8))
  | .f8 => (BitVec (bif false then 8 else 4 * 8))
  | .f7 => (BitVec (bif false then 8 else 4 * 8))
  | .f6 => (BitVec (bif false then 8 else 4 * 8))
  | .f5 => (BitVec (bif false then 8 else 4 * 8))
  | .f4 => (BitVec (bif false then 8 else 4 * 8))
  | .f3 => (BitVec (bif false then 8 else 4 * 8))
  | .f2 => (BitVec (bif false then 8 else 4 * 8))
  | .f1 => (BitVec (bif false then 8 else 4 * 8))
  | .f0 => (BitVec (bif false then 8 else 4 * 8))
  | .float_fflags => (BitVec 64)
  | .float_result => (BitVec 64)
  | .vcsr => (BitVec 3)
  | .vr31 => (BitVec 65536)
  | .vr30 => (BitVec 65536)
  | .vr29 => (BitVec 65536)
  | .vr28 => (BitVec 65536)
  | .vr27 => (BitVec 65536)
  | .vr26 => (BitVec 65536)
  | .vr25 => (BitVec 65536)
  | .vr24 => (BitVec 65536)
  | .vr23 => (BitVec 65536)
  | .vr22 => (BitVec 65536)
  | .vr21 => (BitVec 65536)
  | .vr20 => (BitVec 65536)
  | .vr19 => (BitVec 65536)
  | .vr18 => (BitVec 65536)
  | .vr17 => (BitVec 65536)
  | .vr16 => (BitVec 65536)
  | .vr15 => (BitVec 65536)
  | .vr14 => (BitVec 65536)
  | .vr13 => (BitVec 65536)
  | .vr12 => (BitVec 65536)
  | .vr11 => (BitVec 65536)
  | .vr10 => (BitVec 65536)
  | .vr9 => (BitVec 65536)
  | .vr8 => (BitVec 65536)
  | .vr7 => (BitVec 65536)
  | .vr6 => (BitVec 65536)
  | .vr5 => (BitVec 65536)
  | .vr4 => (BitVec 65536)
  | .vr3 => (BitVec 65536)
  | .vr2 => (BitVec 65536)
  | .vr1 => (BitVec 65536)
  | .vr0 => (BitVec 65536)
  | .pmpaddr_n => (Vector (BitVec 32) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .vtype => (BitVec 32)
  | .vl => (BitVec 32)
  | .vstart => (BitVec 32)
  | .tselect => (BitVec 32)
  | .stval => (BitVec 32)
  | .scause => (BitVec 32)
  | .sepc => (BitVec 32)
  | .sscratch => (BitVec 32)
  | .stvec => (BitVec 32)
  | .mconfigptr => (BitVec 32)
  | .mhartid => (BitVec 32)
  | .marchid => (BitVec 32)
  | .mimpid => (BitVec 32)
  | .mvendorid => (BitVec 32)
  | .minstret_increment => Bool
  | .minstret => (BitVec 64)
  | .mtime => (BitVec 64)
  | .mcycle => (BitVec 64)
  | .mcountinhibit => (BitVec 32)
  | .mcounteren => (BitVec 32)
  | .scounteren => (BitVec 32)
  | .mscratch => (BitVec 32)
  | .mtval => (BitVec 32)
  | .mepc => (BitVec 32)
  | .mcause => (BitVec 32)
  | .mtvec => (BitVec 32)
  | .mideleg => (BitVec 32)
  | .medeleg => (BitVec 64)
  | .mip => (BitVec 32)
  | .mie => (BitVec 32)
  | .senvcfg => (BitVec 32)
  | .menvcfg => (BitVec 64)
  | .mseccfg => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec 32)
  | .cur_inst => (BitVec 32)
  | .cur_privilege => Privilege
  | .x31 => (BitVec 32)
  | .x30 => (BitVec 32)
  | .x29 => (BitVec 32)
  | .x28 => (BitVec 32)
  | .x27 => (BitVec 32)
  | .x26 => (BitVec 32)
  | .x25 => (BitVec 32)
  | .x24 => (BitVec 32)
  | .x23 => (BitVec 32)
  | .x22 => (BitVec 32)
  | .x21 => (BitVec 32)
  | .x20 => (BitVec 32)
  | .x19 => (BitVec 32)
  | .x18 => (BitVec 32)
  | .x17 => (BitVec 32)
  | .x16 => (BitVec 32)
  | .x15 => (BitVec 32)
  | .x14 => (BitVec 32)
  | .x13 => (BitVec 32)
  | .x12 => (BitVec 32)
  | .x11 => (BitVec 32)
  | .x10 => (BitVec 32)
  | .x9 => (BitVec 32)
  | .x8 => (BitVec 32)
  | .x7 => (BitVec 32)
  | .x6 => (BitVec 32)
  | .x5 => (BitVec 32)
  | .x4 => (BitVec 32)
  | .x3 => (BitVec 32)
  | .x2 => (BitVec 32)
  | .x1 => (BitVec 32)
  | .nextPC => (BitVec 32)
  | .PC => (BitVec 32)
  | .rvfi_mem_data_present => Bool
  | .rvfi_mem_data => (BitVec 704)
  | .rvfi_int_data_present => Bool
  | .rvfi_int_data => (BitVec 320)
  | .rvfi_pc_data => (BitVec 128)
  | .rvfi_inst_data => (BitVec 192)
  | .rvfi_instruction => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg htif_cmd_write
instance : Inhabited (RegisterRef RegisterType (BitVec 128)) where
  default := .Reg rvfi_pc_data
instance : Inhabited (RegisterRef RegisterType (BitVec 192)) where
  default := .Reg rvfi_inst_data
instance : Inhabited (RegisterRef RegisterType (BitVec 3)) where
  default := .Reg vcsr
instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg PC
instance : Inhabited (RegisterRef RegisterType (BitVec 320)) where
  default := .Reg rvfi_int_data
instance : Inhabited (RegisterRef RegisterType (BitVec (bif 32 = 32 then 34 else 64))) where
  default := .Reg plat_ram_base
instance : Inhabited (RegisterRef RegisterType (BitVec 4)) where
  default := .Reg htif_payload_writes
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg rvfi_instruction
instance : Inhabited (RegisterRef RegisterType (BitVec 65536)) where
  default := .Reg vr0
instance : Inhabited (RegisterRef RegisterType (BitVec 704)) where
  default := .Reg rvfi_mem_data
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg rvfi_int_data_present
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg mhpmevent
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 32) 64)) where
  default := .Reg pmpaddr_n
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 8) 64)) where
  default := .Reg pmpcfg_n
instance : Inhabited (RegisterRef RegisterType (Vector (Option TLB_Entry) 64)) where
  default := .Reg tlb
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception

instance : Arch where
  va_size := 64
  pa := (BitVec (bif 32 = 32 then 34 else 64))
  abort := Unit
  translation := Unit
  trans_start := Unit
  trans_end := Unit
  fault := Unit
  tlb_op := Unit
  cache_op := Unit
  barrier := barrier_kind
  arch_ak := RISCV_strong_access
  sys_reg_id := Unit

