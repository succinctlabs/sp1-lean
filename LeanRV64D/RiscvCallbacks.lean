import LeanRV64D.HexBits
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvTypes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
open instruction
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbom
open cbie
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open TrapVectorMode
open Step
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_write_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_read_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_1 : Nat, 0 ≤ x_1 ∧ x_1 < xlen -/
def mem_exception_callback (x_0 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_1 : Nat) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 64)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_write_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_read_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def trap_callback (x_0 : Unit) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "misa" => (some (0x301 : (BitVec 12)))
  | "mstatus" => (some (0x300 : (BitVec 12)))
  | "mstatush" => (some (0x310 : (BitVec 12)))
  | "mseccfg" => (some (0x747 : (BitVec 12)))
  | "mseccfgh" => (some (0x757 : (BitVec 12)))
  | "menvcfg" => (some (0x30A : (BitVec 12)))
  | "menvcfgh" => (some (0x31A : (BitVec 12)))
  | "senvcfg" => (some (0x10A : (BitVec 12)))
  | "mie" => (some (0x304 : (BitVec 12)))
  | "mip" => (some (0x344 : (BitVec 12)))
  | "medeleg" => (some (0x302 : (BitVec 12)))
  | "medelegh" => (some (0x312 : (BitVec 12)))
  | "mideleg" => (some (0x303 : (BitVec 12)))
  | "mcause" => (some (0x342 : (BitVec 12)))
  | "mtval" => (some (0x343 : (BitVec 12)))
  | "mscratch" => (some (0x340 : (BitVec 12)))
  | "scounteren" => (some (0x106 : (BitVec 12)))
  | "mcounteren" => (some (0x306 : (BitVec 12)))
  | "mcountinhibit" => (some (0x320 : (BitVec 12)))
  | "mvendorid" => (some (0xF11 : (BitVec 12)))
  | "marchid" => (some (0xF12 : (BitVec 12)))
  | "mimpid" => (some (0xF13 : (BitVec 12)))
  | "mhartid" => (some (0xF14 : (BitVec 12)))
  | "mconfigptr" => (some (0xF15 : (BitVec 12)))
  | "sstatus" => (some (0x100 : (BitVec 12)))
  | "sip" => (some (0x144 : (BitVec 12)))
  | "sie" => (some (0x104 : (BitVec 12)))
  | "sscratch" => (some (0x140 : (BitVec 12)))
  | "scause" => (some (0x142 : (BitVec 12)))
  | "stval" => (some (0x143 : (BitVec 12)))
  | "tselect" => (some (0x7A0 : (BitVec 12)))
  | "tdata1" => (some (0x7A1 : (BitVec 12)))
  | "tdata2" => (some (0x7A2 : (BitVec 12)))
  | "tdata3" => (some (0x7A3 : (BitVec 12)))
  | "stvec" => (some (0x105 : (BitVec 12)))
  | "sepc" => (some (0x141 : (BitVec 12)))
  | "mtvec" => (some (0x305 : (BitVec 12)))
  | "mepc" => (some (0x341 : (BitVec 12)))
  | "pmpcfg0" => (some (0x3A0 : (BitVec 12)))
  | "pmpcfg1" => (some (0x3A1 : (BitVec 12)))
  | "pmpcfg2" => (some (0x3A2 : (BitVec 12)))
  | "pmpcfg3" => (some (0x3A3 : (BitVec 12)))
  | "pmpcfg4" => (some (0x3A4 : (BitVec 12)))
  | "pmpcfg5" => (some (0x3A5 : (BitVec 12)))
  | "pmpcfg6" => (some (0x3A6 : (BitVec 12)))
  | "pmpcfg7" => (some (0x3A7 : (BitVec 12)))
  | "pmpcfg8" => (some (0x3A8 : (BitVec 12)))
  | "pmpcfg9" => (some (0x3A9 : (BitVec 12)))
  | "pmpcfg10" => (some (0x3AA : (BitVec 12)))
  | "pmpcfg11" => (some (0x3AB : (BitVec 12)))
  | "pmpcfg12" => (some (0x3AC : (BitVec 12)))
  | "pmpcfg13" => (some (0x3AD : (BitVec 12)))
  | "pmpcfg14" => (some (0x3AE : (BitVec 12)))
  | "pmpcfg15" => (some (0x3AF : (BitVec 12)))
  | "pmpaddr0" => (some (0x3B0 : (BitVec 12)))
  | "pmpaddr1" => (some (0x3B1 : (BitVec 12)))
  | "pmpaddr2" => (some (0x3B2 : (BitVec 12)))
  | "pmpaddr3" => (some (0x3B3 : (BitVec 12)))
  | "pmpaddr4" => (some (0x3B4 : (BitVec 12)))
  | "pmpaddr5" => (some (0x3B5 : (BitVec 12)))
  | "pmpaddr6" => (some (0x3B6 : (BitVec 12)))
  | "pmpaddr7" => (some (0x3B7 : (BitVec 12)))
  | "pmpaddr8" => (some (0x3B8 : (BitVec 12)))
  | "pmpaddr9" => (some (0x3B9 : (BitVec 12)))
  | "pmpaddr10" => (some (0x3BA : (BitVec 12)))
  | "pmpaddr11" => (some (0x3BB : (BitVec 12)))
  | "pmpaddr12" => (some (0x3BC : (BitVec 12)))
  | "pmpaddr13" => (some (0x3BD : (BitVec 12)))
  | "pmpaddr14" => (some (0x3BE : (BitVec 12)))
  | "pmpaddr15" => (some (0x3BF : (BitVec 12)))
  | "pmpaddr16" => (some (0x3C0 : (BitVec 12)))
  | "pmpaddr17" => (some (0x3C1 : (BitVec 12)))
  | "pmpaddr18" => (some (0x3C2 : (BitVec 12)))
  | "pmpaddr19" => (some (0x3C3 : (BitVec 12)))
  | "pmpaddr20" => (some (0x3C4 : (BitVec 12)))
  | "pmpaddr21" => (some (0x3C5 : (BitVec 12)))
  | "pmpaddr22" => (some (0x3C6 : (BitVec 12)))
  | "pmpaddr23" => (some (0x3C7 : (BitVec 12)))
  | "pmpaddr24" => (some (0x3C8 : (BitVec 12)))
  | "pmpaddr25" => (some (0x3C9 : (BitVec 12)))
  | "pmpaddr26" => (some (0x3CA : (BitVec 12)))
  | "pmpaddr27" => (some (0x3CB : (BitVec 12)))
  | "pmpaddr28" => (some (0x3CC : (BitVec 12)))
  | "pmpaddr29" => (some (0x3CD : (BitVec 12)))
  | "pmpaddr30" => (some (0x3CE : (BitVec 12)))
  | "pmpaddr31" => (some (0x3CF : (BitVec 12)))
  | "pmpaddr32" => (some (0x3D0 : (BitVec 12)))
  | "pmpaddr33" => (some (0x3D1 : (BitVec 12)))
  | "pmpaddr34" => (some (0x3D2 : (BitVec 12)))
  | "pmpaddr35" => (some (0x3D3 : (BitVec 12)))
  | "pmpaddr36" => (some (0x3D4 : (BitVec 12)))
  | "pmpaddr37" => (some (0x3D5 : (BitVec 12)))
  | "pmpaddr38" => (some (0x3D6 : (BitVec 12)))
  | "pmpaddr39" => (some (0x3D7 : (BitVec 12)))
  | "pmpaddr40" => (some (0x3D8 : (BitVec 12)))
  | "pmpaddr41" => (some (0x3D9 : (BitVec 12)))
  | "pmpaddr42" => (some (0x3DA : (BitVec 12)))
  | "pmpaddr43" => (some (0x3DB : (BitVec 12)))
  | "pmpaddr44" => (some (0x3DC : (BitVec 12)))
  | "pmpaddr45" => (some (0x3DD : (BitVec 12)))
  | "pmpaddr46" => (some (0x3DE : (BitVec 12)))
  | "pmpaddr47" => (some (0x3DF : (BitVec 12)))
  | "pmpaddr48" => (some (0x3E0 : (BitVec 12)))
  | "pmpaddr49" => (some (0x3E1 : (BitVec 12)))
  | "pmpaddr50" => (some (0x3E2 : (BitVec 12)))
  | "pmpaddr51" => (some (0x3E3 : (BitVec 12)))
  | "pmpaddr52" => (some (0x3E4 : (BitVec 12)))
  | "pmpaddr53" => (some (0x3E5 : (BitVec 12)))
  | "pmpaddr54" => (some (0x3E6 : (BitVec 12)))
  | "pmpaddr55" => (some (0x3E7 : (BitVec 12)))
  | "pmpaddr56" => (some (0x3E8 : (BitVec 12)))
  | "pmpaddr57" => (some (0x3E9 : (BitVec 12)))
  | "pmpaddr58" => (some (0x3EA : (BitVec 12)))
  | "pmpaddr59" => (some (0x3EB : (BitVec 12)))
  | "pmpaddr60" => (some (0x3EC : (BitVec 12)))
  | "pmpaddr61" => (some (0x3ED : (BitVec 12)))
  | "pmpaddr62" => (some (0x3EE : (BitVec 12)))
  | "pmpaddr63" => (some (0x3EF : (BitVec 12)))
  | "fflags" => (some (0x001 : (BitVec 12)))
  | "frm" => (some (0x002 : (BitVec 12)))
  | "fcsr" => (some (0x003 : (BitVec 12)))
  | "vstart" => (some (0x008 : (BitVec 12)))
  | "vxsat" => (some (0x009 : (BitVec 12)))
  | "vxrm" => (some (0x00A : (BitVec 12)))
  | "vcsr" => (some (0x00F : (BitVec 12)))
  | "vl" => (some (0xC20 : (BitVec 12)))
  | "vtype" => (some (0xC21 : (BitVec 12)))
  | "vlenb" => (some (0xC22 : (BitVec 12)))
  | "mcyclecfg" => (some (0x321 : (BitVec 12)))
  | "mcyclecfgh" => (some (0x721 : (BitVec 12)))
  | "minstretcfg" => (some (0x322 : (BitVec 12)))
  | "minstretcfgh" => (some (0x722 : (BitVec 12)))
  | "satp" => (some (0x180 : (BitVec 12)))
  | "seed" => (some (0x015 : (BitVec 12)))
  | "hpmcounter3" => (some (0xC03 : (BitVec 12)))
  | "hpmcounter4" => (some (0xC04 : (BitVec 12)))
  | "hpmcounter5" => (some (0xC05 : (BitVec 12)))
  | "hpmcounter6" => (some (0xC06 : (BitVec 12)))
  | "hpmcounter7" => (some (0xC07 : (BitVec 12)))
  | "hpmcounter8" => (some (0xC08 : (BitVec 12)))
  | "hpmcounter9" => (some (0xC09 : (BitVec 12)))
  | "hpmcounter10" => (some (0xC0A : (BitVec 12)))
  | "hpmcounter11" => (some (0xC0B : (BitVec 12)))
  | "hpmcounter12" => (some (0xC0C : (BitVec 12)))
  | "hpmcounter13" => (some (0xC0D : (BitVec 12)))
  | "hpmcounter14" => (some (0xC0E : (BitVec 12)))
  | "hpmcounter15" => (some (0xC0F : (BitVec 12)))
  | "hpmcounter16" => (some (0xC10 : (BitVec 12)))
  | "hpmcounter17" => (some (0xC11 : (BitVec 12)))
  | "hpmcounter18" => (some (0xC12 : (BitVec 12)))
  | "hpmcounter19" => (some (0xC13 : (BitVec 12)))
  | "hpmcounter20" => (some (0xC14 : (BitVec 12)))
  | "hpmcounter21" => (some (0xC15 : (BitVec 12)))
  | "hpmcounter22" => (some (0xC16 : (BitVec 12)))
  | "hpmcounter23" => (some (0xC17 : (BitVec 12)))
  | "hpmcounter24" => (some (0xC18 : (BitVec 12)))
  | "hpmcounter25" => (some (0xC19 : (BitVec 12)))
  | "hpmcounter26" => (some (0xC1A : (BitVec 12)))
  | "hpmcounter27" => (some (0xC1B : (BitVec 12)))
  | "hpmcounter28" => (some (0xC1C : (BitVec 12)))
  | "hpmcounter29" => (some (0xC1D : (BitVec 12)))
  | "hpmcounter30" => (some (0xC1E : (BitVec 12)))
  | "hpmcounter31" => (some (0xC1F : (BitVec 12)))
  | "hpmcounter3h" => (some (0xC83 : (BitVec 12)))
  | "hpmcounter4h" => (some (0xC84 : (BitVec 12)))
  | "hpmcounter5h" => (some (0xC85 : (BitVec 12)))
  | "hpmcounter6h" => (some (0xC86 : (BitVec 12)))
  | "hpmcounter7h" => (some (0xC87 : (BitVec 12)))
  | "hpmcounter8h" => (some (0xC88 : (BitVec 12)))
  | "hpmcounter9h" => (some (0xC89 : (BitVec 12)))
  | "hpmcounter10h" => (some (0xC8A : (BitVec 12)))
  | "hpmcounter11h" => (some (0xC8B : (BitVec 12)))
  | "hpmcounter12h" => (some (0xC8C : (BitVec 12)))
  | "hpmcounter13h" => (some (0xC8D : (BitVec 12)))
  | "hpmcounter14h" => (some (0xC8E : (BitVec 12)))
  | "hpmcounter15h" => (some (0xC8F : (BitVec 12)))
  | "hpmcounter16h" => (some (0xC90 : (BitVec 12)))
  | "hpmcounter17h" => (some (0xC91 : (BitVec 12)))
  | "hpmcounter18h" => (some (0xC92 : (BitVec 12)))
  | "hpmcounter19h" => (some (0xC93 : (BitVec 12)))
  | "hpmcounter20h" => (some (0xC94 : (BitVec 12)))
  | "hpmcounter21h" => (some (0xC95 : (BitVec 12)))
  | "hpmcounter22h" => (some (0xC96 : (BitVec 12)))
  | "hpmcounter23h" => (some (0xC97 : (BitVec 12)))
  | "hpmcounter24h" => (some (0xC98 : (BitVec 12)))
  | "hpmcounter25h" => (some (0xC99 : (BitVec 12)))
  | "hpmcounter26h" => (some (0xC9A : (BitVec 12)))
  | "hpmcounter27h" => (some (0xC9B : (BitVec 12)))
  | "hpmcounter28h" => (some (0xC9C : (BitVec 12)))
  | "hpmcounter29h" => (some (0xC9D : (BitVec 12)))
  | "hpmcounter30h" => (some (0xC9E : (BitVec 12)))
  | "hpmcounter31h" => (some (0xC9F : (BitVec 12)))
  | "mhpmevent3" => (some (0x323 : (BitVec 12)))
  | "mhpmevent4" => (some (0x324 : (BitVec 12)))
  | "mhpmevent5" => (some (0x325 : (BitVec 12)))
  | "mhpmevent6" => (some (0x326 : (BitVec 12)))
  | "mhpmevent7" => (some (0x327 : (BitVec 12)))
  | "mhpmevent8" => (some (0x328 : (BitVec 12)))
  | "mhpmevent9" => (some (0x329 : (BitVec 12)))
  | "mhpmevent10" => (some (0x32A : (BitVec 12)))
  | "mhpmevent11" => (some (0x32B : (BitVec 12)))
  | "mhpmevent12" => (some (0x32C : (BitVec 12)))
  | "mhpmevent13" => (some (0x32D : (BitVec 12)))
  | "mhpmevent14" => (some (0x32E : (BitVec 12)))
  | "mhpmevent15" => (some (0x32F : (BitVec 12)))
  | "mhpmevent16" => (some (0x330 : (BitVec 12)))
  | "mhpmevent17" => (some (0x331 : (BitVec 12)))
  | "mhpmevent18" => (some (0x332 : (BitVec 12)))
  | "mhpmevent19" => (some (0x333 : (BitVec 12)))
  | "mhpmevent20" => (some (0x334 : (BitVec 12)))
  | "mhpmevent21" => (some (0x335 : (BitVec 12)))
  | "mhpmevent22" => (some (0x336 : (BitVec 12)))
  | "mhpmevent23" => (some (0x337 : (BitVec 12)))
  | "mhpmevent24" => (some (0x338 : (BitVec 12)))
  | "mhpmevent25" => (some (0x339 : (BitVec 12)))
  | "mhpmevent26" => (some (0x33A : (BitVec 12)))
  | "mhpmevent27" => (some (0x33B : (BitVec 12)))
  | "mhpmevent28" => (some (0x33C : (BitVec 12)))
  | "mhpmevent29" => (some (0x33D : (BitVec 12)))
  | "mhpmevent30" => (some (0x33E : (BitVec 12)))
  | "mhpmevent31" => (some (0x33F : (BitVec 12)))
  | "mhpmcounter3" => (some (0xB03 : (BitVec 12)))
  | "mhpmcounter4" => (some (0xB04 : (BitVec 12)))
  | "mhpmcounter5" => (some (0xB05 : (BitVec 12)))
  | "mhpmcounter6" => (some (0xB06 : (BitVec 12)))
  | "mhpmcounter7" => (some (0xB07 : (BitVec 12)))
  | "mhpmcounter8" => (some (0xB08 : (BitVec 12)))
  | "mhpmcounter9" => (some (0xB09 : (BitVec 12)))
  | "mhpmcounter10" => (some (0xB0A : (BitVec 12)))
  | "mhpmcounter11" => (some (0xB0B : (BitVec 12)))
  | "mhpmcounter12" => (some (0xB0C : (BitVec 12)))
  | "mhpmcounter13" => (some (0xB0D : (BitVec 12)))
  | "mhpmcounter14" => (some (0xB0E : (BitVec 12)))
  | "mhpmcounter15" => (some (0xB0F : (BitVec 12)))
  | "mhpmcounter16" => (some (0xB10 : (BitVec 12)))
  | "mhpmcounter17" => (some (0xB11 : (BitVec 12)))
  | "mhpmcounter18" => (some (0xB12 : (BitVec 12)))
  | "mhpmcounter19" => (some (0xB13 : (BitVec 12)))
  | "mhpmcounter20" => (some (0xB14 : (BitVec 12)))
  | "mhpmcounter21" => (some (0xB15 : (BitVec 12)))
  | "mhpmcounter22" => (some (0xB16 : (BitVec 12)))
  | "mhpmcounter23" => (some (0xB17 : (BitVec 12)))
  | "mhpmcounter24" => (some (0xB18 : (BitVec 12)))
  | "mhpmcounter25" => (some (0xB19 : (BitVec 12)))
  | "mhpmcounter26" => (some (0xB1A : (BitVec 12)))
  | "mhpmcounter27" => (some (0xB1B : (BitVec 12)))
  | "mhpmcounter28" => (some (0xB1C : (BitVec 12)))
  | "mhpmcounter29" => (some (0xB1D : (BitVec 12)))
  | "mhpmcounter30" => (some (0xB1E : (BitVec 12)))
  | "mhpmcounter31" => (some (0xB1F : (BitVec 12)))
  | "mhpmcounter3h" => (some (0xB83 : (BitVec 12)))
  | "mhpmcounter4h" => (some (0xB84 : (BitVec 12)))
  | "mhpmcounter5h" => (some (0xB85 : (BitVec 12)))
  | "mhpmcounter6h" => (some (0xB86 : (BitVec 12)))
  | "mhpmcounter7h" => (some (0xB87 : (BitVec 12)))
  | "mhpmcounter8h" => (some (0xB88 : (BitVec 12)))
  | "mhpmcounter9h" => (some (0xB89 : (BitVec 12)))
  | "mhpmcounter10h" => (some (0xB8A : (BitVec 12)))
  | "mhpmcounter11h" => (some (0xB8B : (BitVec 12)))
  | "mhpmcounter12h" => (some (0xB8C : (BitVec 12)))
  | "mhpmcounter13h" => (some (0xB8D : (BitVec 12)))
  | "mhpmcounter14h" => (some (0xB8E : (BitVec 12)))
  | "mhpmcounter15h" => (some (0xB8F : (BitVec 12)))
  | "mhpmcounter16h" => (some (0xB90 : (BitVec 12)))
  | "mhpmcounter17h" => (some (0xB91 : (BitVec 12)))
  | "mhpmcounter18h" => (some (0xB92 : (BitVec 12)))
  | "mhpmcounter19h" => (some (0xB93 : (BitVec 12)))
  | "mhpmcounter20h" => (some (0xB94 : (BitVec 12)))
  | "mhpmcounter21h" => (some (0xB95 : (BitVec 12)))
  | "mhpmcounter22h" => (some (0xB96 : (BitVec 12)))
  | "mhpmcounter23h" => (some (0xB97 : (BitVec 12)))
  | "mhpmcounter24h" => (some (0xB98 : (BitVec 12)))
  | "mhpmcounter25h" => (some (0xB99 : (BitVec 12)))
  | "mhpmcounter26h" => (some (0xB9A : (BitVec 12)))
  | "mhpmcounter27h" => (some (0xB9B : (BitVec 12)))
  | "mhpmcounter28h" => (some (0xB9C : (BitVec 12)))
  | "mhpmcounter29h" => (some (0xB9D : (BitVec 12)))
  | "mhpmcounter30h" => (some (0xB9E : (BitVec 12)))
  | "mhpmcounter31h" => (some (0xB9F : (BitVec 12)))
  | "mhpmevent3h" => (some (0x723 : (BitVec 12)))
  | "mhpmevent4h" => (some (0x724 : (BitVec 12)))
  | "mhpmevent5h" => (some (0x725 : (BitVec 12)))
  | "mhpmevent6h" => (some (0x726 : (BitVec 12)))
  | "mhpmevent7h" => (some (0x727 : (BitVec 12)))
  | "mhpmevent8h" => (some (0x728 : (BitVec 12)))
  | "mhpmevent9h" => (some (0x729 : (BitVec 12)))
  | "mhpmevent10h" => (some (0x72A : (BitVec 12)))
  | "mhpmevent11h" => (some (0x72B : (BitVec 12)))
  | "mhpmevent12h" => (some (0x72C : (BitVec 12)))
  | "mhpmevent13h" => (some (0x72D : (BitVec 12)))
  | "mhpmevent14h" => (some (0x72E : (BitVec 12)))
  | "mhpmevent15h" => (some (0x72F : (BitVec 12)))
  | "mhpmevent16h" => (some (0x730 : (BitVec 12)))
  | "mhpmevent17h" => (some (0x731 : (BitVec 12)))
  | "mhpmevent18h" => (some (0x732 : (BitVec 12)))
  | "mhpmevent19h" => (some (0x733 : (BitVec 12)))
  | "mhpmevent20h" => (some (0x734 : (BitVec 12)))
  | "mhpmevent21h" => (some (0x735 : (BitVec 12)))
  | "mhpmevent22h" => (some (0x736 : (BitVec 12)))
  | "mhpmevent23h" => (some (0x737 : (BitVec 12)))
  | "mhpmevent24h" => (some (0x738 : (BitVec 12)))
  | "mhpmevent25h" => (some (0x739 : (BitVec 12)))
  | "mhpmevent26h" => (some (0x73A : (BitVec 12)))
  | "mhpmevent27h" => (some (0x73B : (BitVec 12)))
  | "mhpmevent28h" => (some (0x73C : (BitVec 12)))
  | "mhpmevent29h" => (some (0x73D : (BitVec 12)))
  | "mhpmevent30h" => (some (0x73E : (BitVec 12)))
  | "mhpmevent31h" => (some (0x73F : (BitVec 12)))
  | "scountovf" => (some (0xDA0 : (BitVec 12)))
  | "stimecmp" => (some (0x14D : (BitVec 12)))
  | "stimecmph" => (some (0x15D : (BitVec 12)))
  | "cycle" => (some (0xC00 : (BitVec 12)))
  | "time" => (some (0xC01 : (BitVec 12)))
  | "instret" => (some (0xC02 : (BitVec 12)))
  | "cycleh" => (some (0xC80 : (BitVec 12)))
  | "timeh" => (some (0xC81 : (BitVec 12)))
  | "instreth" => (some (0xC82 : (BitVec 12)))
  | "mcycle" => (some (0xB00 : (BitVec 12)))
  | "minstret" => (some (0xB02 : (BitVec 12)))
  | "mcycleh" => (some (0xB80 : (BitVec 12)))
  | "minstreth" => (some (0xB82 : (BitVec 12)))
  | mapping0_ =>
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some reg))
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def csr_id_write_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_write_callback name csr value))

def csr_name_read_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_read_callback name csr value))

def csr_id_read_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_read_callback name csr value))

def long_csr_write_callback (name : String) (name_high : String) (value : (BitVec 64)) : SailM Unit := do
  (csr_name_write_callback name (Sail.BitVec.extractLsb value (xlen -i 1) 0))

